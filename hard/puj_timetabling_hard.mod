set D := {1..5}; #Dias de la semana
set INC := {(1,7),(2,7),(2,8),(3,8),(4,9),(5,9),(5,10),(6,10),(6,11),(10,11)}; #Parejas de bloques que no se pueden cruzar
set B := {1..11}; #Bloques horarios
set J{B};
set S := {1..9}; #Semestres
set L := {1..4}; #Lugares
set G := {1..2}; #Grupos
set P := {1..57};  #Profesores
set K := {1,2}; # 1:Materias que pertenecen al semestre S, 2:Materias que se pueden adelantar o atrasar en el semestre S
set M{S,K}; #Materias en el semestre S de tipo K
set MT = union {s in S} M[s,1]; #Todas las 50 materias
set MS{s in S} = union{k in K} M[s,k]; #Materias totales por semestre (K1 U K2)

var x{D,B,MT,L,G, P} binary; #Variable principal, X=1 si la materia MT es asignada el dia D, en el bloque B, en el lugar tipo L, del grupo G, con el profesor P
var N{B,MT,G} binary; #Variable de apoyo, nos permite que una misma asignatura conserve el mismo bloque al estar en dias diferentes
var y{D,S,B} >= 0; #Numero de cruces suaves (K=2)
var w{D,S,B,B} >= 0; #Numero de cruces suaves (K=2)
var Preferences >=0;
var Crosses >=0;

param IS{MT}; #Intensidad Semanal
param HB{MT, B}; #Para ver si la materia le corresponde un bloque de 2 o 3 horas, se puede usar para asignar un horario fijo
param SA{MT, L} binary; #Que tipo de salon le corresponde a la materia
param PR{MT, G, P};  #Que profesor da la materia, el modelo no decide esto, entra como dato de la facultad
param Preferencia{MT, B, D, G}; #Preferencia por asignatura, pendiente de actualización 

maximize z : sum{p in P, d in D, b in B, m in MT, g in G, l in L} 
x[d,b,m,l,g,p]*Preferencia[m,b,d,g] 
- sum{d in D,s in S, b in B} (y[d,s,b]) 
- sum{d in D,s in S, (b1,b2) in INC} (w[d,s,b1,b2]); 
#La funcion objetivo maximiza la asignación de los horarios y su preferencia, y se ve penalizada por los cruces suaves

s.t. 

R1_veces_dia{d in D, g in G, p in P, m in MT} : sum{l in L, b in B}(x[d,b,m,l, g,p]) <= 1; #Maximo una clase de la misma materia al dia

R2_dias_consecutivos{d in {1..4}, g in G, p in P, m in MT}: sum{l in L, b in B}(x[d,b,m, l, g,p] + x[(d+1),b,m, l, g,p]) <= 1; #No asignar clase de la misma materia dias consecutivos

R3_sesiones_por_semana{g in G, m in MT,b in B}: sum{p in P, d in D, l in L}(x[d,b,m,l, g,p]) = IS[m]*N[b,m,g]; #Cumplir con el numero de veces por materia en la semana

R4_Suma_N{m in MT, g in G}: sum{b in B}(N[b,m,g]) = 1; #Garantizar que las clases de la misma materia se den en el mismo bloque durante la semana

R5_clase_por_salon{l in {1,2}, b in B, d in D}:sum{p in P, g in G, m in MT,j in J[b]}(x[d,j,m,l,g,p]) <= 1; #Una clase por salon al tiempo

R6_asignacion_lugar{d in D, g in G, p in P, m in MT, l in L, b in B}: (x[d,b,m,l,g,p]) <= SA[m,l]; #Que tipo de salon le corresponde

R7_asignacion_bloque{d in D, g in G, p in P, m in MT, l in L, b in B}: (x[d,b,m,l,g,p]) <= HB[m,b]; #Asignacion del tipo de bloque por materia 2 o 3 horas

R8_DURA_incopatibilidad_horas{s in S, d in D, (b1,b2) in INC}: #Distincion entre bloques de 2 y 3 horas
 sum{p in P, g in G, l in L, m in M[s,1]}(x[d,b1,m,l,g,p] + x[d,b2,m,l,g,p]) <= 1;

R9_SUAVE_incopatibilidad_horas{s in S, d in D, (b1,b2) in INC}: #Distincion entre bloques de 2 y 3 horas
	sum{p in P, g in G, l in L, m in MS[s]}(x[d,b1,m,l,g,p] + x[d,b2,m,l,g,p]) <= 1 + w[d,s,b1,b2];

R10_cruce_semestral_DURA{d in D, s in S, b in B}: sum{p in P, g in G, l in L, m in M[s,1]}(x[d,b,m,l,g,p]) <= 1; #Las materias del mismo semestre (K=1) NUNCA se deben de cruzar

R11_profesor_por_bloque{d in D, b in B, p in P}: sum{l in L, g in G, m in MT,j in J[b]}(x[d,j,m,l,g,p]) <= 1; #El profesor no puede dar 2 clases al tiempo

R12_asignar_profesores{d in D, g in G, p in P, m in MT, l in L, b in B}: x[d,b,m,l,g,p] <= PR[m,g,p];  #Que profesor le corresponde cada materia

R13_cruce_semestral_SUAVE{d in D, s in S, b in B}:#Restriccion suave para los cruces de materias tipo (K=2)
 sum{p in P, g in G, l in L, m in MS[s]} x[d,b,m,l,g,p] <= 1 + y[d,s,b]; 

RPref: sum{p in P, d in D, b in B, m in MT, g in G, l in L} x[d,b,m,l,g,p]*Preferencia[m,b,d,g] = Preferences;
RCross: sum{d in D,s in S, b in B} (y[d,s,b])+ sum{d in D,s in S, (b1,b2) in INC} (w[d,s,b1,b2]) = Crosses;
