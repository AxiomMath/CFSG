module

public import Init

public section

namespace CFSG.KC.HSK

@[expose] def relsLit : List (List (Nat × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)], [(0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true)], [(0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true)], [(0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true)], [(0, false), (1, false), (1, false), (0, true), (1, true), (1, true), (0, false), (1, false), (1, false), (0, true), (1, true), (1, true), (0, false), (1, false), (1, false), (0, true), (1, true), (1, true), (0, false), (1, false), (1, false), (0, true), (1, true), (1, true), (0, false), (1, false), (1, false), (0, true), (1, true), (1, true), (0, false), (1, false), (1, false), (0, true), (1, true), (1, true)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, false), (1, false), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, false), (1, false), (0, true), (1, false), (1, false), (0, true), (1, false), (1, false)], [(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, false), (0, true), (1, false), (1, false)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true)]]

@[expose] def R0 : Nat := nat_lit 8

@[expose] def R1 : Nat := nat_lit 35322350018580

@[expose] def R2 : Nat := nat_lit 3065037850497807041164954017588240258110557323916214360

@[expose] def R3 : Nat := nat_lit 56759965339163168092168323569284255711409334260199204615336882246611107960

@[expose] def R4 : Nat := nat_lit 46769124235044283059365808173405392845656460103760

@[expose] def R5 : Nat := nat_lit 200870320593700010505133806019716433877269883680349534294112

@[expose] def R6 : Nat := nat_lit 15976510398082902476318604496666290824252763194347956807405630487100595772901534282551440

@[expose] def R7 : Nat := nat_lit 1428411297971480595489923809313603104035108761747591691418191078011971289535742084

@[expose] def R8 : Nat := nat_lit 1047036585084984949403673701565455902929494472367523121538392856044083971540483256725408841880

@[expose] def R9 : Nat := nat_lit 23964764877371582193257729054091863525413276131465851677618475395243680400106571887018128

@[expose] def R10 : Nat := nat_lit 23871758184986719035134320147357885061930969161551505639419632001411967425839887766519952

@[expose] def R11 : Nat := nat_lit 400501643369289666246661084721320947877773100989061221723333673048486741136664545521655187767452

@[expose] def R12 : Nat := nat_lit 1047036585084981265767834836093690490718344537637161777240920976612304053481879728382707499160

@[expose] noncomputable def rel (k : Nat) : Nat :=
  (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) R12 (Nat.beq k (nat_lit 12))) R11 (Nat.beq k (nat_lit 11))) R10 (Nat.beq k (nat_lit 10))) R9 (Nat.beq k (nat_lit 9))) R8 (Nat.beq k (nat_lit 8))) R7 (Nat.beq k (nat_lit 7))) R6 (Nat.beq k (nat_lit 6))) R5 (Nat.beq k (nat_lit 5))) R4 (Nat.beq k (nat_lit 4))) R3 (Nat.beq k (nat_lit 3))) R2 (Nat.beq k (nat_lit 2))) R1 (Nat.beq k (nat_lit 1))) R0 (Nat.beq k (nat_lit 0)))

@[expose] def list : List Nat := [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12]

@[expose] def B0 : Nat := nat_lit 4

@[expose] def B1 : Nat := nat_lit 151119190755127273201700

@[expose] def B2 : Nat := nat_lit 9903671433473814987102232620

@[expose] def B3 : Nat := nat_lit 716411503555297379066075332726516849329573960

@[expose] def B4 : Nat := nat_lit 1074617201955972103584066131327342944433737800

@[expose] noncomputable def subB (j : Nat) : Nat :=
  (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) B4 (Nat.beq j (nat_lit 4))) B3 (Nat.beq j (nat_lit 3))) B2 (Nat.beq j (nat_lit 2))) B1 (Nat.beq j (nat_lit 1))) B0 (Nat.beq j (nat_lit 0)))

@[expose] def G1 : Nat := nat_lit 536883212

@[expose] def G2 : Nat := nat_lit 973565603181811000398757583921204

@[expose] def G3 : Nat := nat_lit 16397357533361393013137031726093085708356

@[expose] def G4 : Nat := nat_lit 4

@[expose] def G5 : Nat := nat_lit 137442103316

@[expose] def G6 : Nat := nat_lit 2305895786309759004

@[expose] def G7 : Nat := nat_lit 590309321295298301988

@[expose] def G8 : Nat := nat_lit 249232794414543616102081941483819068

@[expose] def G9 : Nat := nat_lit 64052177864692941457566530180051116092

@[expose] def G10 : Nat := nat_lit 4181432260671929422892220814114510865440836

@[expose] def G11 : Nat := nat_lit 182691902389808004018830066902753616108605943884

@[expose] def G12 : Nat := nat_lit 274035754722989436406560368947521304837101723724

@[expose] def G13 : Nat := nat_lit 275102009102877583093805261145058150614392905804

@[expose] def G14 : Nat := nat_lit 183401339402000818980435197959355711641674068044

@[expose] def G15 : Nat := nat_lit 1070446658732013932260408528413314781552840780

@[expose] def G16 : Nat := nat_lit 183401339402001790005746656793212164447503659084

@[expose] def G17 : Nat := nat_lit 182690503148798626393110205773271497925035307084

@[expose] def G18 : Nat := nat_lit 274034355481980058780840507818039186653531086924

@[expose] def G19 : Nat := nat_lit 183401344846435614238316340663656737642229280844

@[expose] def G20 : Nat := nat_lit 18029085268560677130328071753353196792207314813722708

@[expose] def G21 : Nat := nat_lit 46769127011790849028820497127104925723803121619028

@[expose] def G22 : Nat := nat_lit 11972804103507080022201059645642464502572678109999188

@[expose] def G23 : Nat := nat_lit 17959206153866791556595740450750404518772106033373268

@[expose] def G24 : Nat := nat_lit 17959206153866770454453537889000959554116176615317588

@[expose] def G25 : Nat := nat_lit 46950742886912458241471144139062314098560936710228

@[expose] def G26 : Nat := nat_lit 70152795003386895047895170001418031783303958237268

@[expose] def G27 : Nat := nat_lit 12019390181820827638376596255014599419205127781757012

@[expose] def G28 : Nat := nat_lit 11972804104900855329787077218174765565228820244475988

@[expose] def G29 : Nat := nat_lit 46950744280687517245008983209896124836410695880788

@[expose] def G30 : Nat := nat_lit 4615445828751533345363986368858418378805072592312995932

@[expose] noncomputable def gen (k : Nat) : Nat :=
  (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) G30 (Nat.beq k (nat_lit 30))) G29 (Nat.beq k (nat_lit 29))) G28 (Nat.beq k (nat_lit 28))) G27 (Nat.beq k (nat_lit 27))) G26 (Nat.beq k (nat_lit 26))) G25 (Nat.beq k (nat_lit 25))) G24 (Nat.beq k (nat_lit 24))) G23 (Nat.beq k (nat_lit 23))) G22 (Nat.beq k (nat_lit 22))) G21 (Nat.beq k (nat_lit 21))) G20 (Nat.beq k (nat_lit 20))) G19 (Nat.beq k (nat_lit 19))) G18 (Nat.beq k (nat_lit 18))) G17 (Nat.beq k (nat_lit 17))) G16 (Nat.beq k (nat_lit 16))) G15 (Nat.beq k (nat_lit 15))) G14 (Nat.beq k (nat_lit 14))) G13 (Nat.beq k (nat_lit 13))) G12 (Nat.beq k (nat_lit 12))) G11 (Nat.beq k (nat_lit 11))) G10 (Nat.beq k (nat_lit 10))) G9 (Nat.beq k (nat_lit 9))) G8 (Nat.beq k (nat_lit 8))) G7 (Nat.beq k (nat_lit 7))) G6 (Nat.beq k (nat_lit 6))) G5 (Nat.beq k (nat_lit 5))) G4 (Nat.beq k (nat_lit 4))) G3 (Nat.beq k (nat_lit 3))) G2 (Nat.beq k (nat_lit 2))) G1 (Nat.beq k (nat_lit 1)))

@[expose] noncomputable def subS (j : Nat) : Nat :=
  (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) G30 (Nat.beq j (nat_lit 29))) G29 (Nat.beq j (nat_lit 28))) G28 (Nat.beq j (nat_lit 27))) G27 (Nat.beq j (nat_lit 26))) G26 (Nat.beq j (nat_lit 25))) G25 (Nat.beq j (nat_lit 24))) G24 (Nat.beq j (nat_lit 23))) G23 (Nat.beq j (nat_lit 22))) G22 (Nat.beq j (nat_lit 21))) G21 (Nat.beq j (nat_lit 20))) G20 (Nat.beq j (nat_lit 19))) G19 (Nat.beq j (nat_lit 18))) G18 (Nat.beq j (nat_lit 17))) G17 (Nat.beq j (nat_lit 16))) G16 (Nat.beq j (nat_lit 15))) G15 (Nat.beq j (nat_lit 14))) G14 (Nat.beq j (nat_lit 13))) G13 (Nat.beq j (nat_lit 12))) G12 (Nat.beq j (nat_lit 11))) G11 (Nat.beq j (nat_lit 10))) G3 (Nat.beq j (nat_lit 9))) G10 (Nat.beq j (nat_lit 8))) G9 (Nat.beq j (nat_lit 7))) G8 (Nat.beq j (nat_lit 6))) G2 (Nat.beq j (nat_lit 5))) G7 (Nat.beq j (nat_lit 4))) G6 (Nat.beq j (nat_lit 3))) G5 (Nat.beq j (nat_lit 2))) G1 (Nat.beq j (nat_lit 1))) G4 (Nat.beq j (nat_lit 0)))

end CFSG.KC.HSK

end
