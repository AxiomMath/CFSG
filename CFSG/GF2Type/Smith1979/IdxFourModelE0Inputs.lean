module

public import CFSG.GF2Type.Smith1979.IdxFourModelChainInputs
public import CFSG.GF2Type.Smith1979.IdxFourModelOrbitInputs

public section

namespace CFSG.GF2Type.Smith1979.IdxFour.E0Chk

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.IdxFour.Orb

@[expose] def inC (n : ℕ) : Bool := inO1701b n && !f0b n 3

@[expose] def orbCReps : List ℕ := [15, 29, 204, 207]

@[expose] def orbCSets (_ : Unit := ()) : List (Std.HashSet ℕ) :=
  orbCReps.map fun r => Std.HashSet.ofList (orbitList pGens r)

@[expose] def orbitCOK (_ : Unit := ()) : Bool :=
  let Ss := orbCSets ()
  Ss.all (fun S => 64 ≤ S.size) &&
    (List.range 4096).all fun n => !inC n || Ss.any fun S => S.contains n

@[expose] def sGensE0 : List (Array ℕ) :=
  [#[2, 4, 1, 8, 16, 32, 128, 256, 64, 512, 1024, 2048],
   #[1448, 2683, 2685, 1441, 2671, 1417, 3990, 1193, 1321, 3542, 425, 2006],
   #[1, 8, 2, 4, 16, 32, 64, 512, 128, 256, 1024, 2048],
   #[2, 1, 4, 8, 32, 16, 128, 64, 256, 512, 2048, 1024],
   #[1, 2, 4, 8, 1040, 2048, 64, 128, 256, 512, 16, 2080]]

@[expose] def ins (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | b :: B => if b ≤ x then x :: b :: B else b :: ins x B

@[expose] def red (B : List ℕ) (x : ℕ) : ℕ := B.foldl (fun x b => min x (x ^^^ b)) x

@[expose] def spinAux (gs : List (Array ℕ)) : ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, B => B
  | _ + 1, [], B => B
  | fuel + 1, x :: q, B =>
    let y := red B x
    if y == 0 then spinAux gs fuel q B
    else spinAux gs fuel (q ++ gs.map fun g => appN g x) (ins y B)

@[expose] def spin (gs : List (Array ℕ)) (v : ℕ) : List ℕ := spinAux gs 100 [v] []

@[expose] def dCodes : List ℕ := [0, 15, 960, 975]

@[expose] def sub6Cands : List ℕ := [3, 192, 195]

@[expose] def sub6Check (_ : Unit := ()) : Bool :=
  sub6Cands.all inO378b &&
    (List.range 4096).all fun v =>
      dCodes.contains v || (let B := spin sGensE0 v; sub6Cands.any fun w => red B w == 0)

@[expose] def sub6OK (_ : Unit := ()) : Bool :=
  Chain.siftOK e0Gens Chain.e0Words Chain.e0Base sGensE0 [] &&
    sGensE0.all (fun g => appN g 15 == 15) && sub6Check ()

end CFSG.GF2Type.Smith1979.IdxFour.E0Chk
