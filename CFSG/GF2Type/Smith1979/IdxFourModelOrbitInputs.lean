module

public import CFSG.GF2Type.Smith1979.IdxFourModelDefs
public import CFSG.GF2Type.Smith1979.IdxFourModelData

public section

namespace CFSG.GF2Type.Smith1979.IdxFour.Orb

open CFSG.GF2Type.Smith1979.GammaU

@[expose] def pc6 (x : ℕ) : ℕ :=
  (x &&& 1) + ((x >>> 1) &&& 1) + ((x >>> 2) &&& 1) + ((x >>> 3) &&& 1) + ((x >>> 4) &&& 1) +
    ((x >>> 5) &&& 1)

@[expose] def wtN (n : ℕ) : ℕ := pc6 ((n ||| (n >>> 6)) &&& 63)

@[expose] def prodExpN (n : ℕ) : ℕ := (pc6 (n &&& 63) + 2 * pc6 (n >>> 6) - wtN n) % 3

@[expose] def inO378b (n : ℕ) : Bool := wtN n == 2 || (wtN n == 6 && prodExpN n == 0)

@[expose] def inO1701b (n : ℕ) : Bool := wtN n == 4 || (wtN n == 6 && prodExpN n != 0)

@[expose] def inOmegab (n : ℕ) : Bool :=
  inO378b n && !f0b n 3 && !f0b n 192 && n != 3 && n != 192 && n != 195

@[expose] def orbitList (gs : List (Array ℕ)) (v : ℕ) : List ℕ :=
  bfsClosure id (gs.map appN) 4096 [v] ((∅ : Std.HashSet ℕ).insert v) []

@[expose] def orbitSetOK (gs : List (Array ℕ)) (v : ℕ) (P : ℕ → Bool) : Bool :=
  let S := Std.HashSet.ofList (orbitList gs v)
  P v && (List.range 4096).all fun n =>
    !(P n) || (S.contains n && gs.all fun g => P (appN g n))

@[expose] def omegaOK (_ : Unit := ()) : Bool := orbitSetOK pGens 12 inOmegab

@[expose] def orbitOK (_ : Unit := ()) : Bool :=
  orbitSetOK m0Gens 3 inO378b && orbitSetOK m0Gens 15 inO1701b &&
    orbitSetOK e0Gens 3 inO378b && orbitSetOK e0Gens 15 inO1701b &&
    ((List.range 4096).filter inO378b).length == 378 &&
    ((List.range 4096).filter inO1701b).length == 1701

end CFSG.GF2Type.Smith1979.IdxFour.Orb
