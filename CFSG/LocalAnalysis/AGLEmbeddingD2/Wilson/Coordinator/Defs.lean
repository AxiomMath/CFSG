module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Gens
public import CFSG.Sporadic.Schreier.J4SElevenBase

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Quasithin.J4M2 CFSG.Quasithin.J4Loc

@[expose] def jInv : J := nrm₂ ^ 20

@[expose] def abGen (m : ℕ) : J := if m = 0 then a else if m = 1 then b else 1

@[expose] def hWord : List ℤ :=
  [1, 2, -2, -2, -1, 2, -2, -1, -2, -1, -2, 2, 2, 1, 2, 2, 2, 2, 1, -2]

@[expose] def hW : J := wordProd abGen hWord

@[expose] def gam : J := (z0 * (hW * jInv * hW⁻¹)) ^ 6 * hW

@[expose] def c1j : J := qy ^ 10 * nrm₁

@[expose] def cA : J := gam * c1j * gam⁻¹

@[expose] def cB : J := gam * nrm₂ * gam⁻¹

@[expose] def cZ : J := gam * qz * gam⁻¹

@[expose] def C0p : Subgroup J := Subgroup.closure {cA, cB, cZ}

@[expose] def mElt : J := gE 15 * gE 29 * gE 1 * gE 7 * gE 9 * gE 11

@[expose] def rRep : Fin 7 → J :=
  ![gE 0, gE 1, gE 0 * gE 2, gE 1 * gE 2, gE 0 * gE 1 * gE 2, gE 1 * gE 3, gE 2 * gE 3]

@[expose] def qNF (e : Bool) (c : ℕ) : J := (if e then z0 else 1) * QT.eta gE 12 c

@[expose] def q8Masks : List ℕ := [0, 503, 3741, 3946]

@[expose] def k3Forms : List (Bool × ℕ × ℕ) :=
  [false, true].flatMap fun e =>
    [(0, 0), (503, 0), (739, 2), (788, 2), (1160, 1), (1407, 1), (2581, 1), (3042, 1),
      (3198, 2), (3465, 2), (3741, 0), (3946, 0)].map fun ci => (e, ci.1, ci.2)

@[expose] def kElt (f : Bool × ℕ × ℕ) : J := qNF f.1 f.2.1 * cE ^ f.2.2

@[expose] def K3set : Set J := {g | ∃ f ∈ k3Forms, g = kElt f}

@[expose] def Q8set : Set J := {g | ∃ e : Bool, ∃ c ∈ q8Masks, g = qNF e c}

end CFSG.AGLEmbeddingD2.Wilson.Coordinator
