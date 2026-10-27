module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThree

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

@[expose] def SixThreeOneAt (p : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    Subgroup.centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X →
    CFSG.Open.pRank p (CFSG.pCore p X) ≤ 3 → CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3 →
    SixThreeOneList p ↥(oPPrimeHull p (⊤ : Subgroup (X ⧸ CFSG.pCore p X)))

@[expose] def LinearListAt (p : ℕ) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W],
    Module.finrank (ZMod p) W ≤ 3 → ∀ H : Subgroup (Module.End (ZMod p) W)ˣ,
      oPPrimeHull p H = H → SixThreeOneList p (↥H ⧸ CFSG.pCore p ↥H)

@[expose] def MatrixListAt (p n : ℕ) : Prop :=
  ∀ H : Subgroup (GL (Fin n) (ZMod p)), oPPrimeHull p H = H →
    SixThreeOneList p (↥H ⧸ CFSG.pCore p ↥H)

@[expose] def SLTwoOrTrivialAt (p : ℕ) : Prop :=
  ∀ H : Subgroup (GL (Fin 2) (ZMod p)), oPPrimeHull p H = H →
    IsSLType 2 (ZMod p) (↥H ⧸ CFSG.pCore p ↥H) ∨ Nat.card (↥H ⧸ CFSG.pCore p ↥H) = 1

@[expose] def SympListAt (p : ℕ) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W],
    Module.finrank (ZMod p) W = 4 → ∀ B : LinearMap.BilinForm (ZMod p) W,
    (∀ u : W, (∀ v : W, B u v = 0) → u = 0) → (∀ w : W, B w w = 0) →
    ∀ H : Subgroup (Module.End (ZMod p) W)ˣ, oPPrimeHull p H = H →
      (∀ x ∈ H, ∃ c : ZMod p, ∀ u v : W,
        B ((x : Module.End (ZMod p) W) u) ((x : Module.End (ZMod p) W) v) = c * B u v) →
      SixThreeOneList p (↥H ⧸ CFSG.pCore p ↥H)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
