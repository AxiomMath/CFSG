module

public import CFSG.ClassicalInvolution.Q3.Q3TIYDefs
public import CFSG.ClassicalInvolution.Q3.Q3TY1

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinRow IsTwinAt TwinElt TwinDatumOn)

@[expose] def TwinYKind3On (P : StatedLieTag → ℕ → Prop) : Prop :=
  OddThreeFreeInput → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z → ∀ (t : StatedLieTag) (n : ℕ),
      TwinRow t n → P t n → LocalShapeC3 2 (CompData.model t n) (conjClass3 K) z →
        ∀ T : Subgroup G, IsTwinAt (conjClass3 K) K T z → IsClassicalMember3 T z →
          ∀ e : TwinElt K T z, LocalOddCentral (conjClass3 K) {e.u} →
            LocalOddThreeFree3 (conjClass3 K) e.u →
              ∀ (ι : Type) [Finite ι]
                (D : LieSystemData3 ι (locQuot (conjClass3 K) e.u) (locFamily (conjClass3 K) e.u)),
                Nat.card ι = 1 → ∀ i : ι, ∃ (t' : StatedLieTag) (n' : ℕ),
                  D.kind i = CompData.model t' n' ∧ TwinRow t' n'

@[expose] def TwinCentralizingNe3 (tY : StatedLieTag) (nY : ℕ) : Prop :=
  ∀ (R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K)
    (x x' ã ã' : (modelUniv tY nY 3 1 Nat.prime_three).K),
    TwinDatumOn tY (modelUniv tY nY 3 1 Nat.prime_three) R R' x x' → ã ∈ R → ã' ∈ R' →
    ã * ã * x⁻¹ ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K →
    ã' * ã' * x'⁻¹ ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K →
    ∃ S ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
      S ≤ Subgroup.centralizer ({ã * ã'} : Set (modelUniv tY nY 3 1 Nat.prime_three).K)

theorem TwinYNoCentral3On.union {P₁ P₂ : StatedLieTag → ℕ → Prop} (h₁ : TwinYNoCentral3On P₁)
    (h₂ : TwinYNoCentral3On P₂) : TwinYNoCentral3On fun t n => P₁ t n ∨ P₂ t n :=
  fun h3 G _ _ _ hnab K z hR t n hrow hP hshape T hT clsT e M hM =>
    hP.elim (fun hp => h₁ h3 G hnab K z hR t n hrow hp hshape T hT clsT e M hM)
      (fun hp => h₂ h3 G hnab K z hR t n hrow hp hshape T hT clsT e M hM)

theorem twinYType3On_union {P₁ P₂ : StatedLieTag → ℕ → Prop} (h₁ : Q3TY.TwinYType3On P₁)
    (h₂ : Q3TY.TwinYType3On P₂) : Q3TY.TwinYType3On fun t n => P₁ t n ∨ P₂ t n :=
  fun G _ _ _ hnab K z hR t n hrow hP hshape T hT clsT e h1 h3 =>
    hP.elim (fun hp => h₁ G hnab K z hR t n hrow hp hshape T hT clsT e h1 h3)
      (fun hp => h₂ G hnab K z hR t n hrow hp hshape T hT clsT e h1 h3)

theorem twinYType3On_mono {P₁ P₂ : StatedLieTag → ℕ → Prop} (h : ∀ t n, P₂ t n → P₁ t n)
    (h₁ : Q3TY.TwinYType3On P₁) : Q3TY.TwinYType3On P₂ :=
  fun G _ _ _ hnab K z hR t n hrow hP hshape T hT clsT e h1 h3 =>
    h₁ G hnab K z hR t n hrow (h t n hP) hshape T hT clsT e h1 h3

end CFSG.ClassicalInvolution.Q3.Q3TIY
