module

public import CFSG.ClassicalInvolution.Q3.Chart
public import CFSG.ClassicalInvolution.Q3.Generation
public import CFSG.ClassicalInvolution.Q3.Q3TCP1
public import CFSG.ClassicalInvolution.RouteD.TwinYStatements
public import CFSG.ClassicalInvolution.Q3.Q3WADict

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinRow IsTwinAt TwinElt twinYModel)
open CFSG.Assembly.LowTwoRank (StatedLieTag)

section Involutions

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem eq_of_mem_of_sq (hK : IsClassicalMember3 K z) {x : G} (hx : x ∈ K) (hsq : x * x = 1)
    (hx1 : x ≠ 1) : x = z := by
  obtain ⟨φ, hφ⟩ := hK.exists_chart
  rcases hφ.eq_one_or_eq_of_sq hK.isCentralInvolution hx hsq with h | h
  · exact absurd h hx1
  · exact h

end Involutions

section Inputs


@[expose] def CommutingProductP1Input3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    RouteD3Setup K z → ∀ M ∈ conjClass3 K, Commutes K M → ∀ x : G, x ∈ K ⊔ M →
      orderOf x = 2 → x ∉ K → x ∉ M →
        LocalOddCentral (conjClass3 K) {x} ∧ LocalOddThreeFree3 (conjClass3 K) x

theorem productP1Input3_of_commuting (h : CommutingProductP1Input3) : Q3TC.ProductP1Input3 := by
  intro G _ _ _ K z hR M hM w hw hKM hzw
  have hzK : z ∈ K := hR.cls.mem
  have hwM : w ∈ M := hw.mem
  have hz2 : z * z = 1 := hR.cls.isCentralInvolution.sq
  have hw2 : w * w = 1 := hw.isCentralInvolution.sq
  have hcomm : z * w = w * z := hKM z hzK w hwM
  have hsq : (z * w) * (z * w) = 1 := by
    calc z * w * (z * w) = z * (w * z) * w := by group
      _ = z * (z * w) * w := by rw [← hcomm]
      _ = (z * z) * (w * w) := by group
      _ = 1 := by rw [hz2, hw2, one_mul]
  have hne1 : z * w ≠ 1 := by
    intro h1
    apply hzw
    calc z = z * (w * w) := by rw [hw2, mul_one]
      _ = (z * w) * w := (mul_assoc _ _ _).symm
      _ = w := by rw [h1, one_mul]
  have hord : orderOf (z * w) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hne1
  have hnK : z * w ∉ K := by
    intro hmem
    have hwK : w ∈ K := by
      have := K.mul_mem (K.inv_mem hzK) hmem
      rwa [inv_mul_cancel_left] at this
    exact hzw (eq_of_mem_of_sq hR.cls hwK hw2 hw.ne_one).symm
  have hnM : z * w ∉ M := by
    intro hmem
    have hzM : z ∈ M := by
      have := M.mul_mem hmem (M.inv_mem hwM)
      rwa [mul_inv_cancel_right] at this
    exact hzw (eq_of_mem_of_sq hw hzM hz2 hR.cls.ne_one)
  exact h G K z hR M hM hKM (z * w) (Subgroup.mul_mem_sup hzK hwM) hord hnK hnM

end Inputs

section Twin


@[expose] def TwinInvolution3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z → ∀ (t : StatedLieTag) (n : ℕ),
      TwinRow t n → LocalShapeC3 2 (CompData.model t n) (conjClass3 K) z →
        ∀ T : Subgroup G, IsTwinAt (conjClass3 K) K T z → IsClassicalMember3 T z

@[expose] def TwinInvolution3On (P : StatedLieTag → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z → ∀ (t : StatedLieTag) (n : ℕ),
      TwinRow t n → P t n → LocalShapeC3 2 (CompData.model t n) (conjClass3 K) z →
        ∀ T : Subgroup G, IsTwinAt (conjClass3 K) K T z → IsClassicalMember3 T z

theorem TwinInvolution3.on (h : TwinInvolution3) (P : StatedLieTag → ℕ → Prop) :
    TwinInvolution3On P :=
  fun G _ _ _ hnab K z hR t n hrow _ hshape T hT => h G hnab K z hR t n hrow hshape T hT

@[expose] def TwinYType3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z → ∀ (t : StatedLieTag) (n : ℕ),
      TwinRow t n → LocalShapeC3 2 (CompData.model t n) (conjClass3 K) z →
        ∀ T : Subgroup G, IsTwinAt (conjClass3 K) K T z → IsClassicalMember3 T z →
          ∀ e : TwinElt K T z, LocalOddCentral (conjClass3 K) {e.u} →
            LocalOddThreeFree3 (conjClass3 K) e.u →
              LocalShapeC3 0 (CompData.model (twinYModel 3 t n).1 (twinYModel 3 t n).2)
                (conjClass3 K) e.u

@[expose] def TwinYType3On (P : StatedLieTag → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z → ∀ (t : StatedLieTag) (n : ℕ),
      TwinRow t n → P t n → LocalShapeC3 2 (CompData.model t n) (conjClass3 K) z →
        ∀ T : Subgroup G, IsTwinAt (conjClass3 K) K T z → IsClassicalMember3 T z →
          ∀ e : TwinElt K T z, LocalOddCentral (conjClass3 K) {e.u} →
            LocalOddThreeFree3 (conjClass3 K) e.u →
              LocalShapeC3 0 (CompData.model (twinYModel 3 t n).1 (twinYModel 3 t n).2)
                (conjClass3 K) e.u

theorem TwinYType3.on (h : TwinYType3) (P : StatedLieTag → ℕ → Prop) : TwinYType3On P :=
  fun G _ _ _ hnab K z hR t n hrow _ hshape T hT hclsT e h1 h3 =>
    h G hnab K z hR t n hrow hshape T hT hclsT e h1 h3

end Twin

end CFSG.ClassicalInvolution.Q3.Q3TY
