module

public import CFSG.ClassicalInvolution.Q3.Q3AMPspG03
public import CFSG.ClassicalInvolution.Q3.Q3Y2WireAll
public import CFSG.ClassicalInvolution.Q3.Q3DInputs3

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3AM

section Axis



variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem BadStd8.exactLayer3_le_rankTwoSpan_axis (h : BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z) {K' : Subgroup G} (hKK' : K' ∈ omegaNbr Ω K)
    (hJK' : K' ∈ omegaNbr Ω J) {t₁ t₂ t₃ : G} {R₁ R₂ R₃ : Subgroup G}
    (hax : BadAxis K J K' z t t₁ t₂ t₃ R₁ R₂ R₃) :
    Q3NL.exactLayer3 Ω z ≤ rankTwoSpan (Subgroup.closure ({z, t, t₁ * t₂ * t₃} : Set G)) := by
  have hs := h.std
  have hΩ3 : Q3.InClass3 Ω := Q3T7.inClass3_of_stand3 hs.stand.toStand3
  have hz1sq : z * z = 1 := hs.hz.sq
  have hz2sq : t * t = 1 := hs.ht.sq
  have hzt : z * t = t * z := hax.z_comm
  have hs2 : (t₁ * t₂ * t₃) * (t₁ * t₂ * t₃) = 1 := hax.s_mul_self
  have hcz : z * (t₁ * t₂ * t₃) = (t₁ * t₂ * t₃) * z := hax.s_comm₁.eq
  have hct : t * (t₁ * t₂ * t₃) = (t₁ * t₂ * t₃) * t := hax.s_comm₂.eq
  have hspair : t₁ * t₂ * t₃ ∉ Subgroup.closure ({z, t} : Set G) := hax.s_not_mem_pair
  have hs1 : t₁ * t₂ * t₃ ≠ 1 := fun e => hspair (e ▸ Subgroup.one_mem _)
  have hAA : IsElemAbelian 2 (Subgroup.closure ({z, t, t₁ * t₂ * t₃} : Set G)) :=
    T8T.isElemAbelian_closure_three hz1sq hz2sq hs2 hzt hcz hct
  have hcard : Nat.card (Subgroup.closure ({z, t, t₁ * t₂ * t₃} : Set G)) = 8 :=
    T8T.natCard_closure_three hz1sq hz2sq hs2 hzt hcz hct hs.hz.ne_one hs.ht.ne_one hax.ne hs1
      hspair
  have hzA : z ∈ Subgroup.closure ({z, t, t₁ * t₂ * t₃} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hTwin : Q3Y2.ModelTwinGen3 := Q3Y2.modelTwinGen3_of_noExc Disc3.twinNoExc3_proved
  exact Q3NF.exactLayer3_le_rankTwoSpan hΩ3 hAA hcard.ge hzA
    (h.exactLayer3_generation hTwin hint hKK' hJK' hax)

end Axis

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
