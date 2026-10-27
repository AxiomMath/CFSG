module

public import CFSG.ClassicalInvolution.Q3.SP3Twin
public import CFSG.ClassicalInvolution.Uniform.UTwinSolv
import CFSG.GroupTheory.SubnormalJoin

public section

namespace CFSG.ClassicalInvolution.Uniform.U4

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem isSubnormal_subgroupOf_top' {X K : Subgroup G} (h : IsSubnormal K X) :
    (K.subgroupOf X).IsSubnormal := by
  have := isSubnormal_subgroupOf h X
  rw [Subgroup.subgroupOf_self] at this
  exact Components.mathlib_subnormal_of_chain this Subgroup.IsSubnormal.top

theorem twinLemma3_central {C J₁ J₂ : Subgroup G} {z : G} (hC : oddCoreIn C = ⊥)
    (h₁ : IsSubnormal J₁ C) (h₂ : IsSubnormal J₂ C)
    (e₁ : Nonempty (↥J₁ ≃* SL(2, ZMod 3))) (e₂ : Nonempty (↥J₂ ≃* SL(2, ZMod 3)))
    (hz : orderOf z = 2) (hz₁ : z ∈ J₁) (hzc : ∀ y ∈ C, z * y = y * z) :
    J₁ = J₂ ∨ ⁅J₁, J₂⁆ = ⊥ := by
  obtain ⟨e₁⟩ := e₁
  obtain ⟨e₂⟩ := e₂
  have hJ₁C : J₁ ≤ C := isSubnormal_le h₁
  have hJ₂C : J₂ ≤ C := isSubnormal_le h₂
  have hHC : J₁ ⊔ J₂ ≤ C := sup_le hJ₁C hJ₂C
  have hHsub : IsSubnormal (J₁ ⊔ J₂) C := by
    have a₁ := isSubnormal_subgroupOf_top' h₁
    have a₂ := isSubnormal_subgroupOf_top' h₂
    have hj := CFSG.GroupTheory.isSubnormal_sup a₁ a₂
    have := Components.chain_map C.subtype (Components.chain_of_mathlib_subnormal hj)
    rwa [Subgroup.map_top, Subgroup.range_subtype, Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hJ₁C, Subgroup.map_subgroupOf_eq_of_le hJ₂C] at this
  have hOH : oddCoreIn (J₁ ⊔ J₂) = ⊥ :=
    le_bot_iff.mp (hC ▸ oddCoreIn_le_of_isSubnormal hHsub)
  have hJ₁H : J₁ ≤ J₁ ⊔ J₂ := le_sup_left
  have hJ₂H : J₂ ≤ J₁ ⊔ J₂ := le_sup_right
  have hsub : ∀ J : Subgroup G, IsSubnormal J C → J ≤ J₁ ⊔ J₂ → IsSubnormal J (J₁ ⊔ J₂) := by
    intro J hJ hJH
    have := isSubnormal_inf hJ (J₁ ⊔ J₂)
    rwa [inf_eq_left.mpr hJH, inf_eq_right.mpr hHC] at this
  set H : Subgroup G := J₁ ⊔ J₂ with hH
  have hY : J₁.subgroupOf H ⊔ J₂.subgroupOf H = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hJ₁H,
      Subgroup.map_subgroupOf_eq_of_le hJ₂H, Subgroup.map_top, Subgroup.range_subtype]
  have hO : ∀ N : Subgroup ↥H, N.Normal → Odd (Nat.card N) → N = ⊥ := by
    intro N hN hodd
    have hle : N.map H.subtype ≤ oddCoreIn H := by
      refine le_oddCoreIn_of_normalizes (Subgroup.map_subtype_le N) ?_ ?_
      · intro x hx
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · rintro ⟨n, hn, rfl⟩
          exact ⟨⟨x, hx⟩ * n * ⟨x, hx⟩⁻¹, hN.conj_mem n hn ⟨x, hx⟩, rfl⟩
        · rintro ⟨n, hn, hny⟩
          refine ⟨⟨x, hx⟩⁻¹ * n * ⟨x, hx⟩, by simpa using hN.conj_mem n hn ⟨x, hx⟩⁻¹, ?_⟩
          have h : (n : G) = x * y * x⁻¹ := hny
          have : y = x⁻¹ * (n : G) * x := by rw [h]; group
          simp [this]
      · rwa [Subgroup.card_map_of_injective H.subtype_injective]
    rw [hOH, le_bot_iff] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective N H.subtype_injective).mp hle
  have hz' : orderOf (⟨z, hJ₁H hz₁⟩ : ↥H) = 2 := by
    rw [← hz]
    exact Subgroup.orderOf_mk z _
  have e₁' : ↥(J₁.subgroupOf H) ≃* SL(2, ZMod 3) := (Subgroup.subgroupOfEquivOfLe hJ₁H).trans e₁
  have e₂' : ↥(J₂.subgroupOf H) ≃* SL(2, ZMod 3) := (Subgroup.subgroupOfEquivOfLe hJ₂H).trans e₂
  have hsolv : Group.IsSolvable ↥H :=
    Q3.Twin.isSolvable_of_sup_eq_top hY (isSubnormal_subgroupOf_top' (hsub J₁ h₁ hJ₁H))
      (isSubnormal_subgroupOf_top' (hsub J₂ h₂ hJ₂H)) (Q3.Twin.isSolvable_subgroup e₁')
      (Q3.Twin.isSolvable_subgroup e₂')
  have hzcH : ∀ y : ↥H, (⟨z, hJ₁H hz₁⟩ : ↥H) * y = y * ⟨z, hJ₁H hz₁⟩ := fun y =>
    Subtype.ext (hzc y.1 (hHC y.2))
  rcases Q3.SP3.twin_of_central hsolv hO (isSubnormal_subgroupOf_top' (hsub J₁ h₁ hJ₁H))
      (isSubnormal_subgroupOf_top' (hsub J₂ h₂ hJ₂H)) e₁' e₂' hz' (Subgroup.mem_subgroupOf.mpr hz₁)
      hzcH with h | h
  · left
    have := congrArg (Subgroup.map H.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hJ₁H, Subgroup.map_subgroupOf_eq_of_le hJ₂H] at this
  · right
    have := congrArg (Subgroup.map H.subtype) h
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJ₁H,
      Subgroup.map_subgroupOf_eq_of_le hJ₂H, Subgroup.map_bot] at this

omit [Finite G] in
theorem eq_of_mk_oddCore_eq {X : Type} [Group X] [Finite X] {z t : X} (hz : orderOf z = 2)
    (hzt : z * t = t * z) (ht : orderOf t = 2)
    (h : QuotientGroup.mk' (classicalInvolutionOddCore X) z =
      QuotientGroup.mk' (classicalInvolutionOddCore X) t) : z = t := by
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz, pow_two] at this
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht, pow_two] at this
  have hmem : z⁻¹ * t ∈ classicalInvolutionOddCore X := by
    have h' : (z : X ⧸ classicalInvolutionOddCore X) = (t : X ⧸ classicalInvolutionOddCore X) := h
    exact QuotientGroup.eq.mp h'
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  rw [hzi] at hmem
  have hsq : (z * t) ^ 2 = 1 := by
    rw [pow_two]
    calc z * t * (z * t) = z * (t * z) * t := by group
      _ = z * (z * t) * t := by rw [hzt]
      _ = (z * z) * (t * t) := by group
      _ = 1 := by rw [hz2, ht2, one_mul]
  have hdvd2 : orderOf (z * t) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have hodd : Odd (Nat.card (classicalInvolutionOddCore X)) :=
    CFSG.ComponentClassification.OddCore.odd_card X
  have hdvdN := Subgroup.orderOf_dvd_natCard _ hmem
  have h1 : orderOf (z * t) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hdvdN
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvdN)
  have h2 : z * t = 1 := orderOf_eq_one_iff.mp h1
  calc z = (z * t) * t⁻¹ := by group
    _ = t⁻¹ := by rw [h2, one_mul]
    _ = t := inv_eq_of_mul_eq_one_right ht2

theorem commutator_le_oddCore_central {X : Type} [Group X] [Finite X] {K J : Subgroup X}
    {z t : X} (hK : IsSubnormal K ⊤) (hJ : IsSubnormal J ⊤) (hz : orderOf z = 2) (hzK : z ∈ K)
    (ht : orderOf t = 2) (htJ : t ∈ J) (hzt : z * t = t * z) (hne : z ≠ t)
    (htc : ∀ y : X, t * y = y * t)
    (eK : Nonempty (K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3)))
    (eJ : Nonempty (J ⧸ classicalInvolutionOddCore J ≃* SL(2, ZMod 3))) :
    ⁅K, J⁆ ≤ classicalInvolutionOddCore X := by
  obtain ⟨e₁⟩ := eK
  obtain ⟨e₂⟩ := eJ
  set π := QuotientGroup.mk' (classicalInvolutionOddCore X) with hπ
  have eK' : ↥(K.map π) ≃* SL(2, ZMod 3) := (Components.oddCore_image_equiv K hK).symm.trans e₁
  have eJ' : ↥(J.map π) ≃* SL(2, ZMod 3) := (Components.oddCore_image_equiv J hJ).symm.trans e₂
  have htc' : ∀ y ∈ (⊤ : Subgroup (X ⧸ classicalInvolutionOddCore X)), π t * y = y * π t := by
    intro y _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    show π t * π x = π x * π t
    rw [← map_mul, ← map_mul, htc x]
  rcases twinLemma3_central (C := ⊤) (J₁ := J.map π) (J₂ := K.map π) (z := π t)
      oddCoreIn_top_quotient (image_oddQuotient_isSubnormal hJ) (image_oddQuotient_isSubnormal hK)
      ⟨eJ'⟩ ⟨eK'⟩ (orderOf_mk_oddCore_eq_two ht) (Subgroup.mem_map_of_mem _ htJ) htc' with h | h
  · exfalso
    have hzK' : π z ∈ J.map π := h ▸ Subgroup.mem_map_of_mem π hzK
    have htJ' : π t ∈ J.map π := Subgroup.mem_map_of_mem π htJ
    have hz2 : orderOf (π z) = 2 := orderOf_mk_oddCore_eq_two hz
    have ht2 : orderOf (π t) = 2 := orderOf_mk_oddCore_eq_two ht
    have hsq : ∀ {w : X ⧸ classicalInvolutionOddCore X}, orderOf w = 2 → w ^ 2 = 1 ∧ w ≠ 1 := by
      intro w hw
      refine ⟨by rw [← hw]; exact pow_orderOf_eq_one w, ?_⟩
      intro h1
      rw [h1, orderOf_one] at hw
      omega
    have hu : π z = π t :=
      Q3.Twin.involution_unique_in eJ' hzK' htJ' (hsq hz2).1 (hsq ht2).1 (hsq hz2).2 (hsq ht2).2
    exact hne (eq_of_mk_oddCore_eq hz hzt ht hu)
  · have h' : ⁅K.map π, J.map π⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact h
    have h1 : (⁅K, J⁆).map π = ⊥ := by rw [Subgroup.map_commutator]; exact h'
    have h2 : ⁅K, J⁆ ≤ π.ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      have : π x ∈ (⁅K, J⁆).map π := Subgroup.mem_map_of_mem π hx
      rw [h1] at this
      exact Subgroup.mem_bot.mp this
    rwa [hπ, QuotientGroup.ker_mk'] at h2

theorem commutator_le_oddCoreIn_central {C K J : Subgroup G} {z t : G}
    (hKC : IsSubnormal K C) (hJC : IsSubnormal J C) (hz : orderOf z = 2) (hzK : z ∈ K)
    (ht : orderOf t = 2) (htJ : t ∈ J) (hzt : z * t = t * z) (hne : z ≠ t)
    (htc : ∀ y ∈ C, t * y = y * t)
    (eK : Nonempty (K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3)))
    (eJ : Nonempty (J ⧸ classicalInvolutionOddCore J ≃* SL(2, ZMod 3))) :
    ⁅K, J⁆ ≤ Balance.oddCoreIn C := by
  have hKle : K ≤ C := isSubnormal_le hKC
  have hJle : J ≤ C := isSubnormal_le hJC
  obtain ⟨e₁⟩ := eK
  obtain ⟨e₂⟩ := eJ
  have hz' : orderOf (⟨z, hKle hzK⟩ : C) = 2 := by rw [Subgroup.orderOf_mk]; exact hz
  have ht' : orderOf (⟨t, hJle htJ⟩ : C) = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  have h := commutator_le_oddCore_central (K := K.subgroupOf C) (J := J.subgroupOf C)
    (z := (⟨z, hKle hzK⟩ : C)) (t := (⟨t, hJle htJ⟩ : C)) (isSubnormal_subgroupOf_top hKC)
    (isSubnormal_subgroupOf_top hJC) hz' (Subgroup.mem_subgroupOf.mpr hzK) ht'
    (Subgroup.mem_subgroupOf.mpr htJ) (Subtype.ext hzt) (fun h => hne (congrArg Subtype.val h))
    (fun y => Subtype.ext (htc y.1 y.2)) (nonempty_quotEquiv_subgroupOf hKle e₁)
    (nonempty_quotEquiv_subgroupOf hJle e₂)
  have hmap : ⁅K, J⁆ = (⁅K.subgroupOf C, J.subgroupOf C⁆).map C.subtype := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKle,
      Subgroup.map_subgroupOf_eq_of_le hJle]
  rw [hmap]
  exact Subgroup.map_mono h

end CFSG.ClassicalInvolution.Uniform.U4
