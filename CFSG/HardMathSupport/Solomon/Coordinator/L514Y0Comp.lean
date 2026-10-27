module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3ALayer
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
open scoped commutatorElement

theorem l514y0_normal_le_center_or_top {K : Type*} [Group K] (hq : CFSG.Open.IsQuasisimple K)
    (M : Subgroup K) [M.Normal] : M ≤ Subgroup.center K ∨ M = ⊤ := by
  obtain ⟨hperf, hs⟩ := hq
  have hnorm : (M.map (QuotientGroup.mk' (Subgroup.center K))).Normal :=
    Subgroup.Normal.map ‹M.Normal› (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have := hnorm
  rcases hs.eq_bot_or_eq_top_of_normal (M.map (QuotientGroup.mk' (Subgroup.center K))) with h | h
  · left
    intro m hm
    have h1 : QuotientGroup.mk' (Subgroup.center K) m ∈
        M.map (QuotientGroup.mk' (Subgroup.center K)) := Subgroup.mem_map_of_mem _ hm
    rw [h, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff m).mp h1
  · right
    have hsup : M ⊔ Subgroup.center K = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center K)) M
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hle : commutator K ≤ M :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [hperf] at hle
    exact top_le_iff.mp hle

theorem l514y0_eq_top_of_sup_center {K : Type*} [Group K] (hperf : commutator K = ⊤)
    {J : Subgroup K} (h : J ⊔ Subgroup.center K = ⊤) : J = ⊤ := by
  refine top_le_iff.1 ?_
  rw [← hperf, commutator_def, Subgroup.commutator_le]
  intro a _ b _
  have ha : a ∈ J ⊔ Subgroup.center K := h ▸ Subgroup.mem_top a
  have hb : b ∈ J ⊔ Subgroup.center K := h ▸ Subgroup.mem_top b
  obtain ⟨j₁, hj₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 ha
  obtain ⟨j₂, hj₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hb
  have hc1 : Commute z₁ j₂ := (Subgroup.mem_center_iff.1 hz₁ j₂).symm
  have hc2 : Commute z₁ z₂ := (Subgroup.mem_center_iff.1 hz₁ z₂).symm
  have hc3 : Commute z₂ j₁ := (Subgroup.mem_center_iff.1 hz₂ j₁).symm
  rw [commutatorElement_mul_mul' hc1 hc2 hc3]
  rw [commutatorElement_def]
  exact J.mul_mem (J.mul_mem (J.mul_mem hj₁ hj₂) (J.inv_mem hj₁)) (J.inv_mem hj₂)

theorem l514y0_glaPComponent_self {Y : Type*} [Group Y] [Finite Y] {S : Subgroup Y}
    (hq : CFSG.Open.IsQuasisimple ↥S) (h3 : 3 ∣ Nat.card S) : GLAPComponent 3 S S := by
  set O : Subgroup ↥S := GLAPPrimeCore 3 ↥S with hO
  have hOtop : O ≠ ⊤ := by
    intro h
    have hc := coprime_card_gLAPPrimeCore_aux 3 ↥S
    rw [← hO, h, Subgroup.card_top] at hc
    exact absurd (Nat.eq_one_of_dvd_coprimes hc (dvd_refl 3) h3) (by norm_num)
  have hnt : Nontrivial (↥S ⧸ O) := by
    rw [QuotientGroup.nontrivial_iff]
    exact hOtop
  have hqq : CFSG.Open.IsQuasisimple (↥S ⧸ O) :=
    isQuasisimple_of_surjective_of_nontrivial hq (QuotientGroup.mk' O) (QuotientGroup.mk'_surjective _)
  have hL : (S.subgroupOf S).map (QuotientGroup.mk' O) = ⊤ := by
    rw [Subgroup.subgroupOf_self, Subgroup.map_top, MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  refine ⟨le_rfl, IsSubnormal.refl S, ⟨le_top, ?_, ?_⟩, ?_⟩
  · rw [hL]; exact IsSubnormal.refl _
  · rw [hL]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      Subgroup.topEquiv.symm hqq
  · intro J hJ _ heq
    rw [hL] at heq
    have hsup : J.subgroupOf S ⊔ O = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' O) (J.subgroupOf S)
      rw [heq, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have : O.Normal := GLAPPrimeCore.normal 3 ↥S
    have hOZ : O ≤ Subgroup.center ↥S := by
      rcases l514y0_normal_le_center_or_top hq O with h | h
      · exact h
      · exact absurd h hOtop
    have hsup' : J.subgroupOf S ⊔ Subgroup.center ↥S = ⊤ :=
      top_le_iff.1 (hsup ▸ sup_le_sup_left hOZ _)
    have htop := l514y0_eq_top_of_sup_center hq.1 hsup'
    exact absurd (Subgroup.subgroupOf_eq_top.1 htop) (not_le_of_gt hJ)

theorem l514y0_comp_iff {Y : Type*} [Group Y] [Finite Y] {F S : Subgroup Y} (hSF : S ≤ F)
    (hcomm : ⁅F, F⁆ ≤ S) (hq : CFSG.Open.IsQuasisimple ↥S) (h3 : 3 ∣ Nat.card S) :
    ∀ J : Subgroup Y, GLAPComponent 3 F J ↔ J = S := by
  intro J
  constructor
  · intro hJ
    have hJF : J ≤ F := hJ.1
    have hperf := glaPComponent_perfect hJ
    have hJS : J ≤ S := by
      calc J = ⁅J, J⁆ := hperf.symm
        _ ≤ ⁅F, F⁆ := Subgroup.commutator_mono hJF hJF
        _ ≤ S := hcomm
    have hsn : IsSubnormal J S := isSubnormal_of_le_of_le hJ.2.1 hJS hSF
    exact eq_of_isSubnormal_of_quasisimple hq hsn hperf (glaPComponent_ne_bot hJ)
  · rintro rfl
    exact glaPComponent_of_normal_sub Nat.prime_three hSF (normal_of_commutator_le hSF hcomm)
      (l514y0_glaPComponent_self hq h3)

end CFSG.HardMathSupport.Solomon.Coordinator
