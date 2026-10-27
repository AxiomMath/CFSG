module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F3Yd
public import CFSG.ClassicalInvolution.Balance.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Fink

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84_oddCore_cent {G : Type} [Group G] [Finite G] {E : Subgroup G}
    (hE : IsElemAb2 E 8) {o e : G} (ho : o ∈ oddCoreIn (normalizer (E : Set G))) (he : e ∈ E) :
    e * o = o * e := by
  set X : Subgroup G := normalizer (E : Set G) with hX
  set O : Subgroup G := oddCoreIn X with hO
  have hEnorm : E ≤ X := Subgroup.le_normalizer
  have heX : e ∈ X := hEnorm he
  have hoX : o ∈ X := CFSG.ClassicalInvolution.Balance.oddCoreIn_le X ho
  have hconjO : e * o⁻¹ * e⁻¹ ∈ O :=
    CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn heX (O.inv_mem ho)
  have hconjE : o * e * o⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp hoX e).mp he
  have hcE : o * e * o⁻¹ * e⁻¹ ∈ E := E.mul_mem hconjE (E.inv_mem he)
  have hcO : o * e * o⁻¹ * e⁻¹ ∈ O := by
    have h := O.mul_mem ho hconjO
    rw [show o * (e * o⁻¹ * e⁻¹) = o * e * o⁻¹ * e⁻¹ from by group] at h
    exact h
  have hoddO : Odd (Nat.card O) :=
    CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn X
  have hcop : Nat.Coprime (Nat.card E) (Nat.card O) := by
    rw [hE.2]
    exact (Nat.coprime_pow_left_iff (n := 8) (by norm_num) 2 (Nat.card O)).mpr
      (Nat.coprime_two_left.mpr hoddO)
  have hdisj : Disjoint E O := Subgroup.disjoint_of_coprime_natCard hcop
  have hinf : E ⊓ O = ⊥ := disjoint_iff.mp hdisj
  have hc1 : o * e * o⁻¹ * e⁻¹ = 1 := by
    have hmem : o * e * o⁻¹ * e⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hinf]
      exact ⟨hcE, hcO⟩
    simpa using hmem
  have hoeq : o * e = e * o := by
    calc o * e = (o * e * o⁻¹ * e⁻¹) * (e * o) := by group
      _ = e * o := by rw [hc1, one_mul]
  exact hoeq.symm

theorem sec8t84_ydata1 {G : Type} [Group G] [Finite G] {t : G} {E Y1 Y2 : Subgroup G}
    (hE : IsElemAb2 E 8) (h : Sec8XO G t E Y1 Y2) :
    ∃ H : Subgroup G,
      Sec8T84YData G Y1 (oddCoreIn (normalizer (E : Set G))) (E ⊓ Y1) H := by
  set X : Subgroup G := normalizer (E : Set G) with hX
  set O : Subgroup G := oddCoreIn X with hO
  obtain ⟨H, hHle, hHinf, hHsup⟩ := h.split1
  have hXnormO : X ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn X
  have hOnorm : (O.subgroupOf Y1).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.o_le1).mpr (h.le1.trans hXnormO)
  have hOodd : Odd (Nat.card O) :=
    CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn X
  have hVnorm : ((E ⊓ Y1).subgroupOf Y1).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    exact (le_inf h.le1 Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hVO : ∀ v ∈ E ⊓ Y1, ∀ o ∈ O, v * o = o * v :=
    fun v hv o ho => sec8t84_oddCore_cent hE ho hv.1
  refine ⟨H, ?_⟩
  exact ⟨h.o_le1, hOnorm, hOodd, h.e16_1, inf_le_right, hVnorm, hVO, h.quot1, h.trans1,
    hHle, hHinf, hHsup⟩

theorem sec8t84_ydata2 {G : Type} [Group G] [Finite G] {t : G} {E Y1 Y2 : Subgroup G}
    (hE : IsElemAb2 E 8) (h : Sec8XO G t E Y1 Y2) :
    ∃ H : Subgroup G,
      Sec8T84YData G Y2 (oddCoreIn (normalizer (E : Set G))) (E ⊓ Y2) H := by
  set X : Subgroup G := normalizer (E : Set G) with hX
  set O : Subgroup G := oddCoreIn X with hO
  obtain ⟨H, hHle, hHinf, hHsup⟩ := h.split2
  have hXnormO : X ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn X
  have hOnorm : (O.subgroupOf Y2).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.o_le2).mpr (h.le2.trans hXnormO)
  have hOodd : Odd (Nat.card O) :=
    CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn X
  have hVnorm : ((E ⊓ Y2).subgroupOf Y2).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    exact (le_inf h.le2 Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hVO : ∀ v ∈ E ⊓ Y2, ∀ o ∈ O, v * o = o * v :=
    fun v hv o ho => sec8t84_oddCore_cent hE ho hv.1
  refine ⟨H, ?_⟩
  exact ⟨h.o_le2, hOnorm, hOodd, h.e16_2, inf_le_right, hVnorm, hVO, h.quot2, h.trans2,
    hHle, hHinf, hHsup⟩

end CFSG.OddStandard.SmallF3.Omega
