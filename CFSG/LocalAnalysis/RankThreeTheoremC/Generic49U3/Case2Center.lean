module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Comp
import CFSG.Walter.W67.CentralExt
import CFSG.LocalAnalysis.AGLEmbedding.ReducedQuotient
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

namespace Case2Data

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P T D F : Subgroup Y} {x : Y}

private theorem T_comm_of_commute (h : Case2Data p P T D F x) {u : Y} (hu : u ∈ T)
    (hnc : u ∉ zOf T) {a b : Y} (ha : a ∈ T) (hb : b ∈ T)
    (hau : a * u = u * a) (hbu : b * u = u * b) : a * b = b * a := by
  haveI := h.fact
  have hZcard : Nat.card (zOf T) = p :=
    card_inf_centralizer_of_nonabelian_card_p_cube h.pdata.T_card h.pdata.T_nonab
  set C : Subgroup Y := T ⊓ centralizer ({u} : Set Y) with hC
  have hCT : C ≤ T := inf_le_left
  have hZC : zOf T ≤ C :=
    inf_le_inf_left T (centralizer_le (Set.singleton_subset_iff.mpr hu))
  have hdvd1 : Nat.card C ∣ p ^ 3 := h.pdata.T_card ▸ Subgroup.card_dvd_of_le hCT
  have hdvd2 : p ∣ Nat.card C := hZcard ▸ Subgroup.card_dvd_of_le hZC
  obtain ⟨i, hi, hCi⟩ := (Nat.dvd_prime_pow h.prime).mp hdvd1
  have hmemC : u ∈ C := ⟨hu, mem_centralizer_iff.mpr (by simp)⟩
  have hi2 : i = 2 := by
    interval_cases i
    · exfalso
      rw [pow_zero] at hCi
      rw [hCi] at hdvd2
      have := Nat.le_of_dvd one_pos hdvd2
      have := h.five
      omega
    · exfalso
      apply hnc
      have hZeq : zOf T = C := Subgroup.eq_of_le_of_card_ge hZC (by rw [hCi, hZcard, pow_one])
      rw [hZeq]
      exact hmemC
    · rfl
    · exfalso
      apply hnc
      have hCeq : C = T :=
        Subgroup.eq_of_le_of_card_ge hCT (by rw [hCi, h.pdata.T_card])
      refine ⟨hu, mem_centralizer_iff.mpr fun g hg => ?_⟩
      have hgC : g ∈ C := hCeq ▸ hg
      exact (mem_centralizer_iff.mp hgC.2 u (Set.mem_singleton u)).symm
  have hcomm : IsMulCommutative C := by
    rw [hi2] at hCi
    exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hCi
  have haC : a ∈ C := ⟨ha, mem_centralizer_iff.mpr (by simpa using hau.symm)⟩
  have hbC : b ∈ C := ⟨hb, mem_centralizer_iff.mpr (by simpa using hbu.symm)⟩
  exact setLike_mul_comm haC hbC

private theorem comm_iff (h : Case2Data p P T D F x) {t t' : Y} (ht : t ∈ T) (ht' : t' ∈ T)
    {d d' : Y} (hd : d ∈ D) (hd' : d' ∈ D) :
    (t * d) * (t' * d') = (t' * d') * (t * d) ↔ t * t' = t' * t := by
  have e1 : d * t' = t' * d := (h.pdata.comm t' ht' d hd).symm
  have e2 : d' * t = t * d' := (h.pdata.comm t ht d' hd').symm
  haveI := h.pdata.D_cyc
  have e3 : d * d' = d' * d := setLike_mul_comm hd hd'
  have l : (t * d) * (t' * d') = (t * t') * (d * d') := by
    calc (t * d) * (t' * d') = t * (d * t') * d' := by simp only [mul_assoc]
      _ = t * (t' * d) * d' := by rw [e1]
      _ = (t * t') * (d * d') := by simp only [mul_assoc]
  have r : (t' * d') * (t * d) = (t' * t) * (d * d') := by
    calc (t' * d') * (t * d) = t' * (d' * t) * d := by simp only [mul_assoc]
      _ = t' * (t * d') * d := by rw [e2]
      _ = (t' * t) * (d' * d) := by simp only [mul_assoc]
      _ = (t' * t) * (d * d') := by rw [e3]
  rw [l, r]
  exact mul_left_inj _

open CFSG.ABGLocalTools in
private theorem exists_noncomm_inf (h : Case2Data p P T D F x) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) (hc : center L ≠ ⊥) :
    ∃ a ∈ P ⊓ L, ∃ b ∈ P ⊓ L, a * b ≠ b * a := by
  by_contra hcon0
  have hcon : ∀ a ∈ P ⊓ L, ∀ b ∈ P ⊓ L, a * b = b * a := fun a ha b hb => by
    by_contra hne
    exact hcon0 ⟨a, ha, b, hb, hne⟩
  apply hc
  haveI := h.fact
  have hN : P ≤ normalizer (L : Set Y) := h.P_le_normalizer hL
  have hPsyl : IsSylowOf p P ⊤ := by
    obtain ⟨S, hS⟩ := h.sylow
    rw [isSylowOf_iff]
    refine ⟨le_top, hS ▸ S.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right, ← hS]
    exact S.not_dvd_index
  have hPL : IsSylowOf p (P ⊓ L) L :=
    (hPsyl.of_le (le_sup_left : P ≤ P ⊔ L) le_top).inf_of_le_normalizer le_sup_right
      (sup_le hN le_normalizer)
  obtain ⟨Q, hQ⟩ := hPL.exists_sylow_eq_subgroupOf
  have hQab : IsMulCommutative (Q : Subgroup L) :=
    IsMulCommutative.of_comm fun a b => by
      have ha : (a : Y) ∈ P ⊓ L :=
        Subgroup.mem_subgroupOf.mp ((SetLike.ext_iff.mp hQ a.1).mp a.2)
      have hb : (b : Y) ∈ P ⊓ L :=
        Subgroup.mem_subgroupOf.mp ((SetLike.ext_iff.mp hQ b.1).mp b.2)
      exact Subtype.ext (Subtype.ext (hcon _ ha _ hb))
  have key := CFSG.Walter.W67.inf_commutator_eq_bot_of_isPGroup Q hQab (Z := center L) le_rfl
    (isPGroup_center_of_isComponentOf h.prime h.core hL)
  rwa [hL.2.2.1, inf_top_eq] at key

theorem eq_of_center_ne_bot (h : Case2Data p P T D F x) {L L' : Subgroup Y}
    (hL : IsComponentOf L ⊤) (hL' : IsComponentOf L' ⊤) (hc : center L ≠ ⊥) (hc' : center L' ≠ ⊥) :
    L = L' := by
  by_contra hne
  obtain ⟨a₁, ha₁, a₂, ha₂, ha⟩ := h.exists_noncomm_inf hL hc
  obtain ⟨b₁, hb₁, b₂, hb₂, hb⟩ := h.exists_noncomm_inf hL' hc'
  have hLL : ⁅L, L'⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne L L' hL hL' hne
  have hcomm : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hLL ha) b hb).symm
  obtain ⟨t₁, ht₁, d₁, hd₁, rfl⟩ := h.exists_mul a₁ ha₁.1
  obtain ⟨t₂, ht₂, d₂, hd₂, rfl⟩ := h.exists_mul a₂ ha₂.1
  obtain ⟨u₁, hu₁, e₁, he₁, rfl⟩ := h.exists_mul b₁ hb₁.1
  obtain ⟨u₂, hu₂, e₂, he₂, rfl⟩ := h.exists_mul b₂ hb₂.1
  have hat : t₁ * t₂ ≠ t₂ * t₁ := fun e => ha ((h.comm_iff ht₁ ht₂ hd₁ hd₂).mpr e)
  have hbt : u₁ * u₂ ≠ u₂ * u₁ := fun e => hb ((h.comm_iff hu₁ hu₂ he₁ he₂).mpr e)
  have hcross : ∀ {t d u e : Y}, t ∈ T → d ∈ D → u ∈ T → e ∈ D →
      t * d ∈ L → u * e ∈ L' → t * u = u * t := fun ht hd hu he hL hL' =>
    (h.comm_iff ht hu hd he).mp (hcomm _ hL _ hL')
  have hnc : u₁ ∉ zOf T := fun hz =>
    hbt (mem_centralizer_iff.mp hz.2 u₂ hu₂).symm
  exact hat (h.T_comm_of_commute hu₁ hnc ht₁ ht₂
    (hcross ht₁ hd₁ hu₁ he₁ ha₁.2 hb₁.2)
    (hcross ht₂ hd₂ hu₁ he₁ ha₂.2 hb₁.2))

end Case2Data

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
