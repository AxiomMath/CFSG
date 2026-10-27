module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34He
public import CFSG.Sporadic.HeldB.OuterCentQS

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.HeldB
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem card_dvd_three_of_odd_normal_heOuterC
    (N : Subgroup ↥heOuterC) [N.Normal] (hN : Odd (Nat.card N)) : Nat.card N ∣ 3 := by
  obtain ⟨-, hqs, hrel⟩ := ctbh_outer_centralizer_derived_quasisimple
  set D : Subgroup ↥heOuterC := heOuterD.subgroupOf heOuterC with hDdef
  have hidx : D.index = 2 := hrel
  haveI hDn : D.Normal := Subgroup.normal_of_index_eq_two hidx
  have hND : N ≤ D := by
    intro x hx
    have hc : Nat.card (↥heOuterC ⧸ D) = 2 := by
      rw [← Subgroup.index_eq_card]
      exact hidx
    have h2 : (QuotientGroup.mk x : ↥heOuterC ⧸ D) ^ 2 = 1 := by
      rw [← hc]
      exact pow_card_eq_one'
    have hn : (QuotientGroup.mk x : ↥heOuterC ⧸ D) ^ Nat.card N = 1 := by
      rw [← QuotientGroup.mk_pow]
      have h1 : (⟨x, hx⟩ : N) ^ Nat.card N = 1 := pow_card_eq_one'
      have h3 : x ^ Nat.card N = 1 := congrArg Subtype.val h1
      rw [h3, QuotientGroup.mk_one]
    have h1 : orderOf (QuotientGroup.mk x : ↥heOuterC ⧸ D) = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.2 hN) (orderOf_dvd_of_pow_eq_one h2)
        (orderOf_dvd_of_pow_eq_one hn)
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hqD : CFSG.IsQuasisimple ↥D :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe heOuterD_le_C).symm hqs
  have hcardD : Nat.card ↥D = 7560 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe heOuterD_le_C).toEquiv, card_heOuterD]
  haveI : (N.subgroupOf D).Normal := Subgroup.Normal.subgroupOf inferInstance D
  have hcardN : Nat.card (N.subgroupOf D) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hND).toEquiv
  have hne : N.subgroupOf D ≠ ⊤ := by
    intro h
    have h1 : Nat.card (N.subgroupOf D) = Nat.card ↥D := by
      rw [h, Subgroup.card_top]
    rw [hcardN, hcardD] at h1
    rw [h1] at hN
    exact (Nat.not_even_iff_odd.2 hN) (by decide)
  have hle : N.subgroupOf D ≤ center ↥D :=
    (CFSG.LocalCores.quasisimple_normal_subgroups hqD inferInstance).resolve_left hne
  have hcardZ : Nat.card (center ↥D) = 3 := by
    rw [Nat.card_congr
      (Subgroup.centerCongr (Subgroup.subgroupOfEquivOfLe heOuterD_le_C)).toEquiv,
      card_center_heOuterD]
  rw [← hcardN, ← hcardZ]
  exact Subgroup.card_dvd_of_le hle

theorem nonempty_fixedSubgroup_equiv_heOuterC
    {S : Type} [Group S] (e : S ≃* NativeSporadic.He) {σ : MulAut S} (hσ : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) :
    Nonempty (↥(fixedSubgroup σ) ≃* ↥heOuterC) := by
  set θ : S ≃* heP := e.trans heEquivP
  obtain ⟨x, hx, hxP, hx2⟩ := exists_heConjR_eq ctbh_full_automorphism_permutation_model.1
    (MulAut.congr θ σ) (by rw [orderOf_congr, hσ]) (by rwa [congr_mem_range_conj_iff])
  obtain ⟨g, hg, hxg⟩ := exists_conj_heAutU x.2 hxP hx2
  exact ⟨(((fixedSubgroupCongr θ σ).trans (MulEquiv.subgroupCongr (by rw [hx]))).trans
    (fixedSubgroupEquivOfConj x hg heAutU hxg)).trans (MulEquiv.subgroupCongr heOuterC_eq.symm)⟩

theorem he_false_of_odd_normal
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.He) {σ : MulAut S} (hσ : orderOf σ = 2)
    {N : Subgroup ↥(fixedSubgroup σ)} [N.Normal] (hodd : Odd (Nat.card N))
    (hdvd : Nat.card (↥(fixedSubgroup σ) ⧸ N) ∣ 1440) : False := by
  haveI := hS
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hcop : Nat.Coprime 2 (Nat.card N) := Nat.coprime_two_left.2 hodd
  by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
  · obtain ⟨s, rfl⟩ := hin
    have hs : orderOf s = 2 := by
      rw [← orderOf_injective _
        (ComponentClassification.CatLeaf.mulAut_conj_injective_of_simple hna) s]
      exact hσ
    have h64 : 2 ^ 6 ∣ Nat.card ↥(fixedSubgroup (MulAut.conj s)) := by
      rcases SeitzReduction.SporadicRefine.he_inner_fixedSubgroup_cases e s hs with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
      · rw [Nat.card_congr φ.toEquiv, Sporadic.SmallOddCore.card_heInnerGrp0]
        norm_num
      · rw [Nat.card_congr φ.toEquiv, Sporadic.SmallOddCore.card_heInnerGrp1]
        norm_num
    rw [hmul] at h64
    have h6 := (Nat.Coprime.pow_left 6 hcop).dvd_of_dvd_mul_right h64
    have h7 := h6.trans hdvd
    norm_num at h7
  · obtain ⟨f⟩ := nonempty_fixedSubgroup_equiv_heOuterC e hσ hin
    haveI : (N.map f.toMonoidHom).Normal := Subgroup.Normal.map inferInstance _ f.surjective
    have hcard : Nat.card (N.map f.toMonoidHom) = Nat.card N :=
      Subgroup.card_map_of_injective f.injective
    have h3 : Nat.card N ∣ 3 := by
      rw [← hcard]
      exact card_dvd_three_of_odd_normal_heOuterC _ (hcard ▸ hodd)
    have hF : Nat.card ↥(fixedSubgroup σ) = 15120 :=
      SeitzReduction.SporadicRefine.he_outer_card_fixedSubgroup e hσ hin
    have h7 : 7 ∣ Nat.card (↥(fixedSubgroup σ) ⧸ N) * Nat.card N := by
      rw [← hmul, hF]
      norm_num
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).1 h7 with h | h
    · have := h.trans hdvd
      norm_num at this
    · have := h.trans h3
      norm_num at this

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
