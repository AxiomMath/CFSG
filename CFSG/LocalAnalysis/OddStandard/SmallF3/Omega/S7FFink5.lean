module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FFinkStd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FFinkConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Fink5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.General

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 (exists_full_conj_centralized
  normal_of_forall_odd_inf)
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25 odd_inf_of_lemma25)

theorem asc82Fink5_of_inputs (h36 : Asc82Lemma36) (hP34 : Asc82PocketExists)
    (h34c : Asc82Lemma34c) (h71 : Asc82Lemma71) (h33F : Asc82Lemma33F) (hP : Asc82Tab6P)
    (h25 : Asc76Lemma25) : Asc82Fink5 := by
  intro G _ _ t L S z hctx x hx hx4
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := hctx.toSec3SettingLB
  haveI := hS.simple
  have hLC : InCStar L := h71 G t L hS hctx.omega6
  have hLstd := s7f_isStandard_L h36 hP34 h34c hS hLC
  have hcyc := h33F G t L hS L hLC hS.inF
  have hxC : x ∈ centralizer (L : Set G) := (mem_inf.mp hx).2
  have htC := hctx.t_mem_centralizer
  have hxp : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx4]; norm_num)
  have hxp' : IsPGroup 2 (zpowers (⟨x, hxC⟩ : ↥(centralizer (L : Set G)))) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx4]; norm_num)
  obtain ⟨S₀, hS₀⟩ := hxp'.exists_le_sylow
  have h4dvd : 4 ∣ Nat.card S₀ := by
    have hmem : (⟨x, hxC⟩ : ↥(centralizer (L : Set G))) ∈
        (S₀ : Subgroup ↥(centralizer (L : Set G))) := hS₀ (mem_zpowers _)
    have hdvd := Subgroup.orderOf_dvd_natCard (S₀ : Subgroup ↥(centralizer (L : Set G))) hmem
    rwa [Subgroup.orderOf_mk, hx4] at hdvd
  have h4 : 4 ≤ Nat.card S₀ := Nat.le_of_dvd Nat.card_pos h4dvd
  have hO := s7f_assemblyOddCore_eq_bot hS.involution
  have hnot := s7f_not_normal hLstd htC hS.involution
  have hLX : ¬ L.Normal → ∀ y ∈ centralizer (L : Set G), orderOf y = 2 →
      L ≤ normalClosure ({y} : Set G) := fun _ y _ hy =>
    s7f_le_normalClosure L fun h => by
      rw [h, orderOf_one] at hy
      omega
  by_cases hall : ∀ g : G, g ∉ normalizer (L : Set G) → ∀ P : Subgroup G,
      P ≤ (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ⊓ normalizer (L : Set G) →
        IsPGroup 2 P → Nat.card P ≤ 2
  · exact absurd (normal_of_forall_odd_inf hLstd hO S₀ (hcyc S₀)
      (odd_inf_of_lemma25 hO hLstd S₀ (hcyc S₀) h4 (s7f_three_le_twoRank_L hP hctx.isOm6P) h25
        hLX hall)) hnot
  · push Not at hall
    obtain ⟨g, hg, P, hP', hP2, hPcard⟩ := hall
    have hP4 : 4 ≤ Nat.card P := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP2
      rw [hn] at hPcard ⊢
      have hn2 : 2 ≤ n := by
        by_contra h
        have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    obtain ⟨g', hg', R, T, hRC, -, hRcard, hTg, -, -, hTcard, hRT⟩ :=
      exists_full_conj_centralized hLstd S₀ (hcyc S₀) hg (hP'.trans inf_le_left)
        (hP'.trans inf_le_right) hP2 hP4
    exact s7f_exists_conj_commute hLstd hcyc htC hS.involution hxC hxp hg' hRC
      (hRcard.trans (Sylow.card_eq_multiplicity S₀)) hTg
      (hTcard ▸ (dvd_trans (by norm_num) h4dvd)) hRT

end CFSG.OddStandard.SmallF3.Omega
