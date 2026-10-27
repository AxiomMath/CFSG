module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3L3Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3L3Ar
import CFSG.Adapters.TauCetiLieModels
import CFSG.LieType.SeitzGeneration.ExcCatModels
public import CFSG.GH74.L5U5.Models

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I137C3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti
  CFSG.HardMathSupport.Solomon.Coordinator.I1420

section Simple


private theorem l3_finite_isSimpleGroup_of_lieModel {G : Type} [Group G] {t : StatedLieTag}
    {n p f : ℕ} (hn : n ≠ 0) (h : CFSG.Models.LieModel G t n p f) :
    Finite G ∧ IsSimpleGroup G := by
  have hm : StatedClassicalModel G t n p f := h.2.resolve_right fun h' => hn h'.1
  obtain ⟨hfin, -, hs⟩ := CFSG.LieType.Simplicity.fam_classical_converse G ⟨t, n, p, f, hm⟩
  exact ⟨hfin, hs⟩

theorem l3_list93_finite_simple {Q₀ : Type} [Group Q₀] (h : catalogIs Q₀ (S9.isList93 3)) :
    Finite Q₀ ∧ IsSimpleGroup Q₀ := by
  obtain ⟨⟨d, hv⟩, ⟨e⟩, hshape⟩ := list93three_cases h
  rcases hshape with ⟨q, hd, hq⟩ | ⟨q, hd, hq⟩ | ⟨q, hd, hq⟩ | ⟨q, hd, hq⟩ | ⟨q, hd, hq⟩ |
    ⟨q, hd, hq⟩ | hd | ⟨q, hd, hq, -⟩ | ⟨q, hd, hq, -⟩
  ·
    dsimp only at hd
    subst hd
    exact l3_finite_isSimpleGroup_of_lieModel (by norm_num) (CFSG.Models.lieModel_D 4 q hv e)
  ·
    dsimp only at hd
    subst hd
    rcases CFSG.Models.lieModel_B 2 q hv e with hm | hm <;>
      exact l3_finite_isSimpleGroup_of_lieModel (by norm_num) hm
  ·
    dsimp only at hd
    subst hd
    obtain ⟨hf, hs⟩ := CFSG.LieType.SeitzGeneration.finite_isSimpleGroup_cat_G2 hv
    exact ⟨Finite.of_equiv _ e.symm.toEquiv, (MulEquiv.isSimpleGroup_congr e).2 hs⟩
  ·
    dsimp only at hd
    subst hd
    exact l3_finite_isSimpleGroup_of_lieModel (by norm_num)
      (CFSG.Models.lieModel_twistedA 3 q hv e)
  ·
    dsimp only at hd
    subst hd
    exact l3_finite_isSimpleGroup_of_lieModel (by norm_num)
      (CFSG.Models.lieModel_twistedA 5 q hv e)
  ·
    dsimp only at hd
    subst hd
    obtain ⟨hf, hs⟩ := CFSG.LieType.SeitzGeneration.finite_isSimpleGroup_cat_trialityD4 hv
    exact ⟨Finite.of_equiv _ e.symm.toEquiv, (MulEquiv.isSimpleGroup_congr e).2 hs⟩
  ·
    dsimp only at hd
    subst hd
    obtain ⟨hf, hs⟩ := CFSG.LieType.SeitzGeneration.finite_isSimpleGroup_cat_reeF4 hv
    exact ⟨Finite.of_equiv _ e.symm.toEquiv, (MulEquiv.isSimpleGroup_congr e).2 hs⟩
  ·
    dsimp only at hd
    subst hd
    exact l3_finite_isSimpleGroup_of_lieModel (by norm_num) (CFSG.Models.lieModel_A 2 q hv e)
  ·
    dsimp only at hd
    subst hd
    exact l3_finite_isSimpleGroup_of_lieModel (by norm_num)
      (CFSG.Models.lieModel_twistedA 2 q hv e)

end Simple

section Orders


theorem l3_false_of_card_psl2 {Q₀ : Type} [Group Q₀] [Finite Q₀]
    (h : catalogIs Q₀ (S9.isList93 3))
    (hQ : Nat.card Q₀ = 60 ∨ ∃ m : ℕ, 2 ≤ m ∧ Nat.card Q₀ = 2 ^ m * (4 ^ m - 1)) : False := by
  rcases hQ with h60 | ⟨m, hm, hcard⟩
  · have h64 := two_pow_six_dvd_card_list93three h
    rw [h60] at h64
    omega
  · rcases card_list93three h with hfix | ⟨e, he2, hev, hc, -⟩ | ⟨e, he3, hodd, hc⟩
    · exact l3_fixed_ne hfix hm hcard
    · exact l3_orderA_ne he2 hev hm (hc.symm.trans hcard)
    · exact l3_orderTwistedA_ne he3 hodd hm (hc.symm.trans hcard)

end Orders

section Main



theorem core3Group_statedProj_SL3_char_two {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn1 : 1 ≤ n) : Core3Group (StatedProj (StatedSL 3 K)) := by
  intro T A hT2 hT hA Q₀ _ ⟨f, hf⟩ hQ
  exfalso
  obtain ⟨hfin, hsimp⟩ := l3_list93_finite_simple hQ
  haveI := hfin
  haveI := hsimp
  have hcard := two_pow_six_dvd_card_list93three hQ
  have hab : ∃ a b : Q₀, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hprime := CFSG.GH74.GLS.IVK.Lifted.prime_card_of_simple_abelian hcon
    have h64 : 64 ∣ Nat.card Q₀ := hcard
    have h2 : 2 ∣ Nat.card Q₀ := (show 2 ∣ 64 by norm_num).trans h64
    have heq := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hprime).1 h2
    rw [← heq] at h64
    omega
  exact l3_false_of_card_psl2 hQ
    (l3_card_simple_section_statedProj_three (f := n) (by omega) hK hT2 hT hA hab f hf)

theorem core3Group_statedProj_SL3 {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (_hn : Even n) (hn1 : 1 ≤ n) :
    Core3Group (StatedProj (StatedSL 3 K)) :=
  core3Group_statedProj_SL3_char_two hK hn1

theorem core3At_L3 :
    Core3At fun d => ∃ q : PrimePower, d = .A 2 q ∧ q.p = 2 ∧ Even q.exponent := by
  rintro ⟨d, hv⟩ ⟨q, rfl, hq, hev⟩ S _ _ ⟨e⟩
  have hm : StatedClassicalModel S .PSL 3 q.p q.exponent :=
    (CFSG.Models.lieModel_A 2 q hv e).2.resolve_right fun h => absurd h.1 (by norm_num)
  rw [hq] at hm
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hm
  exact Core3Group.of_mulEquiv e'
    (core3Group_statedProj_SL3 hK hev q.exponent_pos)

theorem core3Group_of_SL3cover (Q : Type) [Group Q] [Finite Q] (_hQ : CFSG.Open.IsQuasisimple Q)
    (h : ∃ n : ℕ, 1 ≤ n ∧ Even n ∧ FullLinearCover false 3 (2 ^ n) Q) :
    Core3Group (Q ⧸ Subgroup.center Q) := by
  obtain ⟨n, hn1, hn, K, _, _, hcov⟩ := h
  rw [if_neg Bool.false_ne_true] at hcov
  obtain ⟨hcard, ⟨e⟩⟩ := hcov
  let eQ : Q ⧸ Subgroup.center Q ≃* StatedProj (StatedSL 3 K) :=
    (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans
      (QuotientGroup.quotientMulEquivOfEq (CFSG.GH74.L5U5.center_statedSL_eq 3))
  exact Core3Group.of_mulEquiv eQ (core3Group_statedProj_SL3 hcard hn hn1)

end Main

end CFSG.LocalAnalysis.GLTheoremA.I137C3

end
