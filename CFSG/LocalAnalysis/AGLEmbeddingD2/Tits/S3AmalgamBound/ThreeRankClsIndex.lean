module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankClsRot
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankClsUnitary
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LieType.SeitzGeneration.ThreeIndepOrth
public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.SectionRank TauCeti CFSG.LieType.SeitzGeneration
  CFSG.Models Matrix

section Helpers

theorem two_le_pRank_of_char_three {S : Type} [Group S] [Finite S] {t : StatedLieTag} {n f : ℕ}
    (h : StatedClassicalModel S t n 3 f) (hf : t = .PSL → n = 2 → 2 ≤ f) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨-, hf1, hcases⟩ := classical_model_rank (by norm_num : (3 : ℕ) ≠ 2) h
  rcases hcases with ⟨ht, ⟨rfl, h1⟩ | ⟨-, h2⟩ | h3⟩ | ⟨-, ⟨-, h2⟩ | h3⟩ | ⟨-, ⟨-, h2⟩ | h3⟩ | h4
  · have := hf ht rfl
    omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

theorem two_le_pRank_of_not_rankLE2 {K : Type} [Group K] [Finite K] (h : ¬ RankLE2 3 K) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  unfold RankLE2 at h
  push Not at h
  obtain ⟨F, hF, hcard⟩ := h
  obtain ⟨E, -, hE, hEcard⟩ := exists_isElemAbelian_card_of_le (k := 2) Nat.prime_three hF
    (by omega)
  exact le_pRank (by norm_num) le_top hE hEcard

theorem statedClassical_of_lieModel {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (hn : n ≠ 0) (h : LieModel G t n p f) : StatedClassicalModel G t n p f := by
  rcases h with ⟨-, h | ⟨h0, -⟩⟩
  · exact h
  · exact absurd h0 hn

theorem two_le_pRank_of_equiv {S G : Type} [Group S] [Finite S] [Group G] [Finite G]
    (e : S ≃* G) (h : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G)) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  rw [pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
  exact h

end Helpers

section Families

theorem not_three_dvd_pow {p f : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) : ¬ 3 ∣ p ^ f := fun h =>
  hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
    (Nat.prime_three.dvd_of_dvd_pow h)).symm

theorem two_le_of_admissible_PSL {n p f : ℕ} (h : StatedLieAdmissible .PSL n p f) (hn : n = 2)
    (hp3 : p = 3) : 2 ≤ f := by
  obtain ⟨-, hf, -, -, hne⟩ := h
  by_contra hlt
  have : f = 1 := by omega
  subst hn hp3 this
  exact hne rfl

theorem A_two_le_pRank_three {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.A r q).Valid)
    {S : Type} [Group S] [Finite S] (e : S ≃* Cat ⟨.A r q, hv⟩)
    (h1 : ¬ (r = 1 ∧ q.p ≠ 3)) (h2 : ¬ (r = 2 ∧ q.card % 3 = 2)) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have hq : q.card = q.p ^ q.exponent := PrimePower.card_def q
  have hmodel : StatedClassicalModel S .PSL (r + 1) q.p q.exponent :=
    statedClassical_of_lieModel (by omega) (lieModel_A r q hv e)
  by_cases hp3 : q.p = 3
  · rw [hp3] at hmodel
    exact two_le_pRank_of_char_three hmodel fun _ hn =>
      two_le_of_admissible_PSL hmodel.1 (by omega) rfl
  obtain ⟨hadm, K, _, _, hK, ⟨eK⟩⟩ := hmodel
  refine two_le_pRank_of_equiv eK ?_
  rcases (show r = 1 ∨ r = 2 ∨ 3 ≤ r by omega) with rfl | rfl | h3
  · exact absurd ⟨rfl, hp3⟩ h1
  · have hmod : q.card % 3 = 1 := by
      have := not_three_dvd_pow (f := q.exponent) q.prime_p hp3
      omega
    exact psl_three_two_le_pRank_three (by rw [hK, ← hq]; exact hmod)
  · exact psl_two_le_pRank_three (by omega)

theorem twistedA_two_le_pRank_three {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.twistedA r q).Valid) {S : Type} [Group S] [Finite S]
    (e : S ≃* Cat ⟨.twistedA r q, hv⟩) (h1 : ¬ (r = 2 ∧ q.card % 3 = 1)) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have hq : q.card = q.p ^ q.exponent := PrimePower.card_def q
  have hc : ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = q.p :=
    LieTypeIndex.characteristic_twistedA r q
  have hf : ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ = q.exponent :=
    LieTypeIndex.fieldExponent_twistedA r q
  have hmodel : StatedClassicalModel S .PSU (r + 1) q.p q.exponent := by
    have := statedClassical_of_lieModel (by omega) (lieModel_twistedA r q hv e)
    rwa [hc, hf] at this
  by_cases hp3 : q.p = 3
  · rw [hp3] at hmodel
    exact two_le_pRank_of_char_three hmodel fun h => nomatch h
  obtain ⟨hadm, K, _, _, hK, ⟨eK⟩⟩ := hmodel
  refine two_le_pRank_of_equiv eK ?_
  have hqp : (q.p ^ q.exponent) ^ 2 = q.p ^ (2 * q.exponent) := by ring
  rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | h3
  · have hmod : q.card % 3 = 2 := by
      have := not_three_dvd_pow (f := q.exponent) q.prime_p hp3
      omega
    exact psu_three_two_le_pRank_three hK (by rw [← hq]; exact hmod)
  · have : CharP K q.p := ringChar.of_eq
      (CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq (f := 2 * q.exponent) q.prime_p
        (by have := q.exponent_pos; omega) (by rw [hK, hqp]))
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    exact psu_two_le_pRank_three_of_four_le hK q.exponent_pos hp3 (by omega)

theorem B_two_le_pRank_three {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.B r q).Valid)
    {S : Type} [Group S] [Finite S] (e : S ≃* Cat ⟨.B r q, hv⟩) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  have : Finite (Cat ⟨.B r q, hv⟩) := Finite.of_equiv S e.toEquiv
  rcases lieModel_B r q hv e with hm | hm
  · have hmodel := statedClassical_of_lieModel (by
      have := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
      omega) hm
    obtain ⟨⟨-, -, hn, -⟩, K, _, _, hK, ⟨eK⟩⟩ := hmodel
    exact two_le_pRank_of_equiv eK (psp_two_le_pRank_three hn)
  · have hmodel := statedClassical_of_lieModel (by
      have := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
      omega) hm
    obtain ⟨⟨-, -, hn, hp2⟩, -⟩ := hmodel
    exact two_le_pRank_of_equiv e (two_le_pRank_of_not_rankLE2
      (not_rankLE2_orthogonal_three ⟨.B r q, hv⟩ (Or.inl ⟨r, q, rfl, hn, hp2⟩)))

theorem C_two_le_pRank_three {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.C r q).Valid)
    {S : Type} [Group S] [Finite S] (e : S ≃* Cat ⟨.C r q, hv⟩) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  have hmodel := statedClassical_of_lieModel (by
    have := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
    omega) (lieModel_C r q hv e)
  obtain ⟨⟨-, -, hn, -⟩, K, _, _, hK, ⟨eK⟩⟩ := hmodel
  exact two_le_pRank_of_equiv eK (psp_two_le_pRank_three hn)

theorem D_two_le_pRank_three {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.D r q).Valid)
    {S : Type} [Group S] [Finite S] (e : S ≃* Cat ⟨.D r q, hv⟩) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) :=
  haveI : Finite (Cat ⟨.D r q, hv⟩) := Finite.of_equiv S e.toEquiv
  two_le_pRank_of_equiv e (two_le_pRank_of_not_rankLE2
    (not_rankLE2_orthogonal_three ⟨.D r q, hv⟩ (Or.inr (Or.inl ⟨r, q, rfl⟩))))

theorem twistedD_two_le_pRank_three {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.twistedD r q).Valid) {S : Type} [Group S] [Finite S]
    (e : S ≃* Cat ⟨.twistedD r q, hv⟩) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) :=
  haveI : Finite (Cat ⟨.twistedD r q, hv⟩) := Finite.of_equiv S e.toEquiv
  two_le_pRank_of_equiv e (two_le_pRank_of_not_rankLE2
    (not_rankLE2_orthogonal_three ⟨.twistedD r q, hv⟩ (Or.inr (Or.inr ⟨r, q, rfl⟩))))

end Families

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls
