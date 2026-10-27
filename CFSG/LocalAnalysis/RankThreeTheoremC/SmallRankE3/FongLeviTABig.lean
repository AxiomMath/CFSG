module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviRankArith
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviCenter
public import CFSG.Adapters.LieModelSimple
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviOutAut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open TauCeti Subgroup CFSG.Open

theorem tABig_pRank_false {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ}
    (S : E3Setting K K₀ B z p) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (h4 : 4 ≤ CFSG.Open.pRank ℓ (⊤ : Subgroup ↥K)) : False := by
  have h1 := S.hℓ ℓ hℓ hℓ2
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup K] at h1
  omega

theorem tABig_psu_false {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ}
    (S : E3Setting K K₀ B z p) {N f : ℕ} (hN : 5 ≤ N) (hf : 1 ≤ f) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = (2 ^ f) ^ 2)
    (eF : ↥K ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU N (2 ^ f) F))
    (hmodel : CFSG.Blueprint.LieModel ↥K .PSU N 2 f) : False := by
  have hp5 : 5 ≤ p := S.hp5
  have hp : p.Prime := S.hp
  rcases Nat.even_or_odd f with hfe | hfo
  · rcases Nat.lt_or_ge f 4 with hf4 | hf4
    ·
      have hf2 : f = 2 := by
        obtain ⟨k, hk⟩ := hfe
        omega
      subst hf2
      rcases Nat.lt_or_ge N 6 with hN6 | hN6
      ·
        obtain rfl : N = 5 := by omega
        haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
        have h3 : 5 - 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥K) := by
          rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 5) eF]
          exact psu_sub_two_le_pRank_of_dvd (ℓ := 5) (n := 5) (f := 2) (F := F)
            (by norm_num) (by norm_num) hF (by norm_num)
        by_cases hp5' : p = 5
        ·
          have hKr5 : CFSG.Open.pRank 5 K ≤ 1 := by
            subst hp5'
            exact S.hKr
          rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup K] at hKr5
          omega
        ·
          have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 2 F :=
            ⟨Nat.prime_two, by norm_num, by rw [hF]; norm_num⟩
          have e' : ↥K ≃* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU 5 :=
            eF.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by norm_num)).symm
          have hOut : ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) := by
            rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv,
              (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_full_diagonal_outer_order
                hU (n := 5) (by norm_num) (by norm_num)).2.2.2.2.1]
            have hg : Nat.gcd 5 (2 ^ 2 + 1) = 5 := by norm_num
            rw [hg]
            intro hd
            rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
            · rcases (Nat.Prime.dvd_mul hp).1 h with h' | h'
              · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h'
                omega
              · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h'
                omega
            · exact hp5' ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)
          haveI : IsSimpleGroup ↥K :=
            CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hmodel
          have hZ : Subgroup.center ↥K = ⊥ :=
            center_eq_bot_of_simple_of_two_le_pRank (ℓ := 5) (by norm_num) (by omega)
          exact false_of_not_dvd_card_outer S hZ hOut
      ·
        haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
        have h4 : 4 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥K) := by
          rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 5) eF]
          exact psu_four_le_pRank_of_dvd (ℓ := 5) (n := N) (f := 2) (F := F)
            (by norm_num) hN (Or.inr hN6) hF (by norm_num)
        exact tABig_pRank_false S (ℓ := 5) (by norm_num) (by norm_num) h4
    ·
      obtain ⟨ℓ, hℓp, hℓ2, hℓ5, hℓd⟩ := exists_prime_dvd_two_pow_add_one_ne_five hfe hf4
      haveI : Fact ℓ.Prime := ⟨hℓp⟩
      have h4 : 4 ≤ CFSG.Open.pRank ℓ (⊤ : Subgroup ↥K) := by
        rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hℓp.one_lt eF]
        exact psu_four_le_pRank_of_dvd (ℓ := ℓ) (n := N) (f := f) (F := F) hℓ2 hN (Or.inl hℓ5)
          hF hℓd
      exact tABig_pRank_false S hℓp hℓ2 h4
  ·
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) := by
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) eF]
      exact psu_four_le_pRank_of_dvd (ℓ := 3) (n := N) (f := f) (F := F) (by norm_num)
        hN (Or.inl (by norm_num)) hF (three_dvd_two_pow_add_one hfo)
    exact tABig_pRank_false S (ℓ := 3) Nat.prime_three (by norm_num) h4

theorem tABig_false {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ}
    (S : E3Setting K K₀ B z p) {n : ℕ} (hn : 4 ≤ n) {q : PrimePower} (hq2 : q.p = 2)
    (hv : (LieTypeIndex.twistedA n q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.twistedA n q, hv⟩)) : False := by
  obtain ⟨e⟩ := e
  have hmodel0 := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA n q hv e
  rw [hq2] at hmodel0
  have hmodel : CFSG.Blueprint.LieModel ↥K .PSU (n + 1) 2 q.exponent :=
    Or.inl ⟨by decide, hmodel0⟩
  obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := hmodel0
  have hf : 1 ≤ q.exponent := by
    have := q.exponent_pos
    omega
  exact tABig_psu_false S (N := n + 1) (f := q.exponent) (by omega) hf hF eF hmodel

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
