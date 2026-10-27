module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Split
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.LinHighCover
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.LinModelAutRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem n_sub_two_le_pRank_of_model {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n r f p : ℕ}
    (hm : StatedClassicalModel X t n r f) (ht : t = .PSL ∨ t = .PSU) (hn : 2 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpg : p ∣ diagGcd t n r f) :
    n - 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  have : Fact p.Prime := ⟨hp⟩
  rcases ht with rfl | rfl
  · obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hm
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    exact (CFSG.SectionRank.OddCover.scalar_quotient_diagonal_torus_rank (K := K) hadm.1 hn
      (r := p) hp2 (H := StatedSL n K)
      (.inl ⟨hK, rfl, (hpg.trans (Nat.gcd_dvd_right _ _) : p ∣ r ^ f - 1)⟩)
      ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) le_rfl).1
  · obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hm
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    exact (CFSG.SectionRank.OddCover.scalar_quotient_diagonal_torus_rank (K := K) hadm.1 hn
      (r := p) hp2 (H := StatedSU n (r ^ f) K)
      (.inr ⟨hK, rfl, (hpg.trans (Nat.gcd_dvd_right _ _) : p ∣ r ^ f + 1)⟩)
      ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (r ^ f) K)) le_rfl).1

theorem t1bLieHardAt_lin_aux (hGA : CFSG.Open.GriessAllModelsStatement) {t : StatedLieTag}
    (ht : t = .PSL ∨ t = .PSU) {L : Type} [Group L] [Finite L] (hLC : LieCentralQuotient L)
    (hq : CFSG.Open.IsQuasisimple L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcond : CFSG.Open.pRank p (⊤ : Subgroup L) < 7 ∨ p ∣ Nat.card (Subgroup.center L))
    {n r f : ℕ} (hm : CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) t n r f)
    (hn : 3 ≤ n) (hpg : p ∣ diagGcd t n r f) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut L)) ≤ CFSG.Open.pRank p (⊤ : Subgroup L) + 1 := by
  have hcl : StatedClassicalModel (L ⧸ Subgroup.center L) t n r f := classical_of_lieModel hm ht
  have hcen := center_centerQuotient_eq_bot hq
  have hA := pRank_mulAut_le_mulAut_centerQuotient hq.1 hp (L := L)
  have hS2 : n - 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L)) :=
    n_sub_two_le_pRank_of_model hcl ht (by omega) hp hp2 hpg
  have hex : ∃ n r f : ℕ,
      (CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .PSL n r f ∧
        p ∣ Nat.gcd n (r ^ f - 1)) ∨
      (CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .PSU n r f ∧
        p ∣ Nat.gcd n (r ^ f + 1)) := by
    rcases ht with rfl | rfl
    · exact ⟨n, r, f, Or.inl ⟨hm, hpg⟩⟩
    · exact ⟨n, r, f, Or.inr ⟨hm, hpg⟩⟩
  have hperf : Group.IsPerfect L := ⟨hq.1⟩
  by_cases hg2 : p ^ 2 ∣ diagGcd t n r f
  · have hpn : p ^ 2 ∣ n := by
      rcases ht with rfl | rfl
      · exact hg2.trans (Nat.gcd_dvd_left _ _)
      · exact hg2.trans (Nat.gcd_dvd_left _ _)
    have hn9 : 9 ≤ n := by
      have h1 := Nat.le_of_dvd (by omega) hpn
      have h3 : 3 ≤ p := by
        have := hp.two_le
        omega
      nlinarith
    by_cases hZ : p ∣ Nat.card (Subgroup.center L)
    · have ha : p ∣ (genericOrders t n r f).1 := by
        rcases ht with rfl | rfl <;> exact hpg
      obtain ⟨-, h2⟩ := lieCoverRankHighLin_aux hGA hperf hp hp2 hZ (by omega) hm ht ha
      have h3 := pRank_mulAut_le_of_model hcl ht hn hp hp2 hpg
      omega
    · exfalso
      have h7 : CFSG.Open.pRank p (⊤ : Subgroup L) < 7 := hcond.resolve_right hZ
      have := pRank_centerQuotient_le_of_not_dvd hp hZ
      omega
  · have h1 := pRank_mulAut_le_succ_of_model hcl ht hn hp hp2 hpg hg2 hcen
    have hSL : CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤
        CFSG.Open.pRank p (⊤ : Subgroup L) := by
      by_cases hZ : p ∣ Nat.card (Subgroup.center L)
      · by_cases h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L))
        · exact lieCoverRankHighLin hGA L hq hLC p hp hp2 hZ h3 hex
        · have : Fact p.Prime := ⟨hp⟩
          have hpL : p ∣ Nat.card L := hZ.trans (Subgroup.card_subgroup_dvd_card _)
          have h2 := (CFSG.SectionRank.perfect_cyclic_center_odd_elements (L := L) hp2 hpL).2 hZ
          rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
          omega
      · exact pRank_centerQuotient_le_of_not_dvd hp hZ
    omega

theorem t1bLieHardAt_PSL (hGA : CFSG.Open.GriessAllModelsStatement) : T1bLieHardAt .PSL := by
  intro L _ _ hLC hq _ p hp hp2 hcond ⟨n, r, f, hm, hE⟩
  obtain ⟨-, hn, hpg⟩ := psl_facts_of_lieModel_of_not_easy hm hE
  exact t1bLieHardAt_lin_aux hGA (Or.inl rfl) hLC hq hp hp2 hcond hm hn hpg

theorem t1bLieHardAt_PSU (hGA : CFSG.Open.GriessAllModelsStatement) : T1bLieHardAt .PSU := by
  intro L _ _ hLC hq _ p hp hp2 hcond ⟨n, r, f, hm, hE⟩
  obtain ⟨hn, -, hpg⟩ := psu_facts_of_lieModel_of_not_easy hm hE
  exact t1bLieHardAt_lin_aux hGA (Or.inr rfl) hLC hq hp hp2 hcond hm hn hpg

theorem t1bLieHardAt_psl_psu (hGA : CFSG.Open.GriessAllModelsStatement) :
    T1bLieHardAt .PSL ∧ T1bLieHardAt .PSU :=
  ⟨t1bLieHardAt_PSL hGA, t1bLieHardAt_PSU hGA⟩

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
