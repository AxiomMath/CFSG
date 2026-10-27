module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Center
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.AutTransfer
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.AutSix
public import CFSG.LocalAnalysis.AGLEmbedding.AltBetaRank
public import CFSG.LocalAnalysis.SectionRank.CyclicCenter
public import CFSG.Quasithin.H13.A7SectionRank
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Alt

open Equiv

section Center

variable {L : Type} [Group L] [Finite L] [Group.IsPerfect L] {n : ℕ}

theorem pRank_center_le_one (hn : 5 ≤ n) (e : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin n))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : CFSG.Open.pRank p (Subgroup.center L) ≤ 1 := by
  obtain ⟨E, hEZ, -, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (Subgroup.center L)
  have hd : p ^ CFSG.Open.pRank p (Subgroup.center L) ∣ Nat.card (Subgroup.center L) := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hEZ
  have := (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hd
  exact this.trans (center_facts hn e hp hp2).1

omit [Group.IsPerfect L] in
theorem dvd_of_pos_pRank_center {p : ℕ} (hp : p.Prime)
    (h : 1 ≤ CFSG.Open.pRank p (Subgroup.center L)) :
    p ∣ Nat.card (Subgroup.center L) := by
  obtain ⟨E, hEZ, -, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (Subgroup.center L)
  have hd : p ^ CFSG.Open.pRank p (Subgroup.center L) ∣ Nat.card (Subgroup.center L) := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hEZ
  exact (dvd_pow_self p (by omega)).trans hd

end Center

theorem pRank_top_le_of_not_dvd {G : Type*} [Group G] [Finite G] {p k : ℕ} (hp : 1 < p)
    (h : ¬ p ^ (k + 1) ∣ Nat.card G) : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ k := by
  by_contra hk
  push Not at hk
  obtain ⟨E, -, -, hcard⟩ := CFSG.SectionRank.exists_pRank hp (⊤ : Subgroup G)
  apply h
  refine (pow_dvd_pow p hk).trans ?_
  rw [← hcard]
  exact Subgroup.card_subgroup_dvd_card E

theorem card_mulAut_alternating_six_dvd :
    Nat.card (MulAut (alternatingGroup (Fin 6))) ∣ 1440 := by
  obtain ⟨hfin, hle⟩ :=
    Balance.Alt.finite_and_card_mulAut_alternatingGroup_six_le
  have hpos : 0 < Nat.card (MulAut (alternatingGroup (Fin 6))) := Nat.card_pos
  have hinj := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num)
  have h720 : 720 ∣ Nat.card (MulAut (alternatingGroup (Fin 6))) := by
    have h := Subgroup.card_subgroup_dvd_card
      (MonoidHom.range (MulAut.conjNormal (H := alternatingGroup (Fin 6))))
    rwa [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_eq_fintype_card,
      Fintype.card_perm, Fintype.card_fin, show Nat.factorial 6 = 720 by decide] at h
  obtain ⟨k, hk⟩ := h720
  have hk' : k = 1 ∨ k = 2 := by omega
  rcases hk' with rfl | rfl
  · exact ⟨2, by omega⟩
  · exact ⟨1, by omega⟩

theorem pRank_mulAut_alternating_six_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut (alternatingGroup (Fin 6)))) ≤ 6 / p := by
  have := Balance.Alt.finite_and_card_mulAut_alternatingGroup_six_le.1
  have hd := card_mulAut_alternating_six_dvd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  refine pRank_top_le_of_not_dvd hp.one_lt fun h => ?_
  have h1 := h.trans hd
  by_cases h3 : p = 3
  · subst h3
    norm_num at h1
  · by_cases h5 : p = 5
    · subst h5
      norm_num at h1
    · have hp7 : 7 ≤ p := by
        by_contra hc
        push Not at hc
        interval_cases p <;> first | omega | exact absurd hp (by norm_num)
      have h6 : 6 / p = 0 := Nat.div_eq_of_lt (by omega)
      rw [h6, zero_add, pow_one] at h1
      have h2 : p ∣ 2 ^ 5 * 3 ^ 2 * 5 := h1
      rcases (Nat.Prime.dvd_mul hp).1 h2 with h4 | h4
      · rcases (Nat.Prime.dvd_mul hp).1 h4 with h4 | h4
        · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h4)
          omega
        · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h4)
          omega
      · have := Nat.le_of_dvd (by norm_num) h4
        omega

section Aut

variable {L : Type} [Group L] [Finite L] [Group.IsPerfect L] {n : ℕ}

theorem pRank_aut_le (hn : 5 ≤ n) (e : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin n))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut L)) ≤ n / p := by
  have hinj : Function.Injective (Balance.Alt.autCenterQuot L) :=
    Balance.Alt.autCenterQuot_injective L
  by_cases hn6 : n = 6
  · subst hn6
    have := Balance.Alt.finite_and_card_mulAut_alternatingGroup_six_le.1
    have hinj' : Function.Injective ((MulAut.congr e).toMonoidHom.comp
        (Balance.Alt.autCenterQuot L)) :=
      (MulAut.congr e).injective.comp hinj
    exact (CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt _ hinj').trans
      (pRank_mulAut_alternating_six_le hp hp2)
  · exact (CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt _ hinj).trans
      (CFSG.AGLEmbedding.pRank_top_mulAut_le hn hn6 e hp)

theorem le_pRank_top (hn : 5 ≤ n) (e : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin n))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : n / p ≤ CFSG.Open.pRank p (⊤ : Subgroup L) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hZ : p ∣ Nat.card (Subgroup.center L)
  · obtain ⟨rfl, hn67⟩ := (center_facts hn e hp hp2).2 hZ
    have hpL : 3 ∣ Nat.card L := hZ.trans (Subgroup.card_subgroup_dvd_card _)
    have h2 := (CFSG.SectionRank.perfect_cyclic_center_odd_elements (L := L) hp2 hpL).2 hZ
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
    omega
  · have h1 := CFSG.SectionRank.pRank_quotient_eq (Subgroup.center L) hZ
    have h2 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e
    have h3 := (CFSG.Quasithin.H13.A7.section_rank_alternating_odd_prime_rank).1 n p hp hp2
    omega

end Aut

end CFSG.HardMathSupport.Timmesfeld.Tables.Alt
