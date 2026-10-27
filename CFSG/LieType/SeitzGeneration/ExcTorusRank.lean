module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.RegimesOuterNarrow

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.PreuniquenessRankFour.Helpers

theorem SylowTorus.rankLE1 {G : Type*} [Group G] {p : ℕ} (h : SylowTorus G p 1) (hp : p.Prime) :
    RankLE1 p G := fun F hF => by simpa using h.rank_le hp hF

theorem not_rankLE2_of_elemAbelian {G : Type*} [Group G] {p m : ℕ} (hp : p.Prime) (hm : 3 ≤ m)
    {E : Subgroup G} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ m) : ¬ RankLE2 p G := by
  intro hr
  have h1 := hr E hE
  rw [hcard] at h1
  have h2 : p ^ 3 ≤ p ^ m := Nat.pow_le_pow_right hp.pos hm
  have h3 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

@[expose] def degreesW : Tag → List ℕ
  | .F4 => [2, 6, 8, 12]
  | τ => degreesE τ

@[expose] def degCount (τ : Tag) (e : ℕ) : ℕ := ((degreesW τ).filter fun d => e ∣ d).length

theorem le_thirty_of_degCount_pos {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {e : ℕ} (h : 0 < degCount τ e) : e ≤ 30 := by
  obtain ⟨d, hd⟩ := List.exists_mem_of_length_pos h
  rw [List.mem_filter] at hd
  have hb : ∀ d ∈ degreesW τ, 0 < d ∧ d ≤ 30 := by
    rcases hτ with rfl | rfl | rfl | rfl <;> decide
  have hdvd : e ∣ d := by simpa using hd.2
  exact (Nat.le_of_dvd (hb d hd.1).1 hdvd).trans (hb d hd.1).2

theorem elemAbelian_card_eq_one_of_ordProj {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (h : p ^ (Nat.card G).factorization p = 1) {F : Subgroup G}
    (hF : IsElemAbelian p F) : Nat.card F = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h0 : (Nat.card G).factorization p = 0 := by
    rcases Nat.eq_zero_or_pos ((Nat.card G).factorization p) with h0 | h0
    · exact h0
    · exact absurd h (by
        have := Nat.one_lt_pow h0.ne' hp.one_lt
        omega)
  have hnd : ¬ p ∣ Nat.card G := by
    intro hd
    have hpos : 0 < Nat.card G := Nat.card_pos
    exact (Nat.Prime.factorization_pos_of_dvd hp hpos.ne' hd).ne' h0
  obtain ⟨n, hn⟩ := (isPGroup_of_isElemAbelian hF).exists_card_eq
  have hnn : n = 0 := by
    by_contra hn0
    apply hnd
    have : p ∣ Nat.card F := by rw [hn]; exact dvd_pow_self p hn0
    exact this.trans (Subgroup.card_subgroup_dvd_card F)
  rw [hn, hnn, pow_zero]

section Order


theorem elemAbelian_card_eq_one_of_degCount_zero {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ Nat.card K) {e : ℕ}
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e) (h0 : degCount τ e = 0)
    {F : Subgroup (adjointGroup τ K)} (hF : IsElemAbelian p F) : Nat.card F = 1 := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hnil : ((degreesE τ).filter fun d => e ∣ d).length = 0 := by
    rcases hτ with rfl | rfl | rfl <;> simpa [degCount, degreesW] using h0
  refine elemAbelian_card_eq_one_of_ordProj hp ?_ hF
  have hD : ∀ d ∈ degreesE τ, e ∣ d → d ≠ 0 ∧ ¬ p ∣ d / e := by
    intro d hd hed
    exfalso
    have hmem : d ∈ (degreesE τ).filter (fun d => e ∣ d) :=
      List.mem_filter.2 ⟨hd, by simpa using hed⟩
    have := List.length_pos_of_mem hmem
    omega
  rw [ordProj_card_adjointGroup_E hτ hp hp3 hpq, prod_ordProj_pow_sub_one hp (by omega) hpq hq2
    he (degreesE τ) hD, hnil, pow_zero]

end Order

end CFSG.LieType.SeitzGeneration
