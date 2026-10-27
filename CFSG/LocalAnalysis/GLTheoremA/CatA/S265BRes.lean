module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BFour

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def tyUnTwo (n : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedA r q => r + 1 = n ∧ q.card = 2 | _ => False

@[expose] def QUBRank : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x b : Ω) (n : ℕ), QUNL 3 S B T x b →
    5 ≤ n → n ≤ 9 → catalogIs (PSimple 3 (Ipart 3 S b)) (tyUnTwo n) →
    (3 ^ n ≤ 3 * Nat.card B ∧ (¬ 3 ∣ n → 3 ^ n ≤ Nat.card B)) ∧
      ∃ E : Subgroup Ω, IsElemAbelian 3 E ∧ 3 ^ 6 ≤ Nat.card E

@[expose] def QSBRank : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω) (n : ℕ),
    QSNL 3 S B T x D K → 5 ≤ n → n ≤ 9 → catalogIs (PSimple 3 K) (tyUnTwo n) →
    (3 ^ n ≤ 3 * Nat.card B ∧ (¬ 3 ∣ n → 3 ^ n ≤ Nat.card B)) ∧
      ∃ E : Subgroup Ω, IsElemAbelian 3 E ∧ 3 ^ 6 ≤ Nat.card E

@[expose] def QUBBig : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x b : Ω) (n : ℕ), QUNL 3 S B T x b →
    5 ≤ n → n ≤ 9 → catalogIs (PSimple 3 (Ipart 3 S b)) (tyUnTwo n) →
    3 ^ n ≤ 3 * Nat.card B → 3 ^ 6 ≤ Nat.card B → QUConcl 3 S B x b

@[expose] def QSBBig : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω) (n : ℕ),
    QSNL 3 S B T x D K → 5 ≤ n → n ≤ 9 → catalogIs (PSimple 3 K) (tyUnTwo n) →
    3 ^ n ≤ 3 * Nat.card B → 3 ^ 6 ≤ Nat.card B → QSConcl 3 S B D K

@[expose] def QUBRes : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x b : Ω), QUNL 3 S B T x b →
    (catalogIs (PSimple 3 (Ipart 3 S b)) S9.isU5two ∨
      catalogIs (PSimple 3 (Ipart 3 S b)) S9.isU6two) →
    Nat.card B = 3 ^ 5 → (⁅T, B⁆ : Subgroup Ω) ≠ ⊥ → QUConcl 3 S B x b

@[expose] def QSBRes : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω),
    QSNL 3 S B T x D K →
    (catalogIs (PSimple 3 K) S9.isU5two ∨ catalogIs (PSimple 3 K) S9.isU6two) →
    Nat.card B = 3 ^ 5 → (⁅T, B⁆ : Subgroup Ω) ≠ ⊥ → QSConcl 3 S B D K

private theorem exists_tyUnTwo {G : Type} [Group G] (h : catalogIs G tyUnHigh) :
    ∃ n, 5 ≤ n ∧ n ≤ 9 ∧ catalogIs G (tyUnTwo n) := by
  obtain ⟨i, hi, e⟩ := h
  cases i with
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedA r q =>
      obtain ⟨h4, h8, h2⟩ : 4 ≤ r ∧ r ≤ 8 ∧ q.card = 2 := hi
      exact ⟨r + 1, by omega, by omega, .lie ⟨.twistedA r q, hv⟩,
        (⟨rfl, h2⟩ : r + 1 = r + 1 ∧ q.card = 2), e⟩
    | _ => exact hi.elim
  | _ => exact hi.elim

private theorem low_of_tyUnTwo {G : Type} [Group G] {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≤ 6)
    (h : catalogIs G (tyUnTwo n)) : catalogIs G S9.isU5two ∨ catalogIs G S9.isU6two := by
  obtain ⟨i, hi, e⟩ := h
  cases i with
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedA r q =>
      obtain ⟨hr, h2⟩ : r + 1 = n ∧ q.card = 2 := hi
      rcases (by omega : r = 4 ∨ r = 5) with rfl | rfl
      · exact Or.inl ⟨.lie ⟨.twistedA 4 q, hv⟩, h2, e⟩
      · exact Or.inr ⟨.lie ⟨.twistedA 5 q, hv⟩, h2, e⟩
    | _ => exact hi.elim
  | _ => exact hi.elim

private theorem card_eq_three_pow {Ω : Type} [Group Ω] [Finite Ω] {B : Subgroup Ω}
    (hB : IsElemAbelian 3 B) : ∃ k, Nat.card B = 3 ^ k := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 B := fun g => ⟨1, Subtype.ext (by simpa using hB.2 g g.2)⟩
  exact IsPGroup.iff_card.1 hP

private theorem res_arith {n k : ℕ} (hn5 : 5 ≤ n) (hn9 : n ≤ 9)
    (h1 : 3 ^ n ≤ 3 * 3 ^ k) (h2 : ¬ 3 ∣ n → 3 ^ n ≤ 3 ^ k) (h6 : 3 ^ k < 3 ^ 6) :
    n ≤ 6 ∧ k = 5 := by
  have hk : k < 6 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h6
  have h1' : 3 ^ n ≤ 3 ^ (k + 1) := by rw [pow_succ]; omega
  have hnk : n ≤ k + 1 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h1'
  refine ⟨by omega, ?_⟩
  rcases (by omega : n = 5 ∨ n = 6) with rfl | rfl
  · have := (Nat.pow_le_pow_iff_right (by norm_num)).1 (h2 (by norm_num))
    omega
  · omega

theorem quFamBHigh_of_parts (h2 : QUBRank) (h3 : QUBBig) (hR : QUBRes) : QUFamBHigh := by
  intro p Ω _ _ S B T x b hN hp hcat
  subst hp
  obtain ⟨n, hn5, hn9, hn⟩ := exists_tyUnTwo hcat
  obtain ⟨⟨hr1, hr2⟩, E, hE, hE6⟩ := h2 Ω S B T x b n hN hn5 hn9 hn
  by_cases hB6 : 3 ^ 6 ≤ Nat.card B
  · exact h3 Ω S B T x b n hN hn5 hn9 hn hr1 hB6
  obtain ⟨k, hk⟩ := card_eq_three_pow hN.cfg.elem
  rw [hk] at hr1 hr2 hB6
  obtain ⟨hn6, rfl⟩ := res_arith hn5 hn9 hr1 hr2 (Nat.lt_of_not_le hB6)
  refine hR Ω S B T x b hN (low_of_tyUnTwo hn5 hn6 hn) hk ?_
  rcases hN.cfg.maxc with hc | hc
  · exact hc
  · exact absurd ((hc E hE).trans_lt (hk ▸ Nat.lt_of_not_le hB6)) (not_lt.2 hE6)

theorem qsFamBHigh_of_parts (h2 : QSBRank) (h3 : QSBBig) (hR : QSBRes) : QSFamBHigh := by
  intro p Ω _ _ S B T x D K hN hp hcat
  subst hp
  obtain ⟨n, hn5, hn9, hn⟩ := exists_tyUnTwo hcat
  obtain ⟨⟨hr1, hr2⟩, E, hE, hE6⟩ := h2 Ω S B T x D K n hN hn5 hn9 hn
  by_cases hB6 : 3 ^ 6 ≤ Nat.card B
  · exact h3 Ω S B T x D K n hN hn5 hn9 hn hr1 hB6
  obtain ⟨k, hk⟩ := card_eq_three_pow hN.cfg.elem
  rw [hk] at hr1 hr2 hB6
  obtain ⟨hn6, rfl⟩ := res_arith hn5 hn9 hr1 hr2 (Nat.lt_of_not_le hB6)
  refine hR Ω S B T x D K hN (low_of_tyUnTwo hn5 hn6 hn) hk ?_
  rcases hN.cfg.maxc with hc | hc
  · exact hc
  · exact absurd ((hc.1 E hE).trans_lt (hk ▸ Nat.lt_of_not_le hB6)) (not_lt.2 hE6)

end CFSG.LocalAnalysis.GLTheoremA.S265

end
