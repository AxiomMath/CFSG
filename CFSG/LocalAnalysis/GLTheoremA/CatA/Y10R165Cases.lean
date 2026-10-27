module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10F165
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Vac
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2EUp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TablesHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement


@[expose] def I165On (P : GLALabel → ℕ → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (p q : ℕ),
    HasLabel K (fun l : GLALabel => l = lab) → P lab p →
    p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    (∀ lab' : GLALabel, HasLabel K (fun l : GLALabel => l = lab') → ¬ GLASplit16 p lab') →
    ¬ p ∣ Nat.card (Subgroup.center K) →
    ∀ A : Subgroup K, IsElemAbelian p A →
      (∀ g : K, g ∈ Subgroup.centralizer (A : Set K) → orderOf g = p → g ∈ A) →
      GLATwoLocalRank p K ≤ CFSG.Open.pRank p A →
      CFSG.Open.pRank p (⊤ : Subgroup K) ≤ CFSG.Open.pRank p A →
      (⁅A, nGen A (⊤ : Subgroup K)⁆ ≠ ⊥ ∨ CFSG.Open.pRank p A + 2 ≤ evenRank K) →
      evenRank K = GLATwoLocalRank q K → CFSG.Open.pRank p A + 1 ≤ evenRank K →
      4 ≤ CFSG.Open.pRank p A + 1 →
      ∃ D E F J : Subgroup K, D ≤ E ∧ E ≤ A ∧ Nat.card D = p ∧ Nat.card E = p ^ 2 ∧
        GLAPComponent p (Subgroup.centralizer (D : Set K)) J ∧
        A ≤ Subgroup.normalizer (J : Set K) ∧
        GLAPLayer p (J ⊓ Subgroup.centralizer (E : Set K)) ≠ ⊥ ∧
        F ≤ Subgroup.centralizer (D : Set K) ∧ IsElemAbelian q F ∧
        F ≤ Subgroup.normalizer (J : Set K) ∧ 3 ≤ CFSG.Open.pRank q F

@[expose] def i165FamA (lab : GLALabel) (p : ℕ) : Prop :=
  lab.tag = .A ∧ 2 ≤ rk2Ord p lab.n ∧ 3 * rk2Ord p lab.n ≤ lab.rank + 1

@[expose] def i165FamTwA (lab : GLALabel) (p : ℕ) : Prop :=
  lab.tag = .twA ∧ rk2Ord p lab.n ≠ 2

@[expose] def i165FamBC (lab : GLALabel) (p : ℕ) : Prop :=
  (lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ rk2Ord p lab.n

@[expose] def i165FamD (lab : GLALabel) (p : ℕ) : Prop :=
  lab.tag = .D ∧ (3 ≤ rk2Ord p lab.n ∨
    (rk2Ord p lab.n = 2 ∧ Odd lab.rank ∧ 5 ≤ lab.rank))

@[expose] def i165FamTwD (lab : GLALabel) (p : ℕ) : Prop :=
  lab.tag = .twD ∧ 3 ≤ rk2Ord p lab.n

@[expose] def i165FamE6 (lab : GLALabel) (p : ℕ) : Prop :=
  lab.tag = .E6 ∧
    ((rk2Ord p lab.n = 2 ∧ 2 ≤ lab.n) ∨ (rk2Ord p lab.n = 3 ∧ 2 ≤ lab.n))

@[expose] def i165FamTwE6 (lab : GLALabel) (p : ℕ) : Prop :=
  lab.tag = .twE6 ∧ (rk2Ord p lab.n = 1 ∨ rk2Ord p lab.n = 6)

@[expose] def i165FamE7 (lab : GLALabel) (p : ℕ) : Prop :=
  lab.tag = .E7 ∧ (rk2Ord p lab.n = 3 ∨ rk2Ord p lab.n = 6)

@[expose] def i165FamE8 (lab : GLALabel) (p : ℕ) : Prop :=
  lab.tag = .E8 ∧ (rk2Ord p lab.n = 3 ∨ rk2Ord p lab.n = 4 ∨ rk2Ord p lab.n = 6)


private theorem i165FamA_of_label {K : Type} [Group K] [Finite K] {A : Subgroup K} {l n p : ℕ}
    (hK : Rk2IsLabel K ⟨.A, l, n⟩)
    (hns : ∀ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) → ¬ GLASplit16 p lab)
    (hp : p.Prime) (hp2 : p ≠ 2) (hm3 : 3 ≤ CFSG.Open.pRank p A)
    (hmax : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ CFSG.Open.pRank p A) :
    i165FamA ⟨.A, l, n⟩ p := by
  have hm0pos : 0 < rk2Ord p n := rk2Ord_pos hp hp2 n
  by_cases hm1 : rk2Ord p n = 1
  · exact (i165_false_of_split hK hns
      (rk2_split_untw (by trivial) (rk2Ord_eq_one_iff.1 hm1))).elim
  by_cases hfam : 3 * rk2Ord p n ≤ l + 1
  · have h2 : 2 ≤ rk2Ord p n := by omega
    exact ⟨rfl, h2, hfam⟩
  · exact (i165_false_of_rk2Mult_le_two hK hp hp2 (rk2Mult_A_le_two hp hp2 hm1 hfam)
      hm3 hmax).elim

private theorem i165FamTwA_of_label {K : Type} [Group K] [Finite K] {l n p : ℕ}
    (hK : Rk2IsLabel K ⟨.twA, l, n⟩)
    (hns : ∀ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) → ¬ GLASplit16 p lab)
    (hp : p.Prime) (hp2 : p ≠ 2) : i165FamTwA ⟨.twA, l, n⟩ p := by
  by_cases hm2 : rk2Ord p n = 2
  · exact (i165_false_of_split hK hns (rk2_split_tw (by simp [CFSG.Assembly.LargeEvenUntwisted])
      (by simp) (by simp) ((rk2Ord_eq_two_iff hp hp2).1 hm2))).elim
  · exact ⟨rfl, hm2⟩

private theorem i165FamB_of_label {K : Type} [Group K] [Finite K] {A : Subgroup K} {l n p : ℕ}
    (hK : Rk2IsLabel K ⟨.B, l, n⟩)
    (hns : ∀ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) → ¬ GLASplit16 p lab)
    (hTorus : I165TorusRankLower) (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center K)) (hm3 : 3 ≤ CFSG.Open.pRank p A)
    (hmax : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ CFSG.Open.pRank p A)
    (hm1 : CFSG.Open.pRank p A + 1 ≤ evenRank K) (hn1 : 1 ≤ n) :
    i165FamBC ⟨.B, l, n⟩ p := by
  have hKr : Rk2KRank := rk2KRank
  have hUp : Rk2Upper := rk2Upper_holds
  have hm0pos : 0 < rk2Ord p n := rk2Ord_pos hp hp2 n
  by_cases hm1' : rk2Ord p n = 1
  · exact (i165_false_of_split hK hns
      (rk2_split_untw (by trivial) (rk2Ord_eq_one_iff.1 hm1'))).elim
  by_cases hm3' : 3 ≤ rk2Ord p n
  · exact ⟨Or.inl rfl, hm3'⟩
  have hm2 : rk2Ord p n = 2 := by omega
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn : n = 1 := by omega
    have hp3 : p = 3 := (rk2Ord_one_eq_two_iff hp hp2).1 (by rwa [hn] at hm2)
    exact (i165_false_of_split hK hns (rk2_split_n1 hn hp3)).elim
  have hup : CFSG.Open.evenRank K ≤ l :=
    (rk2_eUpAt_of_tables hKr hUp hK).bd (Or.inl rfl) hn2
  have hlow : l ≤ CFSG.Open.pRank p (⊤ : Subgroup K) := by
    have h := hTorus K ⟨.B, l, n⟩ p hK hp hp2 hZ
      ((rk2Ord_eq_two_iff hp hp2).1 hm2) hn2 (Or.inl rfl)
    simpa [i165TorusRank] using h
  exact (i165_false_of_rank_le_pRank hp hlow hup hm3 hmax hm1).elim

private theorem i165FamC_of_label {K : Type} [Group K] [Finite K] {A : Subgroup K} {l n p : ℕ}
    (hK : Rk2IsLabel K ⟨.C, l, n⟩)
    (hns : ∀ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) → ¬ GLASplit16 p lab)
    (hTorus : I165TorusRankLower) (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center K)) (hm3 : 3 ≤ CFSG.Open.pRank p A)
    (hmax : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ CFSG.Open.pRank p A)
    (hm1 : CFSG.Open.pRank p A + 1 ≤ evenRank K) (hn1 : 1 ≤ n) :
    i165FamBC ⟨.C, l, n⟩ p := by
  have hKr : Rk2KRank := rk2KRank
  have hUp : Rk2Upper := rk2Upper_holds
  have hm0pos : 0 < rk2Ord p n := rk2Ord_pos hp hp2 n
  by_cases hm1' : rk2Ord p n = 1
  · exact (i165_false_of_split hK hns
      (rk2_split_untw (by trivial) (rk2Ord_eq_one_iff.1 hm1'))).elim
  by_cases hm3' : 3 ≤ rk2Ord p n
  · exact ⟨Or.inr rfl, hm3'⟩
  have hm2 : rk2Ord p n = 2 := by omega
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn : n = 1 := by omega
    have hp3 : p = 3 := (rk2Ord_one_eq_two_iff hp hp2).1 (by rwa [hn] at hm2)
    exact (i165_false_of_split hK hns (rk2_split_n1 hn hp3)).elim
  have hup : CFSG.Open.evenRank K ≤ l := by
    have h := (rk2_eUpAt_of_tables hKr hUp (rk2_isLabel_norm hK)).bd (Or.inl rfl) hn2
    simpa [rk2Norm] using h
  have hlow : l ≤ CFSG.Open.pRank p (⊤ : Subgroup K) := by
    have h := hTorus K ⟨.C, l, n⟩ p hK hp hp2 hZ
      ((rk2Ord_eq_two_iff hp hp2).1 hm2) hn2 (Or.inr (Or.inl rfl))
    simpa [i165TorusRank] using h
  exact (i165_false_of_rank_le_pRank hp hlow hup hm3 hmax hm1).elim

private theorem i165FamD_of_label {K : Type} [Group K] [Finite K] {A : Subgroup K} {l n p : ℕ}
    (hK : Rk2IsLabel K ⟨.D, l, n⟩)
    (hns : ∀ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) → ¬ GLASplit16 p lab)
    (hTorus : I165TorusRankLower) (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center K)) (hm3 : 3 ≤ CFSG.Open.pRank p A)
    (hmax : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ CFSG.Open.pRank p A)
    (hm1 : CFSG.Open.pRank p A + 1 ≤ evenRank K) (hn1 : 1 ≤ n) (hl3 : 3 ≤ l) :
    i165FamD ⟨.D, l, n⟩ p := by
  have hKr : Rk2KRank := rk2KRank
  have hUp : Rk2Upper := rk2Upper_holds
  have hm0pos : 0 < rk2Ord p n := rk2Ord_pos hp hp2 n
  by_cases hm1' : rk2Ord p n = 1
  · exact (i165_false_of_split hK hns
      (rk2_split_untw (by trivial) (rk2Ord_eq_one_iff.1 hm1'))).elim
  by_cases hm3' : 3 ≤ rk2Ord p n
  · exact ⟨rfl, Or.inl hm3'⟩
  have hm2 : rk2Ord p n = 2 := by omega
  by_cases hodd : Odd l
  · by_cases hl5 : 5 ≤ l
    · exact ⟨rfl, Or.inr ⟨hm2, hodd, hl5⟩⟩
    · have hl3eq : l = 3 := by
        obtain ⟨k, hk⟩ := hodd
        omega
      have hr : rk2Mult ⟨.D, l, n⟩ (rk2Ord p n) ≤ 2 := by
        rw [hl3eq, hm2]
        exact rk2Mult_D_three_two
      exact (i165_false_of_rk2Mult_le_two hK hp hp2 hr hm3 hmax).elim
  · have heven : Even l := Nat.not_odd_iff_even.1 hodd
    have hn2 : 2 ≤ n := by
      by_contra hlt
      have hn : n = 1 := by omega
      have hp3 : p = 3 := (rk2Ord_one_eq_two_iff hp hp2).1 (by rwa [hn] at hm2)
      exact (i165_false_of_split hK hns (rk2_split_n1 hn hp3)).elim
    have hup : CFSG.Open.evenRank K ≤ l :=
      (rk2_eUpAt_of_tables hKr hUp hK).bd (Or.inr rfl) hn2
    have hlow : l ≤ CFSG.Open.pRank p (⊤ : Subgroup K) := by
      have h := hTorus K ⟨.D, l, n⟩ p hK hp hp2 hZ
        ((rk2Ord_eq_two_iff hp hp2).1 hm2) hn2
        (Or.inr (Or.inr (Or.inl ⟨rfl, heven⟩)))
      simpa [i165TorusRank] using h
    exact (i165_false_of_rank_le_pRank hp hlow hup hm3 hmax hm1).elim

private theorem i165FamTwD_of_label {K : Type} [Group K] [Finite K] {l n p : ℕ}
    (hK : Rk2IsLabel K ⟨.twD, l, n⟩)
    (hns : ∀ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) → ¬ GLASplit16 p lab)
    (hp : p.Prime) (hp2 : p ≠ 2) : i165FamTwD ⟨.twD, l, n⟩ p := by
  by_cases hm1 : rk2Ord p n = 1
  · exact (i165_false_of_split hK hns
      (rk2_split_c (Or.inl rfl) (rk2Ord_eq_one_iff.1 hm1))).elim
  by_cases hm2 : rk2Ord p n = 2
  · exact (i165_false_of_split hK hns (rk2_split_tw (by simp [CFSG.Assembly.LargeEvenUntwisted])
      (by simp) (by simp) ((rk2Ord_eq_two_iff hp hp2).1 hm2))).elim
  · have hm3' : 3 ≤ rk2Ord p n := by
      have := rk2Ord_pos hp hp2 n
      omega
    exact ⟨rfl, hm3'⟩

private theorem i165FamE6_of_label {K : Type} [Group K] [Finite K] {A : Subgroup K} {l n p : ℕ}
    (hK : Rk2IsLabel K ⟨.E6, l, n⟩)
    (hns : ∀ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) → ¬ GLASplit16 p lab)
    (hp : p.Prime) (hp2 : p ≠ 2) (hm3 : 3 ≤ CFSG.Open.pRank p A)
    (hmax : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ CFSG.Open.pRank p A)
    (hb : (⁅A, nGen A (⊤ : Subgroup K)⁆ ≠ ⊥ ∨ CFSG.Open.pRank p A + 2 ≤ evenRank K))
    (hn1 : 1 ≤ n) (hl0 : l = 0) : i165FamE6 ⟨.E6, l, n⟩ p := by
  have hKr : Rk2KRank := rk2KRank
  have hUp : Rk2Upper := rk2Upper_holds
  by_cases hm1 : rk2Ord p n = 1
  · exact (i165_false_of_split hK hns
      (rk2_split_untw (by trivial) (rk2Ord_eq_one_iff.1 hm1))).elim
  by_cases hm2 : rk2Ord p n = 2
  · by_cases hn2 : 2 ≤ n
    · exact ⟨rfl, Or.inl ⟨hm2, hn2⟩⟩
    · have hn : n = 1 := by omega
      have hp3 : p = 3 := (rk2Ord_one_eq_two_iff hp hp2).1 (by rwa [hn] at hm2)
      exact (i165_false_of_split hK hns (rk2_split_n1 hn hp3)).elim
  by_cases hm3' : rk2Ord p n = 3
  · by_cases hn2 : 2 ≤ n
    · exact ⟨rfl, Or.inr ⟨hm3', hn2⟩⟩
    · have hn : n = 1 := by omega
      subst l
      subst n
      have hp7 : p = 7 := (rk2Ord_one_eq_three_iff hp).1 hm3'
      have he4 : CFSG.Open.evenRank K ≤ 4 := (rk2_eUpAt_of_tables hKr hUp hK).e6_one rfl
      exact (i165_false_E6_two hK hp hp7 hm3 he4 hb).elim
  · exact (i165_false_of_rk2Mult_le_two hK hp hp2
      (rk2Mult_E6_le_two hm1 hm2 hm3') hm3 hmax).elim

private theorem i165FamTwE6_of_label {K : Type} [Group K] [Finite K] {l n p : ℕ}
    (hK : Rk2IsLabel K ⟨.twE6, l, n⟩)
    (hns : ∀ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) → ¬ GLASplit16 p lab)
    {A : Subgroup K} (hp : p.Prime) (hp2 : p ≠ 2) (hm3 : 3 ≤ CFSG.Open.pRank p A)
    (hmax : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ CFSG.Open.pRank p A) :
    i165FamTwE6 ⟨.twE6, l, n⟩ p := by
  by_cases hm1 : rk2Ord p n = 1
  · exact ⟨rfl, Or.inl hm1⟩
  by_cases hm2 : rk2Ord p n = 2
  · exact (i165_false_of_split hK hns (rk2_split_tw (by simp [CFSG.Assembly.LargeEvenUntwisted])
      (by simp) (by simp) ((rk2Ord_eq_two_iff hp hp2).1 hm2))).elim
  by_cases hm6 : rk2Ord p n = 6
  · exact ⟨rfl, Or.inr hm6⟩
  · exact (i165_false_of_rk2Mult_le_two hK hp hp2
      (rk2Mult_twE6_le_two hm1 hm2 hm6) hm3 hmax).elim

private theorem i165FamE7_of_label {K : Type} [Group K] [Finite K] {A : Subgroup K} {l n p : ℕ}
    (hK : Rk2IsLabel K ⟨.E7, l, n⟩)
    (hns : ∀ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) → ¬ GLASplit16 p lab)
    (hTorus : I165TorusRankLower) (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center K)) (hm3 : 3 ≤ CFSG.Open.pRank p A)
    (hmax : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ CFSG.Open.pRank p A)
    (hm1 : CFSG.Open.pRank p A + 1 ≤ evenRank K) (hn1 : 1 ≤ n) : i165FamE7 ⟨.E7, l, n⟩ p := by
  have hKr : Rk2KRank := rk2KRank
  have hUp : Rk2Upper := rk2Upper_holds
  have hm0pos : 0 < rk2Ord p n := rk2Ord_pos hp hp2 n
  by_cases hm1' : rk2Ord p n = 1
  · exact (i165_false_of_split hK hns
      (rk2_split_untw (by trivial) (rk2Ord_eq_one_iff.1 hm1'))).elim
  by_cases hm2 : rk2Ord p n = 2
  · have hn2 : 2 ≤ n := by
      by_contra hlt
      have hn : n = 1 := by omega
      have hp3 : p = 3 := (rk2Ord_one_eq_two_iff hp hp2).1 (by rwa [hn] at hm2)
      exact (i165_false_of_split hK hns (rk2_split_n1 hn hp3)).elim
    have hup : CFSG.Open.evenRank K ≤ 7 :=
      (rk2_eUpAt_of_tables hKr hUp hK).e7 rfl hn2
    have hlow : 7 ≤ CFSG.Open.pRank p (⊤ : Subgroup K) := by
      have h := hTorus K ⟨.E7, l, n⟩ p hK hp hp2 hZ
        ((rk2Ord_eq_two_iff hp hp2).1 hm2) hn2
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      simpa [i165TorusRank] using h
    exact (i165_false_of_rank_le_pRank hp hlow hup hm3 hmax hm1).elim
  by_cases hm3' : rk2Ord p n = 3
  · exact ⟨rfl, Or.inl hm3'⟩
  by_cases hm6 : rk2Ord p n = 6
  · exact ⟨rfl, Or.inr hm6⟩
  · exact (i165_false_of_rk2Mult_le_two hK hp hp2
      (rk2Mult_E7_le_two hm1' hm2 hm3' hm6) hm3 hmax).elim

private theorem i165FamE8_of_label {K : Type} [Group K] [Finite K] {A : Subgroup K} {l n p : ℕ}
    (hK : Rk2IsLabel K ⟨.E8, l, n⟩)
    (hns : ∀ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) → ¬ GLASplit16 p lab)
    (hTorus : I165TorusRankLower) (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center K)) (hm3 : 3 ≤ CFSG.Open.pRank p A)
    (hmax : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ CFSG.Open.pRank p A)
    (hm1 : CFSG.Open.pRank p A + 1 ≤ evenRank K) (hn1 : 1 ≤ n) : i165FamE8 ⟨.E8, l, n⟩ p := by
  have hKr : Rk2KRank := rk2KRank
  have hUp : Rk2Upper := rk2Upper_holds
  have hm0pos : 0 < rk2Ord p n := rk2Ord_pos hp hp2 n
  by_cases hm1' : rk2Ord p n = 1
  · exact (i165_false_of_split hK hns
      (rk2_split_untw (by trivial) (rk2Ord_eq_one_iff.1 hm1'))).elim
  by_cases hm2 : rk2Ord p n = 2
  · have hn2 : 2 ≤ n := by
      by_contra hlt
      have hn : n = 1 := by omega
      have hp3 : p = 3 := (rk2Ord_one_eq_two_iff hp hp2).1 (by rwa [hn] at hm2)
      exact (i165_false_of_split hK hns (rk2_split_n1 hn hp3)).elim
    have hup : CFSG.Open.evenRank K ≤ 8 :=
      (rk2_eUpAt_of_tables hKr hUp hK).e8 rfl hn2
    have hlow : 8 ≤ CFSG.Open.pRank p (⊤ : Subgroup K) := by
      have h := hTorus K ⟨.E8, l, n⟩ p hK hp hp2 hZ
        ((rk2Ord_eq_two_iff hp hp2).1 hm2) hn2
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
      simpa [i165TorusRank] using h
    exact (i165_false_of_rank_le_pRank hp hlow hup hm3 hmax hm1).elim
  by_cases hm3' : rk2Ord p n = 3
  · exact ⟨rfl, Or.inl hm3'⟩
  by_cases hm4 : rk2Ord p n = 4
  · exact ⟨rfl, Or.inr (Or.inl hm4)⟩
  by_cases hm6 : rk2Ord p n = 6
  · exact ⟨rfl, Or.inr (Or.inr hm6)⟩
  · exact (i165_false_of_rk2Mult_le_two hK hp hp2
      (rk2Mult_E8_le_two hm1' hm2 hm3' hm4 hm6) hm3 hmax).elim

private theorem i165_false_of_F4_label {K : Type} [Group K] [Finite K] {A : Subgroup K}
    {l n p : ℕ} (hK : Rk2IsLabel K ⟨.F4, l, n⟩)
    (hns : ∀ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) → ¬ GLASplit16 p lab)
    (hTorus : I165TorusRankLower) (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center K)) (hm3 : 3 ≤ CFSG.Open.pRank p A)
    (hmax : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ CFSG.Open.pRank p A)
    (hm1 : CFSG.Open.pRank p A + 1 ≤ evenRank K) (hn1 : 1 ≤ n) : False := by
  have hKr : Rk2KRank := rk2KRank
  have hUp : Rk2Upper := rk2Upper_holds
  have hm0pos : 0 < rk2Ord p n := rk2Ord_pos hp hp2 n
  by_cases hm1' : rk2Ord p n = 1
  · exact (i165_false_of_split hK hns
      (rk2_split_untw (by trivial) (rk2Ord_eq_one_iff.1 hm1'))).elim
  by_cases hm2 : rk2Ord p n = 2
  · have hn2 : 2 ≤ n := by
      by_contra hlt
      have hn : n = 1 := by omega
      have hp3 : p = 3 := (rk2Ord_one_eq_two_iff hp hp2).1 (by rwa [hn] at hm2)
      exact (i165_false_of_split hK hns (rk2_split_n1 hn hp3)).elim
    have hup : CFSG.Open.evenRank K ≤ 4 :=
      (rk2_eUpAt_of_tables hKr hUp hK).f4 rfl hn2
    have hlow : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup K) := by
      have h := hTorus K ⟨.F4, l, n⟩ p hK hp hp2 hZ
        ((rk2Ord_eq_two_iff hp hp2).1 hm2) hn2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      simpa [i165TorusRank] using h
    exact (i165_false_of_rank_le_pRank hp hlow hup hm3 hmax hm1).elim
  · exact (i165_false_of_rk2Mult_le_two hK hp hp2
      (rk2Mult_F4_le_two hm1' hm2) hm3 hmax).elim

private theorem i165_false_of_small_label {K : Type} [Group K] [Finite K] {A : Subgroup K}
    {lab : GLALabel} {p : ℕ} (hK : Rk2IsLabel K lab) (hp : p.Prime) (hp2 : p ≠ 2)
    (ht : lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
      lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der)
    (hm3 : 3 ≤ CFSG.Open.pRank p A)
    (hmax : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ CFSG.Open.pRank p A) : False :=
  i165_false_of_rk2Mult_le_two hK hp hp2
    (rk2Mult_le_two_of_small ht (rk2Ord_pos hp hp2 lab.n)) hm3 hmax

theorem i165Fact_of_families
    (hA : I165On i165FamA) (hTwA : I165On i165FamTwA) (hBC : I165On i165FamBC)
    (hD : I165On i165FamD) (hTwD : I165On i165FamTwD) (hE6 : I165On i165FamE6)
    (hTwE6 : I165On i165FamTwE6) (hE7 : I165On i165FamE7) (hE8 : I165On i165FamE8)
    (hTorus : I165TorusRankLower) : I165Fact := by
  intro K _ _ hK0 p q hp hp2 hq hq2 hqp hns hZ A hAe hSC h12 hmax hb he hm1 hm4
  obtain ⟨lab, hlab2, hK⟩ := rk2_exists_label hK0
  have hm3 : 3 ≤ CFSG.Open.pRank p A := by omega
  obtain ⟨t, l, n⟩ := lab
  have hn1 : 1 ≤ n := hlab2.1
  cases t with
  | A =>
    exact hA K ⟨.A, l, n⟩ p q hK (i165FamA_of_label hK hns hp hp2 hm3 hmax)
      hp hp2 hq hq2 hqp hns hZ A hAe hSC h12 hmax hb he hm1 hm4
  | twA =>
    exact hTwA K ⟨.twA, l, n⟩ p q hK (i165FamTwA_of_label hK hns hp hp2)
      hp hp2 hq hq2 hqp hns hZ A hAe hSC h12 hmax hb he hm1 hm4
  | B =>
    exact hBC K ⟨.B, l, n⟩ p q hK
      (i165FamB_of_label hK hns hTorus hp hp2 hZ hm3 hmax hm1 hn1)
      hp hp2 hq hq2 hqp hns hZ A hAe hSC h12 hmax hb he hm1 hm4
  | C =>
    exact hBC K ⟨.C, l, n⟩ p q hK
      (i165FamC_of_label hK hns hTorus hp hp2 hZ hm3 hmax hm1 hn1)
      hp hp2 hq hq2 hqp hns hZ A hAe hSC h12 hmax hb he hm1 hm4
  | D =>
    exact hD K ⟨.D, l, n⟩ p q hK
      (i165FamD_of_label hK hns hTorus hp hp2 hZ hm3 hmax hm1 hn1 hlab2.2)
      hp hp2 hq hq2 hqp hns hZ A hAe hSC h12 hmax hb he hm1 hm4
  | twD =>
    exact hTwD K ⟨.twD, l, n⟩ p q hK (i165FamTwD_of_label hK hns hp hp2)
      hp hp2 hq hq2 hqp hns hZ A hAe hSC h12 hmax hb he hm1 hm4
  | E6 =>
    have hl0 : l = 0 := hlab2.2
    exact hE6 K ⟨.E6, l, n⟩ p q hK
      (i165FamE6_of_label hK hns hp hp2 hm3 hmax hb hn1 hl0)
      hp hp2 hq hq2 hqp hns hZ A hAe hSC h12 hmax hb he hm1 hm4
  | E7 =>
    exact hE7 K ⟨.E7, l, n⟩ p q hK
      (i165FamE7_of_label hK hns hTorus hp hp2 hZ hm3 hmax hm1 hn1)
      hp hp2 hq hq2 hqp hns hZ A hAe hSC h12 hmax hb he hm1 hm4
  | E8 =>
    exact hE8 K ⟨.E8, l, n⟩ p q hK
      (i165FamE8_of_label hK hns hTorus hp hp2 hZ hm3 hmax hm1 hn1)
      hp hp2 hq hq2 hqp hns hZ A hAe hSC h12 hmax hb he hm1 hm4
  | F4 =>
    exact (i165_false_of_F4_label hK hns hTorus hp hp2 hZ hm3 hmax hm1 hn1).elim
  | twE6 =>
    exact hTwE6 K ⟨.twE6, l, n⟩ p q hK
      (i165FamTwE6_of_label hK hns hp hp2 hm3 hmax)
      hp hp2 hq hq2 hqp hns hZ A hAe hSC h12 hmax hb he hm1 hm4
  | triD4 =>
    exact (i165_false_of_small_label hK hp hp2 (by simp) hm3 hmax).elim
  | G2 =>
    exact (i165_false_of_small_label hK hp hp2 (by simp) hm3 hmax).elim
  | twB2 =>
    exact (i165_false_of_small_label hK hp hp2 (by simp) hm3 hmax).elim
  | twF4 =>
    exact (i165_false_of_small_label hK hp hp2 (by simp) hm3 hmax).elim
  | B2der =>
    exact (i165_false_of_small_label hK hp hp2 (by simp) hm3 hmax).elim
  | G2der =>
    exact (i165_false_of_small_label hK hp hp2 (by simp) hm3 hmax).elim
  | twF4der =>
    exact (i165_false_of_small_label hK hp hp2 (by simp) hm3 hmax).elim

end CFSG.LocalAnalysis.GLTheoremA.Y10F
