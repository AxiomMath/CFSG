module

public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Matrix Subgroup
open scoped commutatorElement

section Helpers

variable {r : ℕ} {D : Type} [Group D]

private theorem exists_card_eq_pow [Finite D] (hr : r.Prime) (hexp : ∀ x : D, x ^ r = 1)
    (H : Subgroup D) : ∃ k, Nat.card H = r ^ k := by
  have := Fact.mk hr
  have hP : IsPGroup r D := fun g => ⟨1, by simpa using hexp g⟩
  exact IsPGroup.iff_card.mp (hP.to_subgroup H)

private theorem mul_card_le_of_lt [Finite D] (hr : r.Prime) (hexp : ∀ x : D, x ^ r = 1)
    {H K : Subgroup D} (h : H < K) : r * Nat.card H ≤ Nat.card K := by
  obtain ⟨i, hi⟩ := exists_card_eq_pow hr hexp H
  obtain ⟨j, hj⟩ := exists_card_eq_pow hr hexp K
  have hlt := card_lt_of_lt h
  rw [hi, hj] at hlt
  rw [hi, hj, ← pow_succ']
  exact Nat.pow_le_pow_right hr.pos ((Nat.pow_lt_pow_iff_right hr.one_lt).mp hlt)

private theorem card_le_of_abelian [Finite D] (hr : r.Prime) (hexp : ∀ x : D, x ^ r = 1)
    (hrk : CFSG.Open.pRank r (⊤ : Subgroup D) ≤ 3) {A : Subgroup D} (hA : A ≤ centralizer A) :
    Nat.card A ≤ r ^ 3 := by
  obtain ⟨k, hk⟩ := exists_card_eq_pow hr hexp A
  have hE : CFSG.Open.IsElemAbelian r A :=
    ⟨le_centralizer_iff_isMulCommutative.mp hA, fun x _ => hexp x⟩
  rw [hk]
  exact Nat.pow_le_pow_right hr.pos
    ((CFSG.SectionRank.le_pRank hr.one_lt le_top hE hk).trans hrk)

private theorem index_centralizer_le [Finite D] (x : D) :
    (centralizer {x}).index ≤ Nat.card (commutator D) := by
  rw [index_centralizer_eq_ncard]
  change _ ≤ (commutator D : Set D).ncard
  refine (Set.ncard_le_ncard ?_).trans
    (Set.ncard_image_of_injective _ (mul_left_injective x)).le
  rintro y ⟨c, hc⟩
  refine ⟨⁅(c : D), x⁆, ?_, ?_⟩
  · rw [_root_.commutator_def]
    exact commutator_mem_commutator (mem_top _) (mem_top _)
  · simp [commutatorElement_def, eq_mul_inv_of_mul_eq hc.symm]

private theorem le_centralizer_sup {A L : Subgroup D} {x : D} (hL : L ≤ centralizer A)
    (hx : x ∈ centralizer L) : L ≤ centralizer (A ⊔ zpowers x : Subgroup D) :=
  le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp hL) (zpowers_le.mpr hx))

private theorem step_of_mem [Finite D] (hr : r.Prime) (hexp : ∀ x : D, x ^ r = 1)
    {A K : Subgroup D} (hA : A ≤ centralizer A) (hK : K ≤ centralizer A) {x : D} (hx : x ∈ K)
    (hxA : x ∉ A) :
    A ⊔ zpowers x ≤ centralizer (A ⊔ zpowers x : Subgroup D) ∧
      K ⊓ centralizer {x} ≤ centralizer (A ⊔ zpowers x : Subgroup D) ∧
      r * Nat.card A ≤ Nat.card (A ⊔ zpowers x : Subgroup D) := by
  have hxc : zpowers x ≤ centralizer A := zpowers_le.mpr (hK hx)
  have hAx : A ⊔ zpowers x ≤ centralizer (zpowers x : Subgroup D) :=
    sup_le (le_centralizer_iff.mp hxc) (le_centralizer _)
  refine ⟨le_centralizer_sup (sup_le hA hxc) (zpowers_le.mp (le_centralizer_iff.mp hAx)),
    le_centralizer_sup (inf_le_left.trans hK) fun h hh => ?_, ?_⟩
  · exact mem_centralizer_singleton_iff.mp (mem_inf.mp hh).2
  · exact mul_card_le_of_lt hr hexp
      (SetLike.lt_iff_le_and_exists.mpr ⟨le_sup_left, x, mem_sup_right (mem_zpowers x), hxA⟩)

private theorem step [Finite D] (hr : r.Prime) (hexp : ∀ x : D, x ^ r = 1)
    (hrk : CFSG.Open.pRank r (⊤ : Subgroup D) ≤ 3) {A K : Subgroup D} (hA : A ≤ centralizer A)
    (hK : K ≤ centralizer A) {c : ℕ} (hc : K.index ≤ c) (hlt : r ^ 3 * c < Nat.card D) :
    ∃ A' K' : Subgroup D, A' ≤ centralizer A' ∧ K' ≤ centralizer A' ∧
      K'.index ≤ c * Nat.card (commutator D) ∧ r * Nat.card A ≤ Nat.card A' := by
  have hAc := card_le_of_abelian hr hexp hrk hA
  have hKD := card_mul_index K
  have hAK : Nat.card A < Nat.card K := by
    by_contra h
    push Not at h
    have : Nat.card K * K.index ≤ r ^ 3 * c := Nat.mul_le_mul (h.trans hAc) hc
    omega
  obtain ⟨x, hxK, hxA⟩ : ∃ x ∈ K, x ∉ A := by
    by_contra h
    push Not at h
    exact absurd (card_le_of_le h) (not_le.mpr hAK)
  obtain ⟨h1, h2, h3⟩ := step_of_mem hr hexp hA hK hxK hxA
  refine ⟨_, _, h1, h2, index_inf_le.trans ?_, h3⟩
  exact Nat.mul_le_mul hc (index_centralizer_le x)

private theorem commutator_start (hcl : commutator D ≤ center D) :
    commutator D ≤ centralizer (commutator D : Subgroup D) ∧
      (⊤ : Subgroup D) ≤ centralizer (commutator D : Subgroup D) :=
  ⟨hcl.trans (center_le_centralizer _),
    le_centralizer_iff.mpr (hcl.trans (by rw [coe_top, centralizer_univ]))⟩

private theorem card_commutator_ne_one [Finite D] (hr : r.Prime) (hexp : ∀ x : D, x ^ r = 1)
    (hrk : CFSG.Open.pRank r (⊤ : Subgroup D) ≤ 3) (h4 : r ^ 4 ≤ Nat.card (D ⧸ commutator D)) :
    Nat.card (commutator D) ≠ 1 := by
  intro h1
  have hA : (⊤ : Subgroup D) ≤ centralizer (⊤ : Subgroup D) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (by rw [← _root_.commutator_def]; exact eq_bot_of_card_eq _ h1)
  have h := card_le_of_abelian hr hexp hrk hA
  rw [card_top, card_eq_card_quotient_mul_card_subgroup (commutator D), h1, mul_one] at h
  have : r ^ 3 < r ^ 4 := Nat.pow_lt_pow_right hr.one_lt (by norm_num)
  omega

private theorem not_sq_le_card_commutator [Finite D] (hr : r.Prime) (hexp : ∀ x : D, x ^ r = 1)
    (hcl : commutator D ≤ center D) (hrk : CFSG.Open.pRank r (⊤ : Subgroup D) ≤ 3)
    (h4 : r ^ 4 ≤ Nat.card (D ⧸ commutator D)) : ¬ r ^ 2 ≤ Nat.card (commutator D) := by
  intro hu
  obtain ⟨hN, hT⟩ := commutator_start hcl
  have hD := card_eq_card_quotient_mul_card_subgroup (commutator D)
  have hu0 : 0 < Nat.card (commutator D) := Nat.card_pos
  have h34 : r ^ 3 < r ^ 4 := Nat.pow_lt_pow_right hr.one_lt (by norm_num)
  have hlt : r ^ 3 * (1 * Nat.card (commutator D)) < Nat.card D := by
    rw [hD, one_mul]
    exact Nat.mul_lt_mul_of_pos_right (h34.trans_le h4) hu0
  have hlt1 : r ^ 3 * 1 < Nat.card D :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (by omega)) hlt
  obtain ⟨A1, K1, hA1, hK1, hi1, hc1⟩ := step hr hexp hrk hN hT (by rw [index_top]) hlt1
  obtain ⟨A2, -, hA2, -, -, hc2⟩ := step hr hexp hrk hA1 hK1 hi1 hlt
  have h := card_le_of_abelian hr hexp hrk hA2
  have : r ^ 4 ≤ r * (r * Nat.card (commutator D)) := by
    rw [← mul_assoc, ← sq, show r ^ 4 = r ^ 2 * r ^ 2 by ring]
    exact Nat.mul_le_mul_left _ hu
  have : r * (r * Nat.card (commutator D)) ≤ Nat.card A2 :=
    (Nat.mul_le_mul_left r hc1).trans hc2
  omega

private theorem card_quotient_lt [Finite D] (hr : r.Prime) (hexp : ∀ x : D, x ^ r = 1)
    (hcl : commutator D ≤ center D) (hrk : CFSG.Open.pRank r (⊤ : Subgroup D) ≤ 3)
    (hu : Nat.card (commutator D) = r) : ¬ r ^ 5 ≤ Nat.card (D ⧸ commutator D) := by
  intro h5
  obtain ⟨hN, hT⟩ := commutator_start hcl
  have hD := card_eq_card_quotient_mul_card_subgroup (commutator D)
  rw [hu] at hD
  have h45 : r ^ 4 < r ^ 5 := Nat.pow_lt_pow_right hr.one_lt (by norm_num)
  have hlt : r ^ 3 * (1 * r * r) < Nat.card D := by
    rw [hD, show r ^ 3 * (1 * r * r) = r ^ 4 * r by ring]
    exact Nat.mul_lt_mul_of_pos_right (h45.trans_le h5) hr.pos
  have hlt1 : r ^ 3 * 1 < Nat.card D :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (by nlinarith [hr.one_lt])) hlt
  have hlt2 : r ^ 3 * (1 * Nat.card (commutator D)) < Nat.card D :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (by rw [hu]; nlinarith [hr.one_lt])) hlt
  obtain ⟨A1, K1, hA1, hK1, hi1, hc1⟩ := step hr hexp hrk hN hT (by rw [index_top]) hlt1
  obtain ⟨A2, K2, hA2, hK2, hi2, hc2⟩ := step hr hexp hrk hA1 hK1 hi1 hlt2
  obtain ⟨A3, -, hA3, -, -, hc3⟩ := step hr hexp hrk hA2 hK2 hi2 (by rw [hu]; exact hlt)
  have h := card_le_of_abelian hr hexp hrk hA3
  rw [hu] at hc1
  have : r * (r * (r * r)) ≤ Nat.card A3 :=
    (Nat.mul_le_mul_left r ((Nat.mul_le_mul_left r hc1).trans hc2)).trans hc3
  have : r ^ 3 < r * (r * (r * r)) := by
    rw [show r * (r * (r * r)) = r ^ 4 by ring]
    exact Nat.pow_lt_pow_right hr.one_lt (by norm_num)
  omega

private theorem center_le_commutator [Finite D] (hr : r.Prime) (hexp : ∀ x : D, x ^ r = 1)
    (hcl : commutator D ≤ center D) (hrk : CFSG.Open.pRank r (⊤ : Subgroup D) ≤ 3)
    (h4 : r ^ 4 ≤ Nat.card (D ⧸ commutator D)) (hu : Nat.card (commutator D) = r) :
    center D ≤ commutator D := by
  by_contra hZ
  obtain ⟨z, hz, hzN⟩ := SetLike.not_le_iff_exists.mp hZ
  obtain ⟨hN, hT⟩ := commutator_start hcl
  obtain ⟨hA0, hK0, hc0⟩ := step_of_mem hr hexp hN hT (mem_top z) hzN
  rw [top_inf_eq, (centralizer_eq_top_iff_subset.mpr (Set.singleton_subset_iff.mpr hz))] at hK0
  have hD := card_eq_card_quotient_mul_card_subgroup (commutator D)
  rw [hu] at hD hc0
  have h34 : r ^ 3 < r ^ 4 := Nat.pow_lt_pow_right hr.one_lt (by norm_num)
  have hlt : r ^ 3 * (1 * r) < Nat.card D := by
    rw [hD, one_mul]
    exact Nat.mul_lt_mul_of_pos_right (h34.trans_le h4) hr.pos
  have hlt1 : r ^ 3 * 1 < Nat.card D :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (by rw [one_mul]; exact hr.one_lt.le)) hlt
  obtain ⟨A1, K1, hA1, hK1, hi1, hc1⟩ := step hr hexp hrk hA0 hK0 (by rw [index_top]) hlt1
  obtain ⟨A2, -, hA2, -, -, hc2⟩ := step hr hexp hrk hA1 hK1 hi1 (by rw [hu]; exact hlt)
  have h := card_le_of_abelian hr hexp hrk hA2
  have : r * (r * (r * r)) ≤ Nat.card A2 :=
    (Nat.mul_le_mul_left r ((Nat.mul_le_mul_left r hc0).trans hc1)).trans hc2
  have : r ^ 3 < r * (r * (r * r)) := by
    rw [show r * (r * (r * r)) = r ^ 4 by ring]
    exact h34
  omega

end Helpers

theorem card_commutator_eq_of_pRank_le_three {r : ℕ} (hr : r.Prime) {D : Type} [Group D]
    [Finite D] (hexp : ∀ x : D, x ^ r = 1)
    (hcl : commutator D ≤ Subgroup.center D)
    (hrk : CFSG.Open.pRank r (⊤ : Subgroup D) ≤ 3)
    (h4 : r ^ 4 ≤ Nat.card (D ⧸ commutator D)) :
    Nat.card (commutator D) = r ∧ Subgroup.center D = commutator D ∧
      Nat.card (D ⧸ commutator D) = r ^ 4 := by
  have hu : Nat.card (commutator D) = r := by
    obtain ⟨a, ha⟩ := exists_card_eq_pow hr hexp (commutator D)
    rcases a with _ | _ | a
    · exact absurd (by simpa using ha) (card_commutator_ne_one hr hexp hrk h4)
    · simpa using ha
    · refine absurd ?_ (not_sq_le_card_commutator hr hexp hcl hrk h4)
      rw [ha]
      exact Nat.pow_le_pow_right hr.pos (by omega)
  have := Fact.mk hr
  have hP : IsPGroup r D := fun g => ⟨1, by simpa using hexp g⟩
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (hP.to_quotient (commutator D))
  have h5 := card_quotient_lt hr hexp hcl hrk hu
  rw [hb] at h4 h5 ⊢
  have hb4 : 4 ≤ b := (Nat.pow_le_pow_iff_right hr.one_lt).mp h4
  have hb5 : ¬ 5 ≤ b := fun h => h5 (Nat.pow_le_pow_right hr.pos h)
  refine ⟨hu, le_antisymm (center_le_commutator hr hexp hcl hrk (hb ▸ h4) hu) hcl, ?_⟩
  rw [show b = 4 by omega]

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
