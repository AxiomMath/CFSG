module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotInvolutionCentralizer

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix

variable {n : ℕ} {K : Type*} [Field K]

theorem one_add_single_mul_mul_one_add_single_apply_of_ne_row {i j r : Fin n} (hri : r ≠ i)
    (c d : K) (B : Matrix (Fin n) (Fin n) K) (l : Fin n) :
    ((1 + single i j c) * B * (1 + single i j d)) r l =
      B r l + if l = j then B r i * d else 0 := by
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul,
    Matrix.add_apply, Matrix.add_apply, Matrix.add_apply, single_mul_apply_of_ne _ _ _ _ _ hri,
    single_mul_mul_single, add_zero]
  by_cases hl : l = j
  · subst hl
    rw [mul_single_apply_same, single_apply_of_row_ne (Ne.symm hri), add_zero, ite_eq_left rfl]
  · rw [mul_single_apply_of_ne _ _ _ _ _ hl, single_apply_of_col_ne _ _ (Ne.symm hl), add_zero,
      ite_eq_right hl]

theorem one_add_single_mul_mul_one_add_single_apply_of_ne_col {i j l : Fin n} (hlj : l ≠ j)
    (c d : K) (B : Matrix (Fin n) (Fin n) K) (r : Fin n) :
    ((1 + single i j c) * B * (1 + single i j d)) r l =
      B r l + if r = i then c * B j l else 0 := by
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul,
    Matrix.add_apply, Matrix.add_apply, Matrix.add_apply, mul_single_apply_of_ne _ _ _ _ _ hlj,
    single_mul_mul_single, single_apply_of_col_ne _ _ (Ne.symm hlj), add_zero, add_zero]
  by_cases hr : r = i
  · subst hr
    rw [single_mul_apply_same, ite_eq_left rfl]
  · rw [single_mul_apply_of_ne _ _ _ _ _ hr, ite_eq_right hr]

omit [Field K] in
private theorem eq_one_of_ne_zero_of_natCard_eq_two_aux [Field K] (hK : Nat.card K = 2) {x : K}
    (hx : x ≠ 0) : x = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card x
  rw [← Nat.card_eq_fintype_card, hK, sq] at h
  exact mul_left_cancel₀ hx (h.trans (mul_one x).symm)

namespace InvPlacement

variable (P : InvPlacement n 1)

theorem level_eq_zero_iff_eq_u_zero {i : Fin n} : P.level i = 0 ↔ i = P.u 0 := by
  rw [P.level_eq_zero_iff]
  constructor
  · rintro ⟨a, rfl⟩
    rw [Subsingleton.elim a 0]
  · rintro rfl
    exact ⟨0, rfl⟩

theorem level_eq_two_iff_eq_w_zero {i : Fin n} : P.level i = 2 ↔ i = P.w 0 := by
  rw [P.level_eq_two_iff]
  constructor
  · rintro ⟨a, rfl⟩
    rw [Subsingleton.elim a 0]
  · rintro rfl
    exact ⟨0, rfl⟩

theorem exists_free_ne_ne (hJ : 3 ≤ P.free.card) (a b : P.free) : ∃ c : P.free, c ≠ a ∧ c ≠ b := by
  classical
  by_contra hc
  push Not at hc
  have hsub : (Finset.univ : Finset P.free) ⊆ {a, b} := fun c _ => by
    by_cases hca : c = a
    · simp [hca]
    · simp [hc c hca]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_coe] at h1
  have h2 := Finset.card_le_two (a := a) (b := b)
  omega

@[expose] def freeRowCol (B : SpecialLinearGroup (Fin n) K) : (P.free → K) × (P.free → K) :=
  (fun l => (B : Matrix (Fin n) (Fin n) K) (P.u 0) l,
    fun l => (B : Matrix (Fin n) (Fin n) K) l (P.w 0))

theorem freeRowCol_fst_apply (B : SpecialLinearGroup (Fin n) K) (l : P.free) :
    (P.freeRowCol B).1 l = (B : Matrix (Fin n) (Fin n) K) (P.u 0) l :=
  rfl

theorem freeRowCol_snd_apply (B : SpecialLinearGroup (Fin n) K) (l : P.free) :
    (P.freeRowCol B).2 l = (B : Matrix (Fin n) (Fin n) K) l (P.w 0) :=
  rfl

theorem freeRowCol_mul {B B' : SpecialLinearGroup (Fin n) K} (hB : B ∈ P.radical K)
    (hB' : B' ∈ P.radical K) : P.freeRowCol (B * B') = P.freeRowCol B + P.freeRowCol B' := by
  refine Prod.ext (funext fun l => ?_) (funext fun l => ?_)
  · have h := congrFun (congrFun (P.regionPart_mul_radical hB hB' 0) (P.u 0)) l
    rw [Matrix.add_apply, regionPart_apply, regionPart_apply, regionPart_apply,
      ite_eq_left ⟨P.level_u 0, P.mem_free.1 l.2⟩, ite_eq_left ⟨P.level_u 0, P.mem_free.1 l.2⟩,
      ite_eq_left ⟨P.level_u 0, P.mem_free.1 l.2⟩] at h
    exact h
  · have h := congrFun (congrFun (P.regionPart_mul_radical hB hB' 1) l) (P.w 0)
    rw [Matrix.add_apply, regionPart_apply, regionPart_apply, regionPart_apply,
      ite_eq_left ⟨P.mem_free.1 l.2, P.level_w 0⟩, ite_eq_left ⟨P.mem_free.1 l.2, P.level_w 0⟩,
      ite_eq_left ⟨P.mem_free.1 l.2, P.level_w 0⟩] at h
    exact h

theorem freeRowCol_one : P.freeRowCol (1 : SpecialLinearGroup (Fin n) K) = 0 := by
  refine Prod.ext (funext fun l => ?_) (funext fun l => ?_)
  · rw [freeRowCol_fst_apply, Matrix.SpecialLinearGroup.coe_one]
    exact one_apply_ne fun h => P.u_not_mem_free 0 (h ▸ l.2)
  · rw [freeRowCol_snd_apply, Matrix.SpecialLinearGroup.coe_one]
    exact one_apply_ne fun h => P.w_not_mem_free 0 (h.symm ▸ l.2)

theorem freeRowCol_transvection_conj {i j : Fin n} (hij : i ≠ j) (hi : i ∈ P.free)
    (hj : j ∈ P.free) (c : K) (B : SpecialLinearGroup (Fin n) K) :
    P.freeRowCol (Matrix.SpecialLinearGroup.transvection hij c * B *
        (Matrix.SpecialLinearGroup.transvection hij c)⁻¹) =
      P.freeRowCol B + (Pi.single ⟨j, hj⟩ ((B : Matrix (Fin n) (Fin n) K) (P.u 0) i * -c),
        Pi.single ⟨i, hi⟩ (c * (B : Matrix (Fin n) (Fin n) K) j (P.w 0))) := by
  have hcoe : ((Matrix.SpecialLinearGroup.transvection hij c * B *
      (Matrix.SpecialLinearGroup.transvection hij c)⁻¹ : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) =
      (1 + single i j c) * (B : Matrix (Fin n) (Fin n) K) * (1 + single i j (-c)) := by
    rw [Matrix.SpecialLinearGroup.transvection_inv, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.SpecialLinearGroup.transvection_coe]
  have hui : P.u 0 ≠ i := fun h => P.u_not_mem_free 0 (h ▸ hi)
  have hwj : P.w 0 ≠ j := fun h => P.w_not_mem_free 0 (h ▸ hj)
  refine Prod.ext (funext fun l => ?_) (funext fun l => ?_)
  · rw [freeRowCol_fst_apply, hcoe, one_add_single_mul_mul_one_add_single_apply_of_ne_row hui,
      Prod.fst_add, Pi.add_apply, freeRowCol_fst_apply]
    simp only [Pi.single_apply, Subtype.ext_iff]
  · rw [freeRowCol_snd_apply, hcoe, one_add_single_mul_mul_one_add_single_apply_of_ne_col hwj,
      Prod.snd_add, Pi.add_apply, freeRowCol_snd_apply]
    simp only [Pi.single_apply, Subtype.ext_iff]

theorem exists_mem_freeRowCol_eq_single [CharP K 2]
    {R' : Subgroup (SpecialLinearGroup (Fin n) K)} (hR : R' ≤ P.radical K)
    (hN : ∀ (i j : Fin n) (hij : i ≠ j), i ∈ P.free → j ∈ P.free → ∀ B ∈ R',
      Matrix.SpecialLinearGroup.transvection hij (1 : K) * B *
        (Matrix.SpecialLinearGroup.transvection hij (1 : K))⁻¹ ∈ R')
    {B : SpecialLinearGroup (Fin n) K} (hB : B ∈ R') {i j : P.free} (hij : i ≠ j) :
    ∃ C ∈ R', P.freeRowCol C =
      (Pi.single j ((B : Matrix (Fin n) (Fin n) K) (P.u 0) i),
        Pi.single i ((B : Matrix (Fin n) (Fin n) K) j (P.w 0))) := by
  have hij' : (i : Fin n) ≠ j := fun h => hij (Subtype.ext h)
  have hTB := hN i j hij' i.2 j.2 B hB
  refine ⟨_, mul_mem hTB hB, ?_⟩
  rw [P.freeRowCol_mul (hR hTB) (hR hB), P.freeRowCol_transvection_conj hij' i.2 j.2]
  have h2 : ∀ x : (P.free → K) × (P.free → K), x + x = 0 := fun x => by
    refine Prod.ext (funext fun l => ?_) (funext fun l => ?_) <;>
      exact CharTwo.add_self_eq_zero _
  rw [add_comm, ← add_assoc, h2, zero_add, CharTwo.neg_eq, mul_one, one_mul]

theorem exists_mem_freeRowCol_eq_zero_single_of [CharP K 2]
    {R' : Subgroup (SpecialLinearGroup (Fin n) K)} (hR : R' ≤ P.radical K)
    (hN : ∀ (i j : Fin n) (hij : i ≠ j), i ∈ P.free → j ∈ P.free → ∀ B ∈ R',
      Matrix.SpecialLinearGroup.transvection hij (1 : K) * B *
        (Matrix.SpecialLinearGroup.transvection hij (1 : K))⁻¹ ∈ R')
    {D : SpecialLinearGroup (Fin n) K} (hD : D ∈ R') {k₀ : P.free}
    (hψ : P.freeRowCol D = (0, Pi.single k₀ 1)) (k : P.free) :
    ∃ D' ∈ R', P.freeRowCol D' = (0, Pi.single k 1) := by
  by_cases hk : k = k₀
  · exact ⟨D, hD, hk ▸ hψ⟩
  · obtain ⟨C, hC, hψC⟩ := P.exists_mem_freeRowCol_eq_single hR hN hD hk
    have h1 : (D : Matrix (Fin n) (Fin n) K) (P.u 0) k = 0 := by
      rw [← freeRowCol_fst_apply, hψ]
      rfl
    have h2 : (D : Matrix (Fin n) (Fin n) K) k₀ (P.w 0) = 1 := by
      rw [← freeRowCol_snd_apply, hψ]
      exact Pi.single_eq_same _ _
    exact ⟨C, hC, by rw [hψC, h1, h2, Pi.single_zero]⟩

theorem exists_mem_freeRowCol_eq_single_zero_of [CharP K 2]
    {R' : Subgroup (SpecialLinearGroup (Fin n) K)} (hR : R' ≤ P.radical K)
    (hN : ∀ (i j : Fin n) (hij : i ≠ j), i ∈ P.free → j ∈ P.free → ∀ B ∈ R',
      Matrix.SpecialLinearGroup.transvection hij (1 : K) * B *
        (Matrix.SpecialLinearGroup.transvection hij (1 : K))⁻¹ ∈ R')
    {E : SpecialLinearGroup (Fin n) K} (hE : E ∈ R') {k₀ : P.free}
    (hψ : P.freeRowCol E = (Pi.single k₀ 1, 0)) (k : P.free) :
    ∃ E' ∈ R', P.freeRowCol E' = (Pi.single k 1, 0) := by
  by_cases hk : k = k₀
  · exact ⟨E, hE, hk ▸ hψ⟩
  · obtain ⟨C, hC, hψC⟩ := P.exists_mem_freeRowCol_eq_single hR hN hE (Ne.symm hk)
    have h1 : (E : Matrix (Fin n) (Fin n) K) (P.u 0) k₀ = 1 := by
      rw [← freeRowCol_fst_apply, hψ]
      exact Pi.single_eq_same _ _
    have h2 : (E : Matrix (Fin n) (Fin n) K) k (P.w 0) = 0 := by
      rw [← freeRowCol_snd_apply, hψ]
      rfl
    exact ⟨C, hC, by rw [hψC, h1, h2, Pi.single_zero]⟩

theorem exists_mem_freeRowCol_eq_zero_single [CharP K 2] (hK : Nat.card K = 2)
    (hJ : 3 ≤ P.free.card) {R' : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hR : R' ≤ P.radical K)
    (hN : ∀ (i j : Fin n) (hij : i ≠ j), i ∈ P.free → j ∈ P.free → ∀ B ∈ R',
      Matrix.SpecialLinearGroup.transvection hij (1 : K) * B *
        (Matrix.SpecialLinearGroup.transvection hij (1 : K))⁻¹ ∈ R')
    {B : SpecialLinearGroup (Fin n) K} (hB : B ∈ R') {j : P.free}
    (hj : (B : Matrix (Fin n) (Fin n) K) j (P.w 0) ≠ 0) (k : P.free) :
    ∃ D ∈ R', P.freeRowCol D = (0, Pi.single k 1) := by
  have hj1 := eq_one_of_ne_zero_of_natCard_eq_two_aux hK hj
  obtain ⟨i, hij, -⟩ := P.exists_free_ne_ne hJ j j
  obtain ⟨i', hi'i, hi'j⟩ := P.exists_free_ne_ne hJ i j
  obtain ⟨C₁, hC₁, hψ₁⟩ := P.exists_mem_freeRowCol_eq_single hR hN hB hij
  obtain ⟨C₂, hC₂, hψ₂⟩ := P.exists_mem_freeRowCol_eq_single hR hN hC₁ hi'i
  have h1 : (C₁ : Matrix (Fin n) (Fin n) K) (P.u 0) i' = 0 := by
    rw [← freeRowCol_fst_apply, hψ₁]
    exact Pi.single_eq_of_ne hi'j _
  have h2 : (C₁ : Matrix (Fin n) (Fin n) K) i (P.w 0) = 1 := by
    rw [← freeRowCol_snd_apply, hψ₁]
    exact (Pi.single_eq_same _ _).trans hj1
  rw [h1, h2, Pi.single_zero] at hψ₂
  exact P.exists_mem_freeRowCol_eq_zero_single_of hR hN hC₂ hψ₂ k

theorem exists_mem_freeRowCol_eq_single_zero [CharP K 2] (hK : Nat.card K = 2)
    (hJ : 3 ≤ P.free.card) {R' : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hR : R' ≤ P.radical K)
    (hN : ∀ (i j : Fin n) (hij : i ≠ j), i ∈ P.free → j ∈ P.free → ∀ B ∈ R',
      Matrix.SpecialLinearGroup.transvection hij (1 : K) * B *
        (Matrix.SpecialLinearGroup.transvection hij (1 : K))⁻¹ ∈ R')
    {B : SpecialLinearGroup (Fin n) K} (hB : B ∈ R') {i : P.free}
    (hi : (B : Matrix (Fin n) (Fin n) K) (P.u 0) i ≠ 0) (k : P.free) :
    ∃ E ∈ R', P.freeRowCol E = (Pi.single k 1, 0) := by
  have hi1 := eq_one_of_ne_zero_of_natCard_eq_two_aux hK hi
  obtain ⟨j, hji, -⟩ := P.exists_free_ne_ne hJ i i
  obtain ⟨j', hj'i, hj'j⟩ := P.exists_free_ne_ne hJ i j
  obtain ⟨C₁, hC₁, hψ₁⟩ := P.exists_mem_freeRowCol_eq_single hR hN hB (Ne.symm hji)
  obtain ⟨C₂, hC₂, hψ₂⟩ := P.exists_mem_freeRowCol_eq_single hR hN hC₁ (Ne.symm hj'j)
  have h1 : (C₁ : Matrix (Fin n) (Fin n) K) (P.u 0) j = 1 := by
    rw [← freeRowCol_fst_apply, hψ₁]
    exact (Pi.single_eq_same _ _).trans hi1
  have h2 : (C₁ : Matrix (Fin n) (Fin n) K) j' (P.w 0) = 0 := by
    rw [← freeRowCol_snd_apply, hψ₁]
    exact Pi.single_eq_of_ne hj'i _
  rw [h1, h2, Pi.single_zero] at hψ₂
  exact P.exists_mem_freeRowCol_eq_single_zero_of hR hN hC₂ hψ₂ k

theorem card_le_of_forall_exists_freeRowCol (hK : Nat.card K = 2)
    {R' : Subgroup (SpecialLinearGroup (Fin n) K)} (hR : R' ≤ P.radical K)
    (hD : ∀ k : P.free, ∃ D ∈ R', P.freeRowCol D = (0, Pi.single k 1))
    (hE : ∀ k : P.free, ∃ E ∈ R', P.freeRowCol E = (Pi.single k 1, 0)) :
    2 ^ P.free.card * 2 ^ P.free.card ≤ Nat.card R' := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  let S : AddSubmonoid ((P.free → K) × (P.free → K)) :=
    { carrier := {p | ∃ B ∈ R', P.freeRowCol B = p}
      add_mem' := by
        rintro _ _ ⟨B, hB, rfl⟩ ⟨B', hB', rfl⟩
        exact ⟨B * B', mul_mem hB hB', P.freeRowCol_mul (hR hB) (hR hB')⟩
      zero_mem' := ⟨1, one_mem _, P.freeRowCol_one⟩ }
  have h01 : ∀ x : K, x = 0 ∨ x = 1 := fun x => by
    by_cases hx : x = 0
    · exact Or.inl hx
    · exact Or.inr (eq_one_of_ne_zero_of_natCard_eq_two_aux hK hx)
  have hfst : ∀ x : P.free → K, (x, (0 : P.free → K)) ∈ S := by
    intro x
    have hx : (x, (0 : P.free → K)) = ∑ k, (Pi.single k (x k), (0 : P.free → K)) := by
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_sum]
        exact (Finset.univ_sum_single x).symm
      · rw [Prod.snd_sum, Finset.sum_const_zero]
    rw [hx]
    refine AddSubmonoid.sum_mem S fun k _ => ?_
    rcases h01 (x k) with h | h
    · rw [h, Pi.single_zero]
      exact S.zero_mem
    · rw [h]
      exact hE k
  have hsnd : ∀ y : P.free → K, ((0 : P.free → K), y) ∈ S := by
    intro y
    have hy : ((0 : P.free → K), y) = ∑ k, ((0 : P.free → K), Pi.single k (y k)) := by
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_sum, Finset.sum_const_zero]
      · rw [Prod.snd_sum]
        exact (Finset.univ_sum_single y).symm
    rw [hy]
    refine AddSubmonoid.sum_mem S fun k _ => ?_
    rcases h01 (y k) with h | h
    · rw [h, Pi.single_zero]
      exact S.zero_mem
    · rw [h]
      exact hD k
  have hsurj : Function.Surjective
      (fun B : R' => P.freeRowCol (B : SpecialLinearGroup (Fin n) K)) := by
    rintro ⟨x, y⟩
    have hxy : (x, y) ∈ S := by
      have hsplit : (x, y) = (x, (0 : P.free → K)) + ((0 : P.free → K), y) :=
        Prod.ext (add_zero x).symm (zero_add y).symm
      rw [hsplit]
      exact S.add_mem (hfst x) (hsnd y)
    obtain ⟨B, hB, hBp⟩ := hxy
    exact ⟨⟨B, hB⟩, hBp⟩
  have h := Nat.card_le_card_of_surjective _ hsurj
  rwa [Nat.card_prod, Nat.card_fun, hK, Nat.card_eq_fintype_card, Fintype.card_coe] at h

theorem freeRowCol_snd_eq_zero_or_fst_eq_zero [CharP K 2] (hK : Nat.card K = 2)
    (hJ : 3 ≤ P.free.card) {R' : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hR : R' ≤ P.radical K)
    (hN : ∀ (i j : Fin n) (hij : i ≠ j), i ∈ P.free → j ∈ P.free → ∀ B ∈ R',
      Matrix.SpecialLinearGroup.transvection hij (1 : K) * B *
        (Matrix.SpecialLinearGroup.transvection hij (1 : K))⁻¹ ∈ R')
    (hcard : Nat.card R' < 2 ^ P.free.card * 2 ^ P.free.card) :
    (∀ B ∈ R', (P.freeRowCol B).2 = 0) ∨ (∀ B ∈ R', (P.freeRowCol B).1 = 0) := by
  by_contra hne
  push Not at hne
  obtain ⟨⟨B₁, hB₁, h₁⟩, ⟨B₂, hB₂, h₂⟩⟩ := hne
  obtain ⟨j, hj⟩ := Function.ne_iff.1 h₁
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h₂
  exact absurd (P.card_le_of_forall_exists_freeRowCol hK hR
    (P.exists_mem_freeRowCol_eq_zero_single hK hJ hR hN hB₁ hj)
    (P.exists_mem_freeRowCol_eq_single_zero hK hJ hR hN hB₂ hi)) (not_le.2 hcard)

end InvPlacement

end CFSG.SeitzReduction.LinearPilot
