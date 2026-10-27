module

public import CFSG.Dihedral.Glauberman.DicksonMaxCases

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

namespace Lemma18iii

open Subgroup Matrix CFSG CFSG.PSL2Table CFSG.Glauberman.Dickson CFSG.Glauberman.Dickson.MaxTrace
  CFSG.BenderSuzuki.MatrixGroups
open scoped MatrixGroups commutatorElement Pointwise

section Matrices

variable {F : Type} [Field F]

theorem sq_eq (A : Matrix (Fin 2) (Fin 2) F) :
    A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem det_comm_eq (A B : SL(2, F)) :
    ((A : Matrix (Fin 2) (Fin 2) F) * B - B * A).det =
      2 - ((⁅A, B⁆ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace := by
  have h2 : ((⁅A, B⁆ : SL(2, F)) * (B * A) : SL(2, F)) = A * B := by
    rw [commutatorElement_def]; group
  have h3 := congrArg (fun X : SL(2, F) => (X : Matrix (Fin 2) (Fin 2) F)) h2
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h3
  have h1 : ((A : Matrix (Fin 2) (Fin 2) F) * B - B * A) =
      (((⁅A, B⁆ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) - 1) *
        ((B : Matrix (Fin 2) (Fin 2) F) * A) := by
    rw [sub_mul, h3, one_mul]
  rw [h1, Matrix.det_mul, Matrix.det_mul, A.2, B.2, mul_one, mul_one, Matrix.det_fin_two,
    Matrix.trace_fin_two]
  have hdet := ((⁅A, B⁆ : SL(2, F))).2
  rw [Matrix.det_fin_two] at hdet
  simp [Matrix.sub_apply]
  linear_combination hdet

theorem det_comm_mem_of_mk_commute {A B : SL(2, F)} (h : mk A * mk B = mk B * mk A) :
    ((A : Matrix (Fin 2) (Fin 2) F) * B - B * A).det = 0 ∨
      ((A : Matrix (Fin 2) (Fin 2) F) * B - B * A).det = 4 := by
  have h' : mk (A * B) = mk (B * A) := by rw [map_mul, map_mul, h]
  rcases (mk_eq_mk_iff _ _).1 h' with h1 | h1
  · left
    have := congrArg (fun X : SL(2, F) => (X : Matrix (Fin 2) (Fin 2) F)) h1
    simp only [Matrix.SpecialLinearGroup.coe_mul] at this
    rw [this, sub_self, Matrix.det_zero]
  · right
    have := congrArg (fun X : SL(2, F) => (X : Matrix (Fin 2) (Fin 2) F)) h1
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg] at this
    rw [this, sub_neg_eq_add, ← two_smul F, Matrix.det_smul, Matrix.det_mul, A.2, B.2]
    norm_num

theorem eq_zero_of_scalar_sq {N : Matrix (Fin 2) (Fin 2) F} {c : F} (hN : N = c • 1)
    (hN2 : N * N = 0) : N = 0 := by
  have : c ^ 2 = 0 := by
    have h := congrArg (fun X : Matrix (Fin 2) (Fin 2) F => X 0 0) hN2
    subst hN
    simpa [pow_two] using h
  have hc : c = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 this
  rw [hN, hc, zero_smul]

theorem natCast_eq_zero_of_pow {C : SL(2, F)} {ε : F} (hε : ε ^ 2 = 1)
    (hτ : (C : Matrix (Fin 2) (Fin 2) F).trace = 2 * ε)
    (hne : (C : Matrix (Fin 2) (Fin 2) F) ≠ ε • 1) {k : ℕ} {δ : F}
    (hk : (C : Matrix (Fin 2) (Fin 2) F) ^ k = δ • (1 : Matrix (Fin 2) (Fin 2) F)) :
    (k : F) = 0 := by
  set M : Matrix (Fin 2) (Fin 2) F := (C : Matrix (Fin 2) (Fin 2) F) with hM
  have hdet : M.det = 1 := C.2
  have hCH := sq_eq M
  rw [hdet, hτ] at hCH
  set N : Matrix (Fin 2) (Fin 2) F := M - ε • 1 with hN
  have hMN : M = ε • 1 + N := by rw [hN]; abel
  have hN2 : N * N = 0 := by
    have h1 : N * N = M * M - (2 * ε) • M + (ε ^ 2) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [hN]
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      module
    rw [h1, hCH, hε]
    module
  have hNne : N ≠ 0 := by
    intro h
    apply hne
    rw [hMN, h, add_zero]
  have hpow : ∀ n : ℕ, M ^ n = (ε ^ n) • (1 : Matrix (Fin 2) (Fin 2) F) +
      ((n : F) * ε ^ (n + 1)) • N := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih, hMN]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hN2,
        smul_zero, add_zero]
      push_cast
      match_scalars
      · linear_combination (ε ^ (n + 1)) * hε
      · linear_combination (-ε ^ n) * hε
  rw [hpow k] at hk
  by_contra hk0
  have hεk : ((k : F) * ε ^ (k + 1)) ≠ 0 := by
    have hε0 : ε ≠ 0 := by
      rintro rfl
      simp at hε
    exact mul_ne_zero hk0 (pow_ne_zero _ hε0)
  have : N = (((k : F) * ε ^ (k + 1))⁻¹ * (δ - ε ^ k)) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have h2 : ((k : F) * ε ^ (k + 1)) • N = (δ - ε ^ k) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [sub_smul]
      rw [← sub_eq_zero] at hk ⊢
      rw [← hk]
      module
    rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hεk, one_smul]
  exact hNne (eq_zero_of_scalar_sq this hN2)

theorem trace_eq_of_pow {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) (C : SL(2, F)) {ε : F}
    (hε : ε ^ 2 = 1)
    (hC : (C : Matrix (Fin 2) (Fin 2) F) ^ p = ε • (1 : Matrix (Fin 2) (Fin 2) F)) :
    (C : Matrix (Fin 2) (Fin 2) F).trace = 2 * ε := by
  set M : Matrix (Fin 2) (Fin 2) F := (C : Matrix (Fin 2) (Fin 2) F) with hM
  have hdet : M.det = 1 := C.2
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hεp : ε ^ p = ε := by
    obtain ⟨j, hj⟩ := hpodd
    rw [hj, pow_succ, pow_mul, hε, one_pow, one_mul]
  set N : Matrix (Fin 2) (Fin 2) F := M - ε • 1 with hN
  have hNp : N ^ p = 0 := by
    have hcomm : Commute M (ε • (1 : Matrix (Fin 2) (Fin 2) F)) :=
      (Commute.one_right M).smul_right ε
    have := sub_pow_char_of_commute p hcomm
    rw [hN, this, hC, smul_pow, one_pow, hεp, sub_self]
  have hdetN : N.det = 0 := by
    have h1 : N.det ^ p = 0 := by rw [← Matrix.det_pow, hNp, Matrix.det_zero]
    exact pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.1 h1
  have hCHN := sq_eq N
  rw [hdetN, zero_smul, sub_zero] at hCHN
  have hpowN : ∀ n : ℕ, N ^ (n + 1) = (N.trace ^ n) • N := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih, smul_mul_assoc, hCHN, smul_smul, ← pow_succ]
  have hN2 : N * N = 0 := by
    obtain ⟨k, hk⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := (Fact.out : p.Prime).pos; omega⟩
    have hk0 : k ≠ 0 := by
      have := (Fact.out : p.Prime).two_le
      omega
    rw [hk, hpowN] at hNp
    rcases smul_eq_zero.1 hNp with h | h
    · have h' : N.trace = 0 := (pow_eq_zero_iff hk0).1 h
      rw [hCHN, h', zero_smul]
    · rw [h, zero_mul]
  have hCHM := sq_eq M
  rw [hdet] at hCHM
  have h2 : N * N = M * M - (2 * ε) • M + (ε ^ 2) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [hN]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    module
  rw [hN2, hCHM, hε] at h2
  have h1 : (M.trace - 2 * ε) • M = 0 := by
    calc (M.trace - 2 * ε) • M
        = (M.trace • M - (1 : F) • (1 : Matrix (Fin 2) (Fin 2) F)) - (2 * ε) • M +
            (1 : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by module
      _ = 0 := h2.symm
  have hM0 : M ≠ 0 := by
    intro h
    rw [h, Matrix.det_zero] at hdet
    exact zero_ne_one hdet
  rcases smul_eq_zero.1 h1 with h | h
  · linear_combination h
  · exact absurd h hM0

end Matrices

section Orders

variable {F : Type} [Field F]

theorem coe_ne_smul_one {C : SL(2, F)} (hC1 : C ≠ 1) (hC2 : C ≠ -1) {ε : F}
    (hε : ε = 1 ∨ ε = -1) : (C : Matrix (Fin 2) (Fin 2) F) ≠ ε • 1 := by
  rcases hε with rfl | rfl
  · intro h
    apply hC1
    apply Subtype.ext
    simpa using h
  · intro h
    apply hC2
    apply Subtype.ext
    simpa using h

theorem natCast_eq_zero_of_pow' {C : SL(2, F)} (hC1 : C ≠ 1) (hC2 : C ≠ -1)
    (h4 : (C : Matrix (Fin 2) (Fin 2) F).trace ^ 2 = 4) {k : ℕ}
    (hk : C ^ k = 1 ∨ C ^ k = -1) : (k : F) = 0 := by
  have h2 : ((C : Matrix (Fin 2) (Fin 2) F).trace - 2) *
      ((C : Matrix (Fin 2) (Fin 2) F).trace + 2) = 0 := by linear_combination h4
  have hk' : ∃ δ : F, (δ = 1 ∨ δ = -1) ∧
      (C : Matrix (Fin 2) (Fin 2) F) ^ k = δ • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rcases hk with hk | hk
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [← Matrix.SpecialLinearGroup.coe_pow, hk]; simp
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [← Matrix.SpecialLinearGroup.coe_pow, hk]; simp
  obtain ⟨δ, -, hδ⟩ := hk'
  rcases mul_eq_zero.1 h2 with h2 | h2
  · exact natCast_eq_zero_of_pow (ε := 1) (by norm_num)
      (by linear_combination h2) (coe_ne_smul_one hC1 hC2 (Or.inl rfl)) hδ
  · exact natCast_eq_zero_of_pow (ε := -1) (by norm_num)
      (by linear_combination h2) (coe_ne_smul_one hC1 hC2 (Or.inr rfl)) hδ

theorem mk_pow_ne_one {C : SL(2, F)} (hC1 : C ≠ 1) (hC2 : C ≠ -1) {n : ℕ}
    (htr : (chAB (C : Matrix (Fin 2) (Fin 2) F).trace n).1 ≠ 0)
    (hn : ((n + 1 : ℕ) : F) ≠ 0 ∨ (C : Matrix (Fin 2) (Fin 2) F).trace ^ 2 ≠ 4) :
    mk C ^ (n + 1) ≠ 1 := by
  intro h
  rcases trace_cond_of_pow C n (pow_lift h) with h0 | h4
  · exact htr h0
  · rcases hn with hn | hn
    · exact hn (natCast_eq_zero_of_pow' hC1 hC2 h4 (pow_lift h))
    · exact hn h4

theorem mk_sq_ne_one (h2 : (2 : F) ≠ 0) {C : SL(2, F)} (hC1 : C ≠ 1) (hC2 : C ≠ -1)
    (hτ : (C : Matrix (Fin 2) (Fin 2) F).trace ≠ 0) : mk C ^ 2 ≠ 1 :=
  mk_pow_ne_one (n := 1) hC1 hC2 (by rw [chAB_one]; exact hτ)
    (Or.inl (by norm_num; exact h2))

theorem mk_cube_ne_one {C : SL(2, F)} (hC1 : C ≠ 1) (hC2 : C ≠ -1)
    (hτ : (C : Matrix (Fin 2) (Fin 2) F).trace ^ 2 - 1 ≠ 0) : mk C ^ 3 ≠ 1 := by
  refine mk_pow_ne_one (n := 2) hC1 hC2 (by rw [chAB_two]; exact hτ) ?_
  by_cases h4 : (C : Matrix (Fin 2) (Fin 2) F).trace ^ 2 = 4
  · left
    have : ((2 + 1 : ℕ) : F) = (C : Matrix (Fin 2) (Fin 2) F).trace ^ 2 - 1 := by
      push_cast; rw [h4]; norm_num
    rw [this]; exact hτ
  · right; exact h4

theorem mk_pow5_ne_one {C : SL(2, F)} (hC1 : C ≠ 1) (hC2 : C ≠ -1)
    (hτ : (C : Matrix (Fin 2) (Fin 2) F).trace ^ 4 - 3 * (C : Matrix (Fin 2) (Fin 2) F).trace ^ 2 + 1
      ≠ 0) : mk C ^ 5 ≠ 1 := by
  refine mk_pow_ne_one (n := 4) hC1 hC2 (by rw [chAB_four]; exact hτ) ?_
  by_cases h4 : (C : Matrix (Fin 2) (Fin 2) F).trace ^ 2 = 4
  · left
    have h16 : (C : Matrix (Fin 2) (Fin 2) F).trace ^ 4 = 16 := by
      calc (C : Matrix (Fin 2) (Fin 2) F).trace ^ 4
          = ((C : Matrix (Fin 2) (Fin 2) F).trace ^ 2) ^ 2 := by ring
        _ = 16 := by rw [h4]; norm_num
    have : ((4 + 1 : ℕ) : F) = (C : Matrix (Fin 2) (Fin 2) F).trace ^ 4 -
        3 * (C : Matrix (Fin 2) (Fin 2) F).trace ^ 2 + 1 := by
      push_cast; rw [h16, h4]; norm_num
    rw [this]; exact hτ
  · right; exact h4

theorem mul_ne_pm_one {A B : SL(2, F)}
    (hD0 : ((A : Matrix (Fin 2) (Fin 2) F) * B - B * A).det ≠ 0) :
    A * B ≠ 1 ∧ A * B ≠ -1 := by
  constructor
  · intro h
    apply hD0
    have h1 : (A : Matrix (Fin 2) (Fin 2) F) * B = 1 := by
      have := congrArg (fun X : SL(2, F) => (X : Matrix (Fin 2) (Fin 2) F)) h
      simpa using this
    have h2 : (B : Matrix (Fin 2) (Fin 2) F) * A = 1 := (Matrix.mul_eq_one_comm_of_card_eq (Fin 2) (Fin 2) F rfl).mp h1
    rw [h1, h2, sub_self, Matrix.det_zero]
  · intro h
    apply hD0
    have h1 : (A : Matrix (Fin 2) (Fin 2) F) * B = -1 := by
      have := congrArg (fun X : SL(2, F) => (X : Matrix (Fin 2) (Fin 2) F)) h
      simpa using this
    have h3 : (A : Matrix (Fin 2) (Fin 2) F) * (-(B : Matrix (Fin 2) (Fin 2) F)) = 1 := by
      rw [Matrix.mul_neg, h1, neg_neg]
    have h2 : (-(B : Matrix (Fin 2) (Fin 2) F)) * A = 1 := (Matrix.mul_eq_one_comm_of_card_eq (Fin 2) (Fin 2) F rfl).mp h3
    have h4 : (B : Matrix (Fin 2) (Fin 2) F) * A = -1 := by
      rw [Matrix.neg_mul] at h2
      exact neg_eq_iff_eq_neg.1 h2
    rw [h1, h4, sub_self, Matrix.det_zero]

theorem mk_mul_orders {p : ℕ} [Fact p.Prime] (h2 : (2 : F) ≠ 0) {A B : SL(2, F)}
    (hD0 : ((A : Matrix (Fin 2) (Fin 2) F) * B - B * A).det ≠ 0)
    (hτ2 : ((A * B : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace ≠ 0)
    (hτ3 : ((A * B : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace ^ 2 - 1 ≠ 0)
    (hτ5 : p = 5 ∨ ((A * B : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace ^ 4 -
      3 * ((A * B : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace ^ 2 + 1 ≠ 0) :
    mk (A * B) ≠ 1 ∧ mk (A * B) ^ 2 ≠ 1 ∧ mk (A * B) ^ 3 ≠ 1 ∧
      (p ≠ 5 → mk (A * B) ^ 5 ≠ 1) := by
  obtain ⟨hC1, hC2⟩ := mul_ne_pm_one hD0
  refine ⟨?_, mk_sq_ne_one h2 hC1 hC2 hτ2, mk_cube_ne_one hC1 hC2 hτ3, fun hp5 => ?_⟩
  · intro h
    rcases (mk_eq_one_iff _).1 h with h | h
    · exact hC1 h
    · exact hC2 h
  · exact mk_pow5_ne_one hC1 hC2 (hτ5.resolve_left hp5)

end Orders

section Groups

theorem dihedral_odd_commute {n : ℕ} (x y : DihedralGroup n) (hx : Odd (orderOf x))
    (hy : Odd (orderOf y)) : x * y = y * x := by
  have hr : ∀ z : DihedralGroup n, Odd (orderOf z) → ∃ i, z = DihedralGroup.r i := by
    intro z hz
    cases z with
    | r i => exact ⟨i, rfl⟩
    | sr i =>
      exfalso
      rw [DihedralGroup.orderOf_sr] at hz
      exact absurd hz (by decide)
  obtain ⟨i, rfl⟩ := hr x hx
  obtain ⟨j, rfl⟩ := hr y hy
  simp [DihedralGroup.r_mul_r, add_comm]

theorem alt4_pow (x : alternatingGroup (Fin 4)) : x ^ 2 = 1 ∨ x ^ 3 = 1 := by
  revert x
  decide

theorem alt5_pow (x : alternatingGroup (Fin 5)) : x ^ 2 = 1 ∨ x ^ 3 = 1 ∨ x ^ 5 = 1 := by
  revert x
  decide +kernel

theorem not_index_two {Q : Type*} [Group Q] (a b : Q) (ha : Odd (orderOf a)) (hb : Odd (orderOf b))
    (N : Subgroup ↥(Subgroup.closure ({a, b} : Set Q))) (hN : N.index = 2) : False := by
  have hodd : ∀ g : Q, Odd (orderOf g) → ∀ hg : g ∈ Subgroup.closure ({a, b} : Set Q),
      (⟨g, hg⟩ : ↥(Subgroup.closure ({a, b} : Set Q))) ∈ N := by
    intro g hg hgc
    obtain ⟨m, hm⟩ := hg
    set x : ↥(Subgroup.closure ({a, b} : Set Q)) := ⟨g, hgc⟩ with hx
    have hxo : orderOf x = orderOf g := Subgroup.orderOf_mk g hgc
    have hgm : x ^ (2 * m + 1) = 1 := by rw [← hm, ← hxo]; exact pow_orderOf_eq_one x
    have h1 : x = (x ^ (m + 1)) ^ 2 := by
      calc x = x ^ (2 * m + 1) * x := by rw [hgm, one_mul]
        _ = (x ^ (m + 1)) ^ 2 := by rw [← pow_succ, ← pow_mul]; ring_nf
    rw [h1]
    exact Subgroup.sq_mem_of_index_two hN _
  have ha' := hodd a ha (Subgroup.subset_closure (by simp))
  have hb' := hodd b hb (Subgroup.subset_closure (by simp))
  have htop : N = ⊤ := by
    rw [eq_top_iff]
    have hcl : Subgroup.closure ((Subtype.val : ↥(Subgroup.closure ({a, b} : Set Q)) → Q) ⁻¹'
        ({a, b} : Set Q)) = ⊤ := Subgroup.closure_closure_coe_preimage
    rw [← hcl, Subgroup.closure_le]
    intro g hg
    rcases hg with hg | hg
    · have : g = ⟨a, Subgroup.subset_closure (by simp)⟩ := Subtype.ext hg
      rw [this]; exact ha'
    · have : g = ⟨b, Subgroup.subset_closure (by simp)⟩ := Subtype.ext hg
      rw [this]; exact hb'
  rw [htop, Subgroup.index_top] at hN
  omega

theorem commutator_mem_of_sup_cyclic {G : Type*} [Group G] (E C : Subgroup G) [E.Normal]
    (hC : IsCyclic C) (hsup : E ⊔ C = ⊤) (x y : G) : ⁅x, y⁆ ∈ E := by
  have hmem : ∀ x : G, ∃ c ∈ C, (x : G ⧸ E) = (c : G ⧸ E) := by
    intro x
    have hx : x ∈ (E : Set G) * (C : Set G) := by
      rw [← Subgroup.normal_mul, hsup]
      exact Set.mem_univ x
    obtain ⟨e, he, c, hc, rfl⟩ := hx
    refine ⟨c, hc, ?_⟩
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff e).mpr he, one_mul]
  have hcyc : IsCyclic (G ⧸ E) :=
    isCyclic_of_surjective ((QuotientGroup.mk' E).comp C.subtype) (by
      intro q
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨c, hc, h⟩ := hmem m
      exact ⟨⟨c, hc⟩, h.symm⟩)
  have hcomm := (IsCyclic.isMulCommutative (α := G ⧸ E)).is_comm.comm
  rw [← QuotientGroup.eq_one_iff]
  change (QuotientGroup.mk' E) ⁅x, y⁆ = 1
  rw [map_commutatorElement, commutatorElement_def,
    hcomm (QuotientGroup.mk' E x) (QuotientGroup.mk' E y), mul_inv_cancel_right, mul_inv_cancel]

end Groups

section Main

variable {F : Type} [Field F] [Finite F]

theorem closure_pair_iso
    {p f : ℕ} [Fact p.Prime] [CharP F p] (hF : Nat.card F = p ^ f)
    (hp2 : p ≠ 2) (A B : SL(2, F))
    (hAo : Odd (orderOf (mk A))) (hBo : Odd (orderOf (mk B)))
    (hD0 : ((A : Matrix (Fin 2) (Fin 2) F) * B - B * A).det ≠ 0)
    (hD4 : ((A : Matrix (Fin 2) (Fin 2) F) * B - B * A).det ≠ 4)
    (hx : ∃ x ∈ Subgroup.closure ({mk A, mk B} : Set (PSL(2, F))),
      x ≠ 1 ∧ x ^ 2 ≠ 1 ∧ x ^ 3 ≠ 1 ∧ (p ≠ 5 → x ^ 5 ≠ 1)) :
    ∃ m : ℕ, m ∣ f ∧ Nonempty (Subgroup.closure ({mk A, mk B} : Set (PSL(2, F))) ≃*
      PSL2MatrixGroup (GaloisField p m)) := by
  classical
  set G : Subgroup (PSL(2, F)) := Subgroup.closure ({mk A, mk B} : Set (PSL(2, F))) with hG
  have haG : mk A ∈ G := Subgroup.subset_closure (by simp)
  have hbG : mk B ∈ G := Subgroup.subset_closure (by simp)
  set a' : ↥G := ⟨mk A, haG⟩ with ha'
  set b' : ↥G := ⟨mk B, hbG⟩ with hb'
  have hnc : mk A * mk B ≠ mk B * mk A := fun h => by
    rcases det_comm_mem_of_mk_commute h with h0 | h4
    · exact hD0 h0
    · exact hD4 h4
  have hnc' : a' * b' ≠ b' * a' := fun h => hnc (congrArg Subtype.val h)
  have hao' : Odd (orderOf a') := by rw [ha', Subgroup.orderOf_mk]; exact hAo
  have hbo' : Odd (orderOf b') := by rw [hb', Subgroup.orderOf_mk]; exact hBo
  obtain ⟨x, hxG, hx1, hx2, hx3, hx5⟩ := hx
  set x' : ↥G := ⟨x, hxG⟩ with hx'
  rcases dickson_psl2_subgroup_list hF G with
    ⟨m, hm, hcard, hel⟩ | ⟨z, -, hcard, hcyc⟩ | ⟨z, hz2, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨h5, ⟨e⟩⟩ |
    ⟨m, t, hm1, hmf, htm, htq, E, C, hE, hEel, hEcard, hCcyc, hCcard, hdisj, hsup, hfaith, -⟩ |
    ⟨m, hmf, ⟨e⟩⟩ | ⟨m, hmf, ⟨e⟩⟩
  ·
    exfalso
    have := hel.toIsMulCommutative
    exact hnc' (IsMulCommutative.is_comm.comm a' b')
  ·
    exfalso
    have : IsMulCommutative ↥G := IsCyclic.isMulCommutative
    exact hnc' (IsMulCommutative.is_comm.comm a' b')
  ·
    exfalso
    have h1 : Odd (orderOf (e a')) := by rw [MulEquiv.orderOf_eq]; exact hao'
    have h2 : Odd (orderOf (e b')) := by rw [MulEquiv.orderOf_eq]; exact hbo'
    exact hnc' (e.injective (by rw [map_mul, map_mul]; exact dihedral_odd_commute _ _ h1 h2))
  ·
    exfalso
    rcases alt4_pow (e x') with h | h
    · apply hx2
      have : x' ^ 2 = 1 := e.injective (by rw [map_pow, map_one]; exact h)
      exact congrArg Subtype.val this
    · apply hx3
      have : x' ^ 3 = 1 := e.injective (by rw [map_pow, map_one]; exact h)
      exact congrArg Subtype.val this
  ·
    exfalso
    have hidx : ((alternatingGroup (Fin 4)).comap e.toMonoidHom).index = 2 := by
      rw [Subgroup.index_comap_of_surjective _ e.surjective]
      exact alternatingGroup.index_eq_two
    exact not_index_two (mk A) (mk B) hAo hBo _ hidx
  ·
    by_cases hp5 : p = 5
    · subst hp5
      obtain ⟨e5⟩ := CFSG.Glauberman.Dickson.MaxCases.nonempty_psl2_galoisField_five
      have hf0 : f ≠ 0 := by
        rintro rfl
        have : Nat.card F = 1 := by rw [hF]; simp
        have h1 : 1 < Nat.card F := Finite.one_lt_card
        omega
      exact ⟨1, one_dvd _, ⟨e.trans e5.symm⟩⟩
    · exfalso
      rcases alt5_pow (e x') with h | h | h
      · apply hx2
        have : x' ^ 2 = 1 := e.injective (by rw [map_pow, map_one]; exact h)
        exact congrArg Subtype.val this
      · apply hx3
        have : x' ^ 3 = 1 := e.injective (by rw [map_pow, map_one]; exact h)
        exact congrArg Subtype.val this
      · apply hx5 hp5
        have : x' ^ 5 = 1 := e.injective (by rw [map_pow, map_one]; exact h)
        exact congrArg Subtype.val this
  ·
    exfalso
    have : E.Normal := hE
    have := hEel
    have hcomm := commutator_mem_of_sup_cyclic E C hCcyc hsup a' b'
    have hpow := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) _ hcomm
    have hpow' : (⁅mk A, mk B⁆ : PSL(2, F)) ^ p = 1 := by
      have := congrArg Subtype.val hpow
      simpa [ha', hb', commutatorElement_def] using this
    have hmk : mk (⁅A, B⁆ ^ p) = 1 := by
      rw [map_pow, map_commutatorElement]; exact hpow'
    rcases (mk_eq_one_iff _).1 hmk with h | h
    · have htr := trace_eq_of_pow hp2 ⁅A, B⁆ (ε := 1) (by norm_num) (by
        have := congrArg (fun X : SL(2, F) => (X : Matrix (Fin 2) (Fin 2) F)) h
        simpa using this)
      apply hD0
      rw [det_comm_eq, htr]; norm_num
    · have htr := trace_eq_of_pow hp2 ⁅A, B⁆ (ε := -1) (by norm_num) (by
        have := congrArg (fun X : SL(2, F) => (X : Matrix (Fin 2) (Fin 2) F)) h
        simpa using this)
      apply hD4
      rw [det_comm_eq, htr]; norm_num
  ·
    exact ⟨m, hmf, ⟨e⟩⟩
  ·
    exfalso
    have hneg : (-1 : GaloisField p m) ≠ 1 := by
      apply Ring.neg_one_ne_one_of_char_ne_two
      rw [ringChar.eq (GaloisField p m) p]
      exact hp2
    have hidx : ((h826_pslToPGL (K := GaloisField p m)).range.comap e.toMonoidHom).index = 2 := by
      rw [Subgroup.index_comap_of_surjective _ e.surjective]
      exact h826_pslToPGL_range_index_eq_two hneg
    exact not_index_two (mk A) (mk B) hAo hBo _ hidx

end Main

end Lemma18iii

end CFSG.GH74.GLS.IVK.Proofs2
