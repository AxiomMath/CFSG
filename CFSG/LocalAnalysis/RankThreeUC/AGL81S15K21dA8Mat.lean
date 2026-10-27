module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF1Borel

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21dA8Proof

open CFSG.Quasithin.H13.C1294

abbrev SL4 : Type := Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)

abbrev M4 : Type := Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)

@[expose] def Mu (a b c d e f : ZMod 2) : M4 :=
  !![1, a, b, c; 0, 1, d, e; 0, 0, 1, f; 0, 0, 0, 1]

theorem upperSub_diag {g : SL4} (hg : g ∈ upperSub) (i : Fin (3 + 1)) : (g : M4) i i = 1 := by
  rw [ub_mem_iff] at hg
  have hut : (g : M4).IsUpperTriangular := fun ⦃i j⦄ h => hg i j h
  have hdet := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_of_isUpperTriangular hut, Fin.prod_univ_four] at hdet
  have key : ∀ w x y z : ZMod 2, w * x * y * z = 1 → w = 1 ∧ x = 1 ∧ y = 1 ∧ z = 1 := by decide
  obtain ⟨h0, h1, h2, h3⟩ := key _ _ _ _ hdet
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem upperSub_param {g : SL4} (hg : g ∈ upperSub) :
    (g : M4) = Mu (g 0 1) (g 0 2) (g 0 3) (g 1 2) (g 1 3) (g 2 3) := by
  have hd := upperSub_diag hg
  rw [ub_mem_iff] at hg
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Mu, hd 0, hd 1, hd 2, hd 3, hg 1 0 (by decide), hg 2 0 (by decide),
      hg 3 0 (by decide), hg 2 1 (by decide), hg 3 1 (by decide), hg 3 2 (by decide)]

abbrev B2 : Type := Matrix (Fin 2) (Fin 2) (ZMod 2)

@[expose] def ofBl (A B C : B2) : M4 :=
  !![A 0 0, A 0 1, B 0 0, B 0 1; A 1 0, A 1 1, B 1 0, B 1 1;
     0, 0, C 0 0, C 0 1; 0, 0, C 1 0, C 1 1]

@[expose] def blkA (M : M4) : B2 := !![M 0 0, M 0 1; M 1 0, M 1 1]

@[expose] def blkB (M : M4) : B2 := !![M 0 2, M 0 3; M 1 2, M 1 3]

@[expose] def blkC (M : M4) : B2 := !![M 2 2, M 2 3; M 3 2, M 3 3]

theorem blkA_ofBl (A B C : B2) : blkA (ofBl A B C) = A := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [blkA, ofBl]

theorem blkB_ofBl (A B C : B2) : blkB (ofBl A B C) = B := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [blkB, ofBl]

theorem blkC_ofBl (A B C : B2) : blkC (ofBl A B C) = C := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [blkC, ofBl]

theorem ofBl_inj {A B C A' B' C' : B2} (h : ofBl A B C = ofBl A' B' C') :
    A = A' ∧ B = B' ∧ C = C' :=
  ⟨by rw [← blkA_ofBl A B C, h, blkA_ofBl], by rw [← blkB_ofBl A B C, h, blkB_ofBl],
    by rw [← blkC_ofBl A B C, h, blkC_ofBl]⟩

theorem ofBl_mul (A B C A' B' C' : B2) :
    ofBl A B C * ofBl A' B' C' = ofBl (A * A') (A * B' + B * C') (C * C') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ofBl, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two] <;> ring

theorem ofBl_one : ofBl 1 0 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ofBl]

theorem det_ofBl (A B C : B2) : (ofBl A B C).det = A.det * C.det := by
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, ofBl, Matrix.det_fin_two,
    Matrix.det_fin_three]
  simp [Fin.succAbove, Matrix.submatrix]
  ring

@[expose] def R3 : Fin 3 → B2
  | 0 => 1
  | 1 => !![0, 1; 1, 1]
  | 2 => !![1, 1; 1, 0]

theorem R3_injective : Function.Injective R3 := by decide

theorem R3_mul : ∀ i j : Fin 3, ∃ k : Fin 3, R3 i * R3 j = R3 k := by decide

theorem R3_inv : ∀ i : Fin 3, ∃ k : Fin 3, R3 i * R3 k = 1 := by decide

theorem R3_det : ∀ i : Fin 3, (R3 i).det = 1 := by decide

theorem R3_conj : ∀ A : B2, A.det = 1 → ∀ i : Fin 3, ∃ k : Fin 3, A * R3 i = R3 k * A := by
  decide

theorem R3_conj' : ∀ A : B2, A.det = 1 → ∀ k : Fin 3, ∃ i : Fin 3, A * R3 i = R3 k * A := by
  decide

@[expose] def dg (A C : B2) (hA : A.det = 1) (hC : C.det = 1) : SL4 :=
  ⟨ofBl A 0 C, by rw [det_ofBl, hA, hC, mul_one]⟩

@[expose] def E0 : Subgroup SL4 where
  carrier := {g | ∃ i j : Fin 3, (g : M4) = ofBl (R3 i) 0 (R3 j)}
  one_mem' := ⟨0, 0, by rw [Matrix.SpecialLinearGroup.coe_one]; exact (ofBl_one).symm⟩
  mul_mem' := by
    rintro g h ⟨i, j, hg⟩ ⟨i', j', hh⟩
    obtain ⟨k, hk⟩ := R3_mul i i'
    obtain ⟨l, hl⟩ := R3_mul j j'
    exact ⟨k, l, by rw [Matrix.SpecialLinearGroup.coe_mul, hg, hh, ofBl_mul, hk, hl]; simp⟩
  inv_mem' := by
    rintro g ⟨i, j, hg⟩
    obtain ⟨k, hk⟩ := R3_inv i
    obtain ⟨l, hl⟩ := R3_inv j
    have h1 : g * dg (R3 k) (R3 l) (R3_det k) (R3_det l) = 1 := by
      apply Matrix.SpecialLinearGroup.ext
      intro a b
      rw [Matrix.SpecialLinearGroup.coe_mul, hg]
      simp only [dg]
      rw [ofBl_mul, hk, hl]
      simp [← ofBl_one]
    refine ⟨k, l, ?_⟩
    rw [inv_eq_of_mul_eq_one_right h1]
    rfl

theorem dg_R3_mem_E0 (i j : Fin 3) : dg (R3 i) (R3 j) (R3_det i) (R3_det j) ∈ E0 :=
  ⟨i, j, rfl⟩

theorem card_E0 : Nat.card E0 = 9 := by
  have e : (Fin 3 × Fin 3) ≃ E0 := Equiv.ofBijective
    (fun p => ⟨dg (R3 p.1) (R3 p.2) (R3_det p.1) (R3_det p.2), dg_R3_mem_E0 p.1 p.2⟩)
    ⟨by
      rintro ⟨i, j⟩ ⟨i', j'⟩ h
      have h1 := congrArg (fun x : E0 => ((x : SL4) : M4)) h
      obtain ⟨hi, -, hj⟩ := ofBl_inj h1
      exact Prod.ext (R3_injective hi) (R3_injective hj),
    by
      rintro ⟨g, i, j, hg⟩
      refine ⟨(i, j), Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_)⟩
      show (ofBl (R3 i) 0 (R3 j)) a b = (g : M4) a b
      rw [hg]⟩
  rw [← Nat.card_congr e]
  simp

theorem mem_normalizer_E0 (n : SL4)
    (h1 : ∀ i j : Fin 3, ∃ i' j' : Fin 3,
      (n : M4) * ofBl (R3 i) 0 (R3 j) = ofBl (R3 i') 0 (R3 j') * n)
    (h2 : ∀ i' j' : Fin 3, ∃ i j : Fin 3,
      (n : M4) * ofBl (R3 i) 0 (R3 j) = ofBl (R3 i') 0 (R3 j') * n) :
    n ∈ Subgroup.normalizer (E0 : Set SL4) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨i, j, hg⟩
    obtain ⟨i', j', h⟩ := h1 i j
    refine ⟨i', j', ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hg, h,
      Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
  · rintro ⟨i', j', h'⟩
    obtain ⟨i, j, h⟩ := h2 i' j'
    refine ⟨i, j, ?_⟩
    have hZ : n * dg (R3 i) (R3 j) (R3_det i) (R3_det j) = (n * g * n⁻¹) * n := by
      apply Matrix.SpecialLinearGroup.ext
      intro a b
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, h', ← h]
      rfl
    have hg : g = dg (R3 i) (R3 j) (R3_det i) (R3_det j) := by
      have h3 : n * dg (R3 i) (R3 j) (R3_det i) (R3_det j) = n * g := by
        rw [hZ]
        group
      exact (mul_left_cancel h3).symm
    rw [hg]
    rfl

theorem dg_mem_normalizer (A C : B2) (hA : A.det = 1) (hC : C.det = 1) :
    dg A C hA hC ∈ Subgroup.normalizer (E0 : Set SL4) := by
  refine mem_normalizer_E0 _ ?_ ?_
  · intro i j
    obtain ⟨i', hi⟩ := R3_conj A hA i
    obtain ⟨j', hj⟩ := R3_conj C hC j
    refine ⟨i', j', ?_⟩
    show ofBl A 0 C * ofBl (R3 i) 0 (R3 j) = ofBl (R3 i') 0 (R3 j') * ofBl A 0 C
    rw [ofBl_mul, ofBl_mul, hi, hj]
    simp
  · intro i' j'
    obtain ⟨i, hi⟩ := R3_conj' A hA i'
    obtain ⟨j, hj⟩ := R3_conj' C hC j'
    refine ⟨i, j, ?_⟩
    show ofBl A 0 C * ofBl (R3 i) 0 (R3 j) = ofBl (R3 i') 0 (R3 j') * ofBl A 0 C
    rw [ofBl_mul, ofBl_mul, hi, hj]
    simp

@[expose] def Ta (a : ZMod 2) : B2 := !![1, a; 0, 1]

@[expose] def Bm (b c d e : ZMod 2) : B2 := !![b, c; d, e]

theorem Mu_eq_ofBl (a b c d e f : ZMod 2) : Mu a b c d e f = ofBl (Ta a) (Bm b c d e) (Ta f) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Mu, ofBl, Ta, Bm]

theorem ta_comm : ∀ a : ZMod 2, Ta a * R3 1 = R3 1 * Ta a → a = 0 := by decide

theorem ta_zero : ∀ i : Fin 3, Ta 0 * R3 1 = R3 i * Ta 0 → i = 1 := by decide

theorem bm_zero : ∀ b c d e : ZMod 2, Bm b c d e * R3 1 = R3 1 * Bm b c d e →
    Bm b c d e = R3 1 * Bm b c d e → b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 := by decide

theorem det_Ta (a : ZMod 2) : (Ta a).det = 1 := by
  simp [Ta, Matrix.det_fin_two]

@[expose] def eA : SL4 := dg (R3 1) (R3 0) (R3_det 1) (R3_det 0)

@[expose] def eAB : SL4 := dg (R3 1) (R3 1) (R3_det 1) (R3_det 1)

@[expose] def s2 : SL4 := dg 1 (Ta 1) Matrix.det_one (det_Ta 1)

theorem eA_mem : eA ∈ E0 := dg_R3_mem_E0 1 0

theorem eAB_mem : eAB ∈ E0 := dg_R3_mem_E0 1 1

theorem eq_one_of_commute_eAB {g : SL4} (hg : g ∈ upperSub)
    (hn : g ∈ Subgroup.normalizer (E0 : Set SL4))
    (hc : g ∈ Subgroup.centralizer ({eAB} : Set SL4)) : g = 1 := by
  have hp := upperSub_param hg
  rw [Mu_eq_ofBl] at hp
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  have hc' := congrArg (fun x : SL4 => (x : M4)) hc
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hc'
  rw [hp] at hc'
  change ofBl _ _ _ * ofBl (R3 1) 0 (R3 1) = ofBl (R3 1) 0 (R3 1) * ofBl _ _ _ at hc'
  rw [ofBl_mul, ofBl_mul] at hc'
  obtain ⟨hc1, hc2, hc3⟩ := ofBl_inj hc'
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero] at hc2
  obtain ⟨i, j, hij⟩ := (Subgroup.mem_normalizer_iff.1 hn eA).1 eA_mem
  have hn' : (g : M4) * (eA : M4) = ofBl (R3 i) 0 (R3 j) * (g : M4) := by
    have h3 : g * eA = (g * eA * g⁻¹) * g := by group
    rw [← hij, ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, ← h3]
  rw [hp] at hn'
  change ofBl _ _ _ * ofBl (R3 1) 0 (R3 0) = ofBl (R3 i) 0 (R3 j) * ofBl _ _ _ at hn'
  rw [ofBl_mul, ofBl_mul] at hn'
  obtain ⟨hn1, hn2, hn3⟩ := ofBl_inj hn'
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero] at hn2
  have ha : g 0 1 = 0 := ta_comm _ hc1
  have hf : g 2 3 = 0 := ta_comm _ hc3
  rw [ha] at hn1
  have hi : i = 1 := ta_zero i hn1
  subst hi
  have hB := bm_zero _ _ _ _ hc2 (by simpa [R3] using hn2)
  have e1 : Ta 0 = 1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [Ta]
  have e2 : Bm 0 0 0 0 = 0 := by ext i j; fin_cases i <;> fin_cases j <;> simp [Bm]
  have hg1 : (g : M4) = 1 := by
    rw [hp, ha, hf, hB.1, hB.2.1, hB.2.2.1, hB.2.2.2, e1, e2, ofBl_one]
  exact Matrix.SpecialLinearGroup.ext _ _ fun x y => by
    rw [hg1, Matrix.SpecialLinearGroup.coe_one]


theorem R3_zero : R3 0 = 1 := rfl

theorem eA_ne_one : eA ≠ 1 := by
  intro h
  have h1 := congrArg (fun x : SL4 => (x : M4)) h
  simp only [eA, dg, Matrix.SpecialLinearGroup.coe_one, R3_zero] at h1
  rw [← ofBl_one] at h1
  have := (ofBl_inj h1).1
  rw [← R3_zero] at this
  exact absurd (R3_injective this) (by decide)

theorem eAB_ne_one : eAB ≠ 1 := by
  intro h
  have h1 := congrArg (fun x : SL4 => (x : M4)) h
  simp only [eAB, dg, Matrix.SpecialLinearGroup.coe_one] at h1
  rw [← ofBl_one] at h1
  have := (ofBl_inj h1).1
  rw [← R3_zero] at this
  exact absurd (R3_injective this) (by decide)

theorem s2_ne_one : s2 ≠ 1 := by
  intro h
  have h1 := congrArg (fun x : SL4 => (x : M4)) h
  simp only [s2, dg, Matrix.SpecialLinearGroup.coe_one] at h1
  rw [← ofBl_one] at h1
  have := (ofBl_inj h1).2.2
  revert this
  decide

theorem s2_mem_upper : s2 ∈ upperSub := by
  rw [ub_mem_iff]
  intro i j hji
  fin_cases i <;> fin_cases j <;> simp_all [s2, dg, ofBl, Ta]

theorem s2_mem_normalizer : s2 ∈ Subgroup.normalizer (E0 : Set SL4) :=
  dg_mem_normalizer _ _ _ _

theorem s2_mem_centralizer : s2 ∈ Subgroup.centralizer ({eA} : Set SL4) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Matrix.SpecialLinearGroup.ext
  intro x y
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  show (ofBl 1 0 (Ta 1) * ofBl (R3 1) 0 (R3 0)) x y = (ofBl (R3 1) 0 (R3 0) * ofBl 1 0 (Ta 1)) x y
  rw [ofBl_mul, ofBl_mul]
  simp [R3_zero]


theorem ofBl_unip_lower (B : B2) : ∀ i j : Fin (3 + 1), j < i → (ofBl 1 B 1) i j = 0 := by
  intro i j hji
  fin_cases i <;> fin_cases j <;> simp_all [ofBl]

theorem eq_ofBl_of_zero {M : M4} (h20 : M 2 0 = 0) (h21 : M 2 1 = 0) (h30 : M 3 0 = 0)
    (h31 : M 3 1 = 0) : M = ofBl (blkA M) (blkB M) (blkC M) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofBl, blkA, blkB, blkC, h20, h21, h30, h31]

theorem decomp {d : SL4} (h20 : d 2 0 = 0) (h21 : d 2 1 = 0) (h30 : d 3 0 = 0) (h31 : d 3 1 = 0) :
    ∃ q ∈ upperSub, ∃ n ∈ Subgroup.normalizer (E0 : Set SL4), d = q * n := by
  have hd := eq_ofBl_of_zero h20 h21 h30 h31
  set A := blkA (d : M4) with hAdef
  set B := blkB (d : M4) with hBdef
  set C := blkC (d : M4) with hCdef
  have hdet : A.det * C.det = 1 := by
    rw [← det_ofBl, ← hd]
    exact d.det_coe
  obtain ⟨hA, hC⟩ := (by decide : ∀ x y : ZMod 2, x * y = 1 → x = 1 ∧ y = 1) _ _ hdet
  have hCu : IsUnit C.det := hC ▸ isUnit_one
  let q : SL4 := ⟨ofBl 1 (B * C⁻¹) 1, by rw [det_ofBl, Matrix.det_one, mul_one]⟩
  refine ⟨q, ?_, dg A C hA hC, dg_mem_normalizer A C hA hC, ?_⟩
  · rw [ub_mem_iff]
    exact ofBl_unip_lower _
  · apply Matrix.SpecialLinearGroup.ext
    intro x y
    rw [Matrix.SpecialLinearGroup.coe_mul]
    show (d : M4) x y = (ofBl 1 (B * C⁻¹) 1 * ofBl A 0 C) x y
    rw [ofBl_mul, hd]
    simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul C hCu]

end K21dA8Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
