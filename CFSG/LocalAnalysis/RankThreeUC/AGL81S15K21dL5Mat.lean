module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dL5Syl
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dL5Block

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21dL5Proof

open K21dA8Proof

abbrev B2 : Type := Matrix (Fin 2) (Fin 2) (ZMod 2)

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

theorem R3_zero : R3 0 = 1 := rfl

@[expose] def Ta (a : ZMod 2) : B2 := !![1, a; 0, 1]

theorem det_Ta (a : ZMod 2) : (Ta a).det = 1 := by
  simp [Ta, Matrix.det_fin_two]

structure LevData where
  c : Bool × Bool × Bool × Bool
  blk : B2 → B2 → Mat5
  blk_mul : ∀ A C A' C' : B2, blk A C * blk A' C' = blk (A * A') (C * C')
  blk_one : blk 1 1 = 1
  blk_inj : ∀ A C A' C' : B2, blk A C = blk A' C' → A = A' ∧ C = C'
  blk_det : ∀ A C : B2, (blk A C).det = A.det * C.det
  blk_bt : ∀ A C : B2, (blk A C).BlockTriangular (bf c)
  blk_surj : ∀ n : SL5, (∀ i j : Fin (4 + 1), bf c i ≠ bf c j → (n : Mat5) i j = 0) →
    ∃ A C : B2, A.det = 1 ∧ C.det = 1 ∧ (n : Mat5) = blk A C

@[expose] def dg (L : LevData) (A C : B2) (hA : A.det = 1) (hC : C.det = 1) : SL5 :=
  ⟨L.blk A C, by rw [L.blk_det, hA, hC, mul_one]⟩

@[expose] def E0 (L : LevData) : Subgroup SL5 where
  carrier := {g | ∃ i j : Fin 3, (g : Mat5) = L.blk (R3 i) (R3 j)}
  one_mem' := ⟨0, 0, by rw [Matrix.SpecialLinearGroup.coe_one, R3_zero, L.blk_one]⟩
  mul_mem' := by
    rintro g h ⟨i, j, hg⟩ ⟨i', j', hh⟩
    obtain ⟨k, hk⟩ := R3_mul i i'
    obtain ⟨l, hl⟩ := R3_mul j j'
    exact ⟨k, l, by rw [Matrix.SpecialLinearGroup.coe_mul, hg, hh, L.blk_mul, hk, hl]⟩
  inv_mem' := by
    rintro g ⟨i, j, hg⟩
    obtain ⟨k, hk⟩ := R3_inv i
    obtain ⟨l, hl⟩ := R3_inv j
    have h1 : g * dg L (R3 k) (R3 l) (R3_det k) (R3_det l) = 1 := by
      apply Matrix.SpecialLinearGroup.ext
      intro a b
      rw [Matrix.SpecialLinearGroup.coe_mul, hg]
      change (L.blk (R3 i) (R3 j) * L.blk (R3 k) (R3 l)) a b = _
      rw [L.blk_mul, hk, hl, L.blk_one]
      rfl
    refine ⟨k, l, ?_⟩
    rw [inv_eq_of_mul_eq_one_right h1]
    rfl

theorem dg_R3_mem_E0 (L : LevData) (i j : Fin 3) :
    dg L (R3 i) (R3 j) (R3_det i) (R3_det j) ∈ E0 L :=
  ⟨i, j, rfl⟩

theorem card_E0 (L : LevData) : Nat.card (E0 L) = 9 := by
  have e : (Fin 3 × Fin 3) ≃ E0 L := Equiv.ofBijective
    (fun p => ⟨dg L (R3 p.1) (R3 p.2) (R3_det p.1) (R3_det p.2), dg_R3_mem_E0 L p.1 p.2⟩)
    ⟨by
      rintro ⟨i, j⟩ ⟨i', j'⟩ h
      have h1 := congrArg (fun x : E0 L => ((x : SL5) : Mat5)) h
      obtain ⟨hi, hj⟩ := L.blk_inj _ _ _ _ h1
      exact Prod.ext (R3_injective hi) (R3_injective hj),
    by
      rintro ⟨g, i, j, hg⟩
      refine ⟨(i, j), Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_)⟩
      show (L.blk (R3 i) (R3 j)) a b = (g : Mat5) a b
      rw [hg]⟩
  rw [← Nat.card_congr e]
  simp

theorem mem_normalizer_E0 (L : LevData) (n : SL5)
    (h1 : ∀ i j : Fin 3, ∃ i' j' : Fin 3,
      (n : Mat5) * L.blk (R3 i) (R3 j) = L.blk (R3 i') (R3 j') * n)
    (h2 : ∀ i' j' : Fin 3, ∃ i j : Fin 3,
      (n : Mat5) * L.blk (R3 i) (R3 j) = L.blk (R3 i') (R3 j') * n) :
    n ∈ Subgroup.normalizer (E0 L : Set SL5) := by
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
    have hZ : n * dg L (R3 i) (R3 j) (R3_det i) (R3_det j) = (n * g * n⁻¹) * n := by
      apply Matrix.SpecialLinearGroup.ext
      intro a b
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, h', ← h]
      rfl
    have hg : g = dg L (R3 i) (R3 j) (R3_det i) (R3_det j) := by
      have h3 : n * dg L (R3 i) (R3 j) (R3_det i) (R3_det j) = n * g := by
        rw [hZ]
        group
      exact (mul_left_cancel h3).symm
    rw [hg]
    rfl

theorem dg_mem_normalizer (L : LevData) (A C : B2) (hA : A.det = 1) (hC : C.det = 1) :
    dg L A C hA hC ∈ Subgroup.normalizer (E0 L : Set SL5) := by
  refine mem_normalizer_E0 L _ ?_ ?_
  · intro i j
    obtain ⟨i', hi⟩ := R3_conj A hA i
    obtain ⟨j', hj⟩ := R3_conj C hC j
    refine ⟨i', j', ?_⟩
    show L.blk A C * L.blk (R3 i) (R3 j) = L.blk (R3 i') (R3 j') * L.blk A C
    rw [L.blk_mul, L.blk_mul, hi, hj]
  · intro i' j'
    obtain ⟨i, hi⟩ := R3_conj' A hA i'
    obtain ⟨j, hj⟩ := R3_conj' C hC j'
    refine ⟨i, j, ?_⟩
    show L.blk A C * L.blk (R3 i) (R3 j) = L.blk (R3 i') (R3 j') * L.blk A C
    rw [L.blk_mul, L.blk_mul, hi, hj]

@[expose] def eA (L : LevData) : SL5 := dg L (R3 1) (R3 0) (R3_det 1) (R3_det 0)

@[expose] def eAB (L : LevData) : SL5 := dg L (R3 1) (R3 1) (R3_det 1) (R3_det 1)

@[expose] def s2 (L : LevData) : SL5 := dg L 1 (Ta 1) Matrix.det_one (det_Ta 1)

theorem eA_mem (L : LevData) : eA L ∈ E0 L := dg_R3_mem_E0 L 1 0

theorem eAB_mem (L : LevData) : eAB L ∈ E0 L := dg_R3_mem_E0 L 1 1

theorem eA_ne_one (L : LevData) : eA L ≠ 1 := by
  intro h
  have h1 := congrArg (fun x : SL5 => (x : Mat5)) h
  simp only [eA, dg, Matrix.SpecialLinearGroup.coe_one, R3_zero] at h1
  rw [← L.blk_one] at h1
  have := (L.blk_inj _ _ _ _ h1).1
  rw [← R3_zero] at this
  exact absurd (R3_injective this) (by decide)

theorem eAB_ne_one (L : LevData) : eAB L ≠ 1 := by
  intro h
  have h1 := congrArg (fun x : SL5 => (x : Mat5)) h
  simp only [eAB, dg, Matrix.SpecialLinearGroup.coe_one] at h1
  rw [← L.blk_one] at h1
  have := (L.blk_inj _ _ _ _ h1).1
  rw [← R3_zero] at this
  exact absurd (R3_injective this) (by decide)

theorem s2_ne_one (L : LevData) : s2 L ≠ 1 := by
  intro h
  have h1 := congrArg (fun x : SL5 => (x : Mat5)) h
  simp only [s2, dg, Matrix.SpecialLinearGroup.coe_one] at h1
  rw [← L.blk_one] at h1
  have := (L.blk_inj _ _ _ _ h1).2
  revert this
  decide

theorem s2_mem_normalizer (L : LevData) : s2 L ∈ Subgroup.normalizer (E0 L : Set SL5) :=
  dg_mem_normalizer L _ _ _ _

theorem s2_mem_centralizer (L : LevData) : s2 L ∈ Subgroup.centralizer ({eA L} : Set SL5) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Matrix.SpecialLinearGroup.ext
  intro x y
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  change (L.blk 1 (Ta 1) * L.blk (R3 1) (R3 0)) x y = (L.blk (R3 1) (R3 0) * L.blk 1 (Ta 1)) x y
  rw [L.blk_mul, L.blk_mul]
  simp [R3_zero]

theorem concl_E0 (L : LevData) (hs2 : s2 L ∈ upperSub5)
    (htriv : ∀ g : SL5, g ∈ upperSub5 → g ∈ Subgroup.normalizer (E0 L : Set SL5) →
      g ∈ Subgroup.centralizer ({eAB L} : Set SL5) → g = 1) :
    K21dConcl upperSub5 (E0 L) := by
  refine ⟨eA L, eA_mem L, eAB L, eAB_mem L, eA_ne_one L, eAB_ne_one L, ?_⟩
  have h1 : Nat.card ↥(upperSub5 ⊓ Subgroup.normalizer (E0 L : Set SL5) ⊓
      Subgroup.centralizer ({eAB L} : Set SL5)) = 1 := by
    rw [Subgroup.card_eq_one, Subgroup.eq_bot_iff_forall]
    intro g hg
    rw [Subgroup.mem_inf, Subgroup.mem_inf] at hg
    exact htriv g hg.1.1 hg.1.2 hg.2
  have h2 : 1 < Nat.card ↥(upperSub5 ⊓ Subgroup.normalizer (E0 L : Set SL5) ⊓
      Subgroup.centralizer ({eA L} : Set SL5)) := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro hbot
    have hmem : s2 L ∈ (upperSub5 ⊓ Subgroup.normalizer (E0 L : Set SL5) ⊓
        Subgroup.centralizer ({eA L} : Set SL5)) :=
      ⟨⟨hs2, s2_mem_normalizer L⟩, s2_mem_centralizer L⟩
    rw [hbot] at hmem
    exact s2_ne_one L (Subgroup.mem_bot.1 hmem)
  omega

@[expose] def dgn (β : Fin (4 + 1) → ℕ) (M : Mat5) : Mat5 :=
  Matrix.of fun i j => if β i = β j then M i j else 0

theorem dgn_mul {β : Fin (4 + 1) → ℕ} {M N : Mat5} (hM : M.BlockTriangular β)
    (hN : N.BlockTriangular β) : dgn β (M * N) = dgn β M * dgn β N := by
  ext i j
  simp only [dgn, Matrix.of_apply, Matrix.mul_apply]
  by_cases h : β i = β j
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : β i = β k
    · rw [if_pos hk, if_pos (hk.symm.trans h)]
    · rw [if_neg hk, zero_mul]
      rcases lt_or_gt_of_ne hk with hlt | hgt
      · rw [hN (show β j < β k by rw [← h]; exact hlt), mul_zero]
      · rw [hM hgt, zero_mul]
  · rw [if_neg h]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : β i = β k
    · by_cases hk' : β k = β j
      · exact absurd (hk.trans hk') h
      · rw [if_neg hk', mul_zero]
    · rw [if_neg hk, zero_mul]

theorem dgn_one (β : Fin (4 + 1) → ℕ) : dgn β 1 = 1 := by
  ext i j
  simp only [dgn, Matrix.of_apply]
  split_ifs with h
  · rfl
  · exact (Matrix.one_apply_ne (fun e => h (by rw [e]))).symm

theorem dgn_dgn (β : Fin (4 + 1) → ℕ) (M : Mat5) : dgn β (dgn β M) = dgn β M := by
  ext i j
  simp only [dgn, Matrix.of_apply]
  split_ifs <;> rfl

theorem dgn_blockTriangular (β : Fin (4 + 1) → ℕ) (M : Mat5) : (dgn β M).BlockTriangular β := by
  intro i j h
  simp [dgn, h.ne']

theorem zmod2_mul_eq_one : ∀ x y : ZMod 2, x * y = 1 → x = 1 ∧ y = 1 := by decide

theorem levi_decomp (c : Bool × Bool × Bool × Bool) {d : SL5} (hd : d ∈ Block c) :
    ∃ q ∈ upperSub5, ∃ n : SL5,
      (∀ i j : Fin (4 + 1), bf c i ≠ bf c j → (n : Mat5) i j = 0) ∧ d = q * n := by
  have hM : (d : Mat5).BlockTriangular (bf c) := hd
  have hM' : ((d⁻¹ : SL5) : Mat5).BlockTriangular (bf c) := (Block c).inv_mem hd
  have hMM' : (d : Mat5) * ((d⁻¹ : SL5) : Mat5) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hM'M : ((d⁻¹ : SL5) : Mat5) * (d : Mat5) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have e1 : dgn (bf c) (d : Mat5) * dgn (bf c) ((d⁻¹ : SL5) : Mat5) = 1 := by
    rw [← dgn_mul hM hM', hMM', dgn_one]
  have e2 : dgn (bf c) ((d⁻¹ : SL5) : Mat5) * dgn (bf c) (d : Mat5) = 1 := by
    rw [← dgn_mul hM' hM, hM'M, dgn_one]
  have hdet := congrArg Matrix.det e1
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  obtain ⟨hd1, hd2⟩ := zmod2_mul_eq_one _ _ hdet
  let n : SL5 := ⟨dgn (bf c) (d : Mat5), hd1⟩
  let n' : SL5 := ⟨dgn (bf c) ((d⁻¹ : SL5) : Mat5), hd2⟩
  have hnn' : n' * n = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    exact e2)
  refine ⟨d * n', ?_, n, ?_, ?_⟩
  · rw [ub5_mem_iff]
    intro i j hji
    have hbt : ((d * n' : SL5) : Mat5).BlockTriangular (bf c) := by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      exact hM.mul (dgn_blockTriangular _ _)
    have hdg : dgn (bf c) ((d * n' : SL5) : Mat5) = 1 := by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      change dgn (bf c) ((d : Mat5) * dgn (bf c) ((d⁻¹ : SL5) : Mat5)) = 1
      rw [dgn_mul hM (dgn_blockTriangular _ _), dgn_dgn, e1]
    by_cases h : bf c i = bf c j
    · have := congrFun (congrFun hdg i) j
      simp only [dgn, Matrix.of_apply, if_pos h] at this
      rw [this]
      exact Matrix.one_apply_ne hji.ne'
    · have h1 := bf_lt c j i
      have h2 : bf c j < bf c i := by
        by_contra hcon
        exact absurd (h1 (by omega)) (not_lt.2 hji.le)
      exact hbt h2
  · intro i j h
    simp [n, dgn, h]
  · rw [mul_assoc, hnn', mul_one]

theorem E0_le_Block (L : LevData) : E0 L ≤ Block L.c := by
  rintro g ⟨i, j, hg⟩
  show (g : Mat5).BlockTriangular (bf L.c)
  rw [hg]
  exact L.blk_bt _ _

theorem levi_normalizer (L : LevData) {n : SL5}
    (hn : ∀ i j : Fin (4 + 1), bf L.c i ≠ bf L.c j → (n : Mat5) i j = 0) :
    n ∈ Subgroup.normalizer (E0 L : Set SL5) := by
  obtain ⟨A, C, hA, hC, hAC⟩ := L.blk_surj n hn
  have : n = dg L A C hA hC := Subtype.ext hAC
  rw [this]
  exact dg_mem_normalizer L A C hA hC

theorem decomp_of_levData (L : LevData) {d : SL5} (hd : d ∈ Block L.c) :
    ∃ q ∈ upperSub5, ∃ n ∈ Subgroup.normalizer (E0 L : Set SL5), d = q * n := by
  obtain ⟨q, hq, n, hn, hdqn⟩ := levi_decomp L.c hd
  exact ⟨q, hq, n, levi_normalizer L hn, hdqn⟩

theorem concl_of_levData (L : LevData) (hs2 : s2 L ∈ upperSub5)
    (htriv : ∀ g : SL5, g ∈ upperSub5 → g ∈ Subgroup.normalizer (E0 L : Set SL5) →
      g ∈ Subgroup.centralizer ({eAB L} : Set SL5) → g = 1)
    {E : Subgroup SL5} (hE : E ≤ Block L.c) (hEc : Nat.card E = 9) :
    K21dConcl upperSub5 E :=
  concl_of_levi (fun _ hd => decomp_of_levData L hd) (E0_le_Block L) (card_E0 L) hE hEc
    (concl_E0 L hs2 htriv)

end K21dL5Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
