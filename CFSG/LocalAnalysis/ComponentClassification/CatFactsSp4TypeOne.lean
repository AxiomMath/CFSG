module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TypeTwo
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup
open scoped commutatorElement

variable {K : Type} [Field K]

theorem blk_neg_one_neg_one : blk (-1 : Matrix (Fin 2) (Fin 2) K) (-1) = -1 := by
  rw [← fromBlocks_one, fromBlocks_neg]
  simp only [blk]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [diag2]

theorem blk_neg (g h : Matrix (Fin 2) (Fin 2) K) : -blk g h = blk (-g) (-h) := by
  simp only [blk, fromBlocks_neg]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [diag2]

theorem det_neg_one_two : (-1 : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  rw [det_neg, det_one, Fintype.card_fin]
  norm_num

theorem eq_one_or_neg_one_of_sq (h2 : (2 : K) ≠ 0) {g : Matrix (Fin 2) (Fin 2) K} (hg : g.det = 1)
    (hgg : g * g = 1) : g = 1 ∨ g = -1 := by
  have e : ∀ i j, (g * g) i j = (1 : Matrix (Fin 2) (Fin 2) K) i j := fun i j => by rw [hgg]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  rw [det_fin_two] at hg
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  by_cases htr : g 0 0 + g 1 1 = 0
  · exfalso
    have h1 : g 1 1 = -g 0 0 := by linear_combination htr
    rw [h1] at hg
    exact h2 (by linear_combination -hg - e00)
  · have hb : g 0 1 = 0 := by
      have : g 0 1 * (g 0 0 + g 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right htr
    have hc : g 1 0 = 0 := by
      have : g 1 0 * (g 0 0 + g 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right htr
    rw [hb] at e00 e11 hg
    have ha : g 0 0 * g 0 0 = 1 := by simpa using e00
    rcases mul_self_eq_one_iff.mp ha with ha1 | ha1
    · left
      have hd : g 1 1 = 1 := by rw [ha1] at hg; simpa [hc] using hg
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha1, hb, hc, hd]
    · right
      have hd : g 1 1 = -1 := by rw [ha1] at hg; simp [hc] at hg; linear_combination -hg
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha1, hb, hc, hd]

theorem blk_symplectic_of_det {g h : Matrix (Fin 2) (Fin 2) K} (hg : g.det = 1)
    (hh : h.det = 1) : (blk g h)ᵀ * formJ 2 K * blk g h = formJ 2 K :=
  (blk_symplectic_iff g h).mpr ⟨hg, hh⟩

variable (K) in
@[expose] def T1 : StatedSp 2 K :=
  toSp (blk 1 (-1)) (blk_symplectic_of_det det_one det_neg_one_two)

theorem coe_T1 : (((T1 K : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = blk 1 (-1) := rfl

variable (K) in
@[expose] def blkSL :
    Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp 2 K where
  toFun x := toSp (blk (x.1 : Matrix (Fin 2) (Fin 2) K) x.2) (blk_symplectic_of_det x.1.2 x.2.2)
  map_one' := sp_ext (by simp [blk_one_one])
  map_mul' x y := sp_ext (by simp [blk_mul])

theorem coe_blkSL (x : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    (((blkSL K x : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      blk (x.1 : Matrix (Fin 2) (Fin 2) K) x.2 := rfl

theorem blk_one_neg_one_eq_diagonal :
    blk (1 : Matrix (Fin 2) (Fin 2) K) (-1) = diagonal (Sum.elim ![1, -1] ![1, -1]) := by
  ext (x | x) (y | y) <;> fin_cases x <;> fin_cases y <;> simp [blk, diag2, diagonal]

theorem exists_blk_of_commute (h2 : (2 : K) ≠ 0) {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hA : A * blk 1 (-1) = blk 1 (-1) * A) : ∃ g h, A = blk g h := by
  rw [blk_one_neg_one_eq_diagonal] at hA
  set d : Fin 2 ⊕ Fin 2 → K := Sum.elim ![1, -1] ![1, -1] with hd
  have hz : ∀ x y, d x ≠ d y → A x y = 0 := by
    intro x y hxy
    have h := congrFun (congrFun hA x) y
    rw [mul_diagonal, diagonal_mul] at h
    have h' : A x y * (d y - d x) = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_right (sub_ne_zero.mpr (Ne.symm hxy))
  have hne : (1 : K) ≠ -1 := fun h => h2 (by linear_combination h)
  refine ⟨!![A (.inl 0) (.inl 0), A (.inl 0) (.inr 0); A (.inr 0) (.inl 0), A (.inr 0) (.inr 0)],
    !![A (.inl 1) (.inl 1), A (.inl 1) (.inr 1); A (.inr 1) (.inl 1), A (.inr 1) (.inr 1)], ?_⟩
  ext (x | x) (y | y) <;> fin_cases x <;> fin_cases y <;> simp only [blk, diag2] <;>
    simp <;>
    first
      | exact hz _ _ (by simpa [hd] using hne)
      | exact hz _ _ (by simpa [hd] using hne.symm)

theorem mem_centralizer_T1_iff (h2 : (2 : K) ≠ 0) {x : StatedSp 2 K} :
    x ∈ centralizer {T1 K} ↔ x ∈ (blkSL K).range := by
  constructor
  · intro hx
    have hc := congrArg (fun y : StatedSp 2 K =>
      ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
      (mem_centralizer_singleton_iff.mp hx)
    simp only [Subgroup.coe_mul, Units.val_mul, coe_T1] at hc
    obtain ⟨g, h, hgh⟩ := exists_blk_of_commute h2 hc
    have hs := symplectic_of_mem x
    rw [hgh, blk_symplectic_iff] at hs
    exact ⟨(⟨g, hs.1⟩, ⟨h, hs.2⟩), sp_ext (by rw [coe_blkSL, hgh])⟩
  · rintro ⟨y, rfl⟩
    rw [mem_centralizer_singleton_iff]
    apply sp_ext
    simp only [Subgroup.coe_mul, Units.val_mul, coe_T1, coe_blkSL, blk_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul]

theorem eq_or_eq_neg_of_proj_eq {a b : StatedSp 2 K} (h : proj 2 K a = proj 2 K b) :
    ((b : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        ((a : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∨
      ((b : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        -((a : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
  have hk : a⁻¹ * b ∈ spScalars 2 K := by
    rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hb : b = a * (a⁻¹ * b) := by group
  rcases (mem_spScalars_iff _).mp hk with h1 | h1
  · left
    rw [hb, Subgroup.coe_mul, Units.val_mul, h1, Matrix.mul_one]
  · right
    rw [hb, Subgroup.coe_mul, Units.val_mul, h1, Matrix.mul_neg, Matrix.mul_one]

theorem proj_blkSL_eq_one_iff
    (x : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    proj 2 K (blkSL K x) = 1 ↔
      ((x.1 : Matrix (Fin 2) (Fin 2) K) = 1 ∧ (x.2 : Matrix (Fin 2) (Fin 2) K) = 1) ∨
        ((x.1 : Matrix (Fin 2) (Fin 2) K) = -1 ∧ (x.2 : Matrix (Fin 2) (Fin 2) K) = -1) := by
  rw [← MonoidHom.mem_ker, ker_proj, mem_spScalars_iff, coe_blkSL]
  constructor
  · rintro (h | h)
    · left
      rw [← blk_one_one] at h
      exact blk_injective _ _ _ _ h
    · right
      rw [← blk_neg_one_neg_one] at h
      exact blk_injective _ _ _ _ h
  · rintro (⟨h1, h1'⟩ | ⟨h1, h1'⟩)
    · left
      rw [h1, h1', blk_one_one]
    · right
      rw [h1, h1', blk_neg_one_neg_one]

@[expose] def negOneSL : Matrix.SpecialLinearGroup (Fin 2) K := ⟨-1, det_neg_one_two⟩

variable (K) in
@[expose] def u1 : StatedProj (StatedSp 2 K) := proj 2 K (T1 K)

variable (K) in
@[expose] def E1 : Subgroup (StatedProj (StatedSp 2 K)) :=
  ((blkSL K).comp (MonoidHom.inl _ _)).range.map (proj 2 K)

variable (K) in
@[expose] def E2 : Subgroup (StatedProj (StatedSp 2 K)) :=
  ((blkSL K).comp (MonoidHom.inr _ _)).range.map (proj 2 K)

variable (K) in
@[expose] def X0 : Subgroup (StatedProj (StatedSp 2 K)) :=
  (centralizer {T1 K}).map (proj 2 K)

theorem mem_E1 {x : StatedProj (StatedSp 2 K)} :
    x ∈ E1 K ↔ ∃ g, proj 2 K (blkSL K (g, 1)) = x := by
  simp [E1]

theorem mem_E2 {x : StatedProj (StatedSp 2 K)} :
    x ∈ E2 K ↔ ∃ h, proj 2 K (blkSL K (1, h)) = x := by
  simp [E2]

theorem mem_X0 (h2 : (2 : K) ≠ 0) {x : StatedProj (StatedSp 2 K)} :
    x ∈ X0 K ↔ ∃ y, proj 2 K (blkSL K y) = x := by
  simp only [X0, mem_map, mem_centralizer_T1_iff h2, MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨_, ⟨y, rfl⟩, rfl⟩

theorem blkSL_mul_split (g h : Matrix.SpecialLinearGroup (Fin 2) K) :
    blkSL K (g, h) = blkSL K (g, 1) * blkSL K (1, h) := by
  rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

theorem u1_eq_proj_blkSL : u1 K = proj 2 K (blkSL K (1, negOneSL)) := by
  rw [u1]
  congr 1

theorem u1_eq_proj_blkSL' : u1 K = proj 2 K (blkSL K (negOneSL, 1)) := by
  have hm : blkSL K (negOneSL, 1) = blkSL K (1, negOneSL) * blkSL K (negOneSL, negOneSL) := by
    have hn : (negOneSL : Matrix.SpecialLinearGroup (Fin 2) K) * negOneSL = 1 :=
      Subtype.ext (by
        change (-1 : Matrix (Fin 2) (Fin 2) K) * -1 = 1
        simp)
    rw [← map_mul, Prod.mk_mul_mk, one_mul, hn]
  have h1 : proj 2 K (blkSL K (negOneSL, negOneSL)) = 1 :=
    (proj_blkSL_eq_one_iff _).mpr (Or.inr ⟨rfl, rfl⟩)
  rw [u1_eq_proj_blkSL, hm, map_mul, h1, mul_one]

theorem E1_le_X0 (h2 : (2 : K) ≠ 0) : E1 K ≤ X0 K := fun x hx => by
  obtain ⟨g, rfl⟩ := mem_E1.mp hx
  exact (mem_X0 h2).mpr ⟨_, rfl⟩

theorem E2_le_X0 (h2 : (2 : K) ≠ 0) : E2 K ≤ X0 K := fun x hx => by
  obtain ⟨h, rfl⟩ := mem_E2.mp hx
  exact (mem_X0 h2).mpr ⟨_, rfl⟩

theorem map_centralizer_le (T : StatedSp 2 K) :
    (centralizer {T}).map (proj 2 K) ≤ centralizer {proj 2 K T} := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hx]

theorem X0_le_centralizer : X0 K ≤ centralizer {u1 K} := map_centralizer_le (T1 K)

theorem exists_mul_of_mem_X0 (h2 : (2 : K) ≠ 0) {x : StatedProj (StatedSp 2 K)}
    (hx : x ∈ X0 K) : ∃ a ∈ E1 K, ∃ b ∈ E2 K, x = a * b := by
  obtain ⟨⟨g, h⟩, rfl⟩ := (mem_X0 h2).mp hx
  exact ⟨_, mem_E1.mpr ⟨g, rfl⟩, _, mem_E2.mpr ⟨h, rfl⟩, by rw [← map_mul, ← blkSL_mul_split]⟩

theorem commute_E1_E2 {x y : StatedProj (StatedSp 2 K)} (hx : x ∈ E1 K) (hy : y ∈ E2 K) :
    x * y = y * x := by
  obtain ⟨g, rfl⟩ := mem_E1.mp hx
  obtain ⟨h, rfl⟩ := mem_E2.mp hy
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one,
    one_mul, mul_one, one_mul]

theorem coe_negOneSL :
    ((negOneSL : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = -1 := rfl

theorem coe_negOneSL_mul (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((negOneSL * g : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      -(g : Matrix (Fin 2) (Fin 2) K) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_negOneSL, neg_one_mul]

theorem proj_blkSL_negOne_one :
    proj 2 K (blkSL K (negOneSL, negOneSL)) = 1 :=
  (proj_blkSL_eq_one_iff _).mpr (Or.inr ⟨rfl, rfl⟩)

theorem proj_blkSL_neg_right (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    proj 2 K (blkSL K (g, negOneSL)) = proj 2 K (blkSL K (negOneSL * g, 1)) := by
  have hm : blkSL K (g, negOneSL) = blkSL K (negOneSL * g, 1) * blkSL K (negOneSL, negOneSL) := by
    apply sp_ext
    rw [Subgroup.coe_mul, Units.val_mul, coe_blkSL, coe_blkSL, coe_blkSL, blk_mul]
    simp only [coe_negOneSL_mul, coe_negOneSL, Matrix.SpecialLinearGroup.coe_one, neg_mul_neg,
      Matrix.mul_one, Matrix.one_mul]
  rw [hm, map_mul, proj_blkSL_negOne_one, mul_one]

theorem proj_blkSL_neg_left (h : Matrix.SpecialLinearGroup (Fin 2) K) :
    proj 2 K (blkSL K (negOneSL, h)) = proj 2 K (blkSL K (1, negOneSL * h)) := by
  have hm : blkSL K (negOneSL, h) = blkSL K (1, negOneSL * h) * blkSL K (negOneSL, negOneSL) := by
    apply sp_ext
    rw [Subgroup.coe_mul, Units.val_mul, coe_blkSL, coe_blkSL, coe_blkSL, blk_mul]
    simp only [coe_negOneSL_mul, coe_negOneSL, Matrix.SpecialLinearGroup.coe_one, neg_mul_neg,
      Matrix.mul_one, Matrix.one_mul]
  rw [hm, map_mul, proj_blkSL_negOne_one, mul_one]

theorem one_ne_neg_one_mat (h2 : (2 : K) ≠ 0) : (1 : Matrix (Fin 2) (Fin 2) K) ≠ -1 := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp only [one_apply_eq, Matrix.neg_apply] at this
  exact h2 (by linear_combination this)

theorem eq_one_or_neg_of_mem_center {h : Matrix.SpecialLinearGroup (Fin 2) K}
    (hz : h ∈ center (Matrix.SpecialLinearGroup (Fin 2) K)) :
    (h : Matrix (Fin 2) (Fin 2) K) = 1 ∨ (h : Matrix (Fin 2) (Fin 2) K) = -1 := by
  obtain ⟨r, hr, hrh⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  rw [Fintype.card_fin, pow_two] at hr
  rw [← hrh]
  rcases mul_self_eq_one_iff.mp hr with rfl | rfl
  · left
    simp
  · right
    ext i j
    by_cases hij : i = j <;> simp [hij, one_apply]

theorem eq_zero_of_eq_neg (h2 : (2 : K) ≠ 0) {g : Matrix (Fin 2) (Fin 2) K} (hg : g = -g) :
    g = 0 := by
  ext i j
  have := congrFun (congrFun hg i) j
  simp only [Matrix.neg_apply, Matrix.zero_apply] at this ⊢
  exact (mul_eq_zero.mp (by linear_combination this : (2 : K) * g i j = 0)).resolve_left h2

theorem ne_neg_of_det (h2 : (2 : K) ≠ 0) (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    (g : Matrix (Fin 2) (Fin 2) K) ≠ -(g : Matrix (Fin 2) (Fin 2) K) := by
  intro hg
  have h0 := eq_zero_of_eq_neg h2 hg
  have := g.2
  rw [h0, det_zero] at this
  exact zero_ne_one this

theorem mem_E1_of_commute_E2 (h2 : (2 : K) ≠ 0) {x : StatedProj (StatedSp 2 K)}
    (hx : x ∈ X0 K) (hc : ∀ y ∈ E2 K, x * y = y * x) : x ∈ E1 K := by
  obtain ⟨⟨g, h⟩, rfl⟩ := (mem_X0 h2).mp hx
  have hk : h ∈ center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.mem_center_iff]
    intro k
    have h1 := hc _ (mem_E2.mpr ⟨k, rfl⟩)
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one,
      one_mul] at h1
    rcases eq_or_eq_neg_of_proj_eq h1 with h3 | h3
    · rw [coe_blkSL, coe_blkSL] at h3
      exact Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul]; exact (blk_injective _ _ _ _ h3).2)
    · exfalso
      rw [coe_blkSL, coe_blkSL, blk_neg] at h3
      exact ne_neg_of_det h2 g (blk_injective _ _ _ _ h3).1
  rcases eq_one_or_neg_of_mem_center hk with h1 | h1
  · exact mem_E1.mpr ⟨g, by rw [show h = 1 from Subtype.ext h1]⟩
  · rw [show h = negOneSL from Subtype.ext h1, proj_blkSL_neg_right]
    exact mem_E1.mpr ⟨_, rfl⟩

theorem mem_E2_of_commute_E1 (h2 : (2 : K) ≠ 0) {x : StatedProj (StatedSp 2 K)}
    (hx : x ∈ X0 K) (hc : ∀ y ∈ E1 K, x * y = y * x) : x ∈ E2 K := by
  obtain ⟨⟨g, h⟩, rfl⟩ := (mem_X0 h2).mp hx
  have hk : g ∈ center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.mem_center_iff]
    intro k
    have h1 := hc _ (mem_E1.mpr ⟨k, rfl⟩)
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one,
      one_mul] at h1
    rcases eq_or_eq_neg_of_proj_eq h1 with h3 | h3
    · rw [coe_blkSL, coe_blkSL] at h3
      exact Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul]; exact (blk_injective _ _ _ _ h3).1)
    · exfalso
      rw [coe_blkSL, coe_blkSL, blk_neg] at h3
      exact ne_neg_of_det h2 h (blk_injective _ _ _ _ h3).2
  rcases eq_one_or_neg_of_mem_center hk with h1 | h1
  · exact mem_E2.mpr ⟨h, by rw [show g = 1 from Subtype.ext h1]⟩
  · rw [show g = negOneSL from Subtype.ext h1, proj_blkSL_neg_left]
    exact mem_E2.mpr ⟨_, rfl⟩

theorem E1_eq_range : E1 K = ((proj 2 K).comp ((blkSL K).comp (MonoidHom.inl _ _))).range :=
  (MonoidHom.range_comp _ _).symm

theorem E2_eq_range : E2 K = ((proj 2 K).comp ((blkSL K).comp (MonoidHom.inr _ _))).range :=
  (MonoidHom.range_comp _ _).symm

theorem injective_E1 (h2 : (2 : K) ≠ 0) :
    Function.Injective ((proj 2 K).comp ((blkSL K).comp (MonoidHom.inl _ _))) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rcases (proj_blkSL_eq_one_iff _).mp hg with ⟨h1, -⟩ | ⟨-, h1⟩
  · exact Subtype.ext h1
  · exact absurd h1 (one_ne_neg_one_mat h2)

theorem injective_E2 (h2 : (2 : K) ≠ 0) :
    Function.Injective ((proj 2 K).comp ((blkSL K).comp (MonoidHom.inr _ _))) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rcases (proj_blkSL_eq_one_iff _).mp hg with ⟨-, h1⟩ | ⟨h1, -⟩
  · exact Subtype.ext h1
  · exact absurd h1 (one_ne_neg_one_mat h2)

@[expose] def E1Equiv (h2 : (2 : K) ≠ 0) : Matrix.SpecialLinearGroup (Fin 2) K ≃* E1 K :=
  (MonoidHom.ofInjective (injective_E1 h2)).trans (MulEquiv.subgroupCongr E1_eq_range.symm)

@[expose] def E2Equiv (h2 : (2 : K) ≠ 0) : Matrix.SpecialLinearGroup (Fin 2) K ≃* E2 K :=
  (MonoidHom.ofInjective (injective_E2 h2)).trans (MulEquiv.subgroupCongr E2_eq_range.symm)

omit [Field K] in
theorem exists_finset_card_four [Finite K] (h4 : 4 ≤ Nat.card K) : ∃ s : Finset K, s.card = 4 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
    (by simpa [Finset.card_univ, Nat.card_eq_fintype_card] using h4)
  exact ⟨s, hs⟩

theorem isQuasisimple_SL2' [Finite K] (h4 : 4 ≤ Nat.card K) :
    CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have h4' := exists_finset_card_four h4
  have hperf := CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := 2) le_rfl (Or.inr h4')
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := K) (n := 2) le_rfl
    (Or.inr h4')
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hab
  push Not at hab
  have hle : commutator (Matrix.SpecialLinearGroup (Fin 2) K) ≤
      center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (center (Matrix.SpecialLinearGroup (Fin 2) K))) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_def, hab (QuotientGroup.mk' _ x),
      mul_inv_cancel_right, mul_inv_cancel]
  rw [Group.isPerfect_def.mp hperf] at hle
  obtain ⟨a, b, hne⟩ := exists_pair_ne
    (Matrix.SpecialLinearGroup (Fin 2) K ⧸ center (Matrix.SpecialLinearGroup (Fin 2) K))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hne (QuotientGroup.eq.mpr (hle (Subgroup.mem_top _)))

theorem orderOf_negOneSL (h2 : (2 : K) ≠ 0) :
    orderOf (negOneSL : Matrix.SpecialLinearGroup (Fin 2) K) = 2 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, coe_negOneSL]
    simp
  · intro h
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
      (g : Matrix (Fin 2) (Fin 2) K)) h
    simp only [coe_negOneSL, Matrix.SpecialLinearGroup.coe_one] at this
    exact one_ne_neg_one_mat h2 this.symm

theorem pPrimeCore_SL2 [Finite K] (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) :
    pPrimeCore 2 (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [pPrimeCore_eq_bot_iff]
  intro N hN hcop
  have hodd : ∀ z ∈ N, (z : Matrix (Fin 2) (Fin 2) K) ≠ -1 := by
    intro z hz h1
    have hzn : z = negOneSL := Subtype.ext h1
    have hdvd := Subgroup.orderOf_dvd_natCard N hz
    rw [hzn, orderOf_negOneSL h2] at hdvd
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop hdvd
  rcases LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups (isQuasisimple_SL2' h4) hN
    with htop | hcen
  · exact absurd rfl (hodd negOneSL (htop ▸ mem_top _))
  · rw [eq_bot_iff]
    intro z hz
    rcases eq_one_or_neg_of_mem_center (hcen hz) with h1 | h1
    · exact (Subgroup.mem_bot).mpr (Subtype.ext h1)
    · exact absurd h1 (hodd z hz)

theorem pPrimeCore_E1 [Finite K] (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) :
    pPrimeCore 2 (E1 K) = ⊥ := by
  rw [← CFSG.pPrimeCore_map_iso 2 (E1Equiv h2), pPrimeCore_SL2 h2 h4, Subgroup.map_bot]

theorem pPrimeCore_E2 [Finite K] (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) :
    pPrimeCore 2 (E2 K) = ⊥ := by
  rw [← CFSG.pPrimeCore_map_iso 2 (E2Equiv h2), pPrimeCore_SL2 h2 h4, Subgroup.map_bot]

theorem isQuasisimple_E1 [Finite K] (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) :
    CFSG.IsQuasisimple (E1 K) :=
  (LocalAnalysis.ComponentInitial.isQuasisimple_congr (E1Equiv h2)).mp (isQuasisimple_SL2' h4)

theorem isQuasisimple_E2 [Finite K] (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) :
    CFSG.IsQuasisimple (E2 K) :=
  (LocalAnalysis.ComponentInitial.isQuasisimple_congr (E2Equiv h2)).mp (isQuasisimple_SL2' h4)

theorem u1_mem_E1 : u1 K ∈ E1 K := mem_E1.mpr ⟨negOneSL, u1_eq_proj_blkSL'.symm⟩

theorem u1_mem_E2 : u1 K ∈ E2 K := mem_E2.mpr ⟨negOneSL, u1_eq_proj_blkSL.symm⟩

theorem u1_ne_one (h2 : (2 : K) ≠ 0) : u1 K ≠ 1 := by
  rw [u1_eq_proj_blkSL]
  intro h
  rcases (proj_blkSL_eq_one_iff _).mp h with ⟨-, h1⟩ | ⟨h1, -⟩
  · exact one_ne_neg_one_mat h2 h1.symm
  · exact one_ne_neg_one_mat h2 h1

theorem sq_proj_blkSL
    (x : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    proj 2 K (blkSL K x) ^ 2 = proj 2 K (blkSL K (x * x)) := by
  rw [pow_two, ← map_mul, ← map_mul]

theorem eq_u1_of_mem_E1 (h2 : (2 : K) ≠ 0) {x : StatedProj (StatedSp 2 K)} (hx : x ∈ E1 K)
    (hord : orderOf x = 2) : x = u1 K := by
  obtain ⟨g, rfl⟩ := mem_E1.mp hx
  have hsq := pow_orderOf_eq_one (proj 2 K (blkSL K (g, 1)))
  rw [hord, sq_proj_blkSL, Prod.mk_mul_mk, mul_one, proj_blkSL_eq_one_iff] at hsq
  rcases hsq with ⟨h1, -⟩ | ⟨-, h1⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul] at h1
    rcases eq_one_or_neg_one_of_sq h2 g.2 h1 with h3 | h3
    · exfalso
      rw [show g = 1 from Subtype.ext h3, show ((1 : Matrix.SpecialLinearGroup (Fin 2) K),
        (1 : Matrix.SpecialLinearGroup (Fin 2) K)) = 1 from rfl, map_one, map_one,
        orderOf_one] at hord
      exact absurd hord (by norm_num)
    · rw [u1_eq_proj_blkSL', show g = negOneSL from Subtype.ext h3]
  · exact absurd h1 (one_ne_neg_one_mat h2)

theorem eq_u1_of_mem_E2 (h2 : (2 : K) ≠ 0) {x : StatedProj (StatedSp 2 K)} (hx : x ∈ E2 K)
    (hord : orderOf x = 2) : x = u1 K := by
  obtain ⟨g, rfl⟩ := mem_E2.mp hx
  have hsq := pow_orderOf_eq_one (proj 2 K (blkSL K (1, g)))
  rw [hord, sq_proj_blkSL, Prod.mk_mul_mk, mul_one, proj_blkSL_eq_one_iff] at hsq
  rcases hsq with ⟨-, h1⟩ | ⟨h1, -⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul] at h1
    rcases eq_one_or_neg_one_of_sq h2 g.2 h1 with h3 | h3
    · exfalso
      rw [show g = 1 from Subtype.ext h3, show ((1 : Matrix.SpecialLinearGroup (Fin 2) K),
        (1 : Matrix.SpecialLinearGroup (Fin 2) K)) = 1 from rfl, map_one, map_one,
        orderOf_one] at hord
      exact absurd hord (by norm_num)
    · rw [u1_eq_proj_blkSL, show g = negOneSL from Subtype.ext h3]
  · exact absurd h1 (one_ne_neg_one_mat h2)

theorem conj_mem_E1 (h2 : (2 : K) ≠ 0) {x e : StatedProj (StatedSp 2 K)} (hx : x ∈ X0 K)
    (he : e ∈ E1 K) : x * e * x⁻¹ ∈ E1 K := by
  obtain ⟨⟨g, h⟩, rfl⟩ := (mem_X0 h2).mp hx
  obtain ⟨k, rfl⟩ := mem_E1.mp he
  refine mem_E1.mpr ⟨g * k * g⁻¹, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul, Prod.inv_mk,
    Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one, mul_inv_cancel]

theorem conj_mem_E2 (h2 : (2 : K) ≠ 0) {x e : StatedProj (StatedSp 2 K)} (hx : x ∈ X0 K)
    (he : e ∈ E2 K) : x * e * x⁻¹ ∈ E2 K := by
  obtain ⟨⟨g, h⟩, rfl⟩ := (mem_X0 h2).mp hx
  obtain ⟨k, rfl⟩ := mem_E2.mp he
  refine mem_E2.mpr ⟨h * k * h⁻¹, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul, Prod.inv_mk,
    Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one, mul_inv_cancel]

theorem conj_mem_map_centralizer (T : StatedSp 2 K) {y x : StatedProj (StatedSp 2 K)}
    (hy : y ∈ centralizer {proj 2 K T}) (hx : x ∈ (centralizer {T}).map (proj 2 K)) :
    y * x * y⁻¹ ∈ (centralizer {T}).map (proj 2 K) := by
  obtain ⟨B, rfl⟩ := proj_surjective y
  obtain ⟨A, hA, rfl⟩ := hx
  let B' : (centralizer {proj 2 K T}).comap (proj 2 K) := ⟨B, mem_comap.mpr hy⟩
  have hAT : A * T * A⁻¹ * T⁻¹ = 1 := by
    rw [mem_centralizer_singleton_iff.mp hA]
    group
  let A' : (centralizer {proj 2 K T}).comap (proj 2 K) :=
    ⟨A, mem_comap.mpr (map_centralizer_le T ⟨A, hA, rfl⟩)⟩
  have hA1 : twist T A' = 1 := Subtype.ext hAT
  have h1 : twist T (B' * A' * B'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, hA1, mul_one, mul_inv_cancel]
  refine ⟨B * A * B⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  have h3 : (B * A * B⁻¹) * T * (B * A * B⁻¹)⁻¹ * T⁻¹ = 1 := congrArg Subtype.val h1
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
  have h4 : (B * A * B⁻¹) * T * (B * A * B⁻¹)⁻¹ = T := by rwa [mul_inv_eq_one] at h3
  calc (B * A * B⁻¹) * T = ((B * A * B⁻¹) * T * (B * A * B⁻¹)⁻¹) * (B * A * B⁻¹) := by group
    _ = T * (B * A * B⁻¹) := by rw [h4]

theorem isSolvable_SL2_of_card_three [Finite K] (hK : Nat.card K = 3) :
    Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have : Fintype K := Fintype.ofFinite K
  have hFcard : Fintype.card K = 3 := by
    simpa [Nat.card_eq_fintype_card] using hK
  let eK : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_three hFcard
  let eP : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* alternatingGroup (Fin 4) :=
    (CFSG.GorensteinWalter.psl2RingEquiv eK).symm.trans
      CFSG.GorensteinWalter.psl2_three_equiv_alternatingGroup
  have : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup.isSolvable (by simp)
  have : Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    Group.isSolvable_of_isSolvable_injective (f := eP.toMonoidHom) eP.injective
  exact Group.isSolvable_of_ker_le_range (center (Matrix.SpecialLinearGroup (Fin 2) K)).subtype
    (QuotientGroup.mk' (center (Matrix.SpecialLinearGroup (Fin 2) K)))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem isSolvable_X0_of_card_three [Finite K] (h2 : (2 : K) ≠ 0) (hK : Nat.card K = 3) :
    Group.IsSolvable (X0 K) := by
  have := isSolvable_SL2_of_card_three hK
  have hrange : ((proj 2 K).comp (blkSL K)).range = X0 K := by
    ext x
    rw [mem_X0 h2, MonoidHom.mem_range]
    rfl
  let f := ((proj 2 K).comp (blkSL K)).rangeRestrict
  have hf : Function.Surjective f := MonoidHom.rangeRestrict_surjective _
  have : Group.IsSolvable ((proj 2 K).comp (blkSL K)).range :=
    Group.isSolvable_of_surjective hf
  rw [hrange] at this
  exact this

end CFSG.ComponentClassification.CatFactsSp4
