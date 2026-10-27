module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTModel
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphPlane
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeGen

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear blockMatrix
  blockMatrix_apply blockMatrix_mul blockMatrix_one)
open scoped MatrixGroups

section BlockMat

variable {K : Type} [Field K] {n : ℕ} (W : Finset (Fin n))

@[expose] noncomputable def ctBlockMat (M : Matrix (Fin W.card) (Fin W.card) K) : Matrix (Fin n) (Fin n) K :=
  blockMatrix W (reindex W.equivFin.symm W.equivFin.symm M)

theorem ctBlockMat_mul (M M' : Matrix (Fin W.card) (Fin W.card) K) :
    ctBlockMat W (M * M') = ctBlockMat W M * ctBlockMat W M' := by
  rw [ctBlockMat, ctBlockMat, ctBlockMat, ← blockMatrix_mul]
  congr 1
  exact (reindexAlgEquiv K K W.equivFin.symm).map_mul M M'

theorem ctBlockMat_one : ctBlockMat W (1 : Matrix (Fin W.card) (Fin W.card) K) = 1 := by
  rw [ctBlockMat, reindex_apply, submatrix_one_equiv, blockMatrix_one]

theorem ctBlockMat_apply (M : Matrix (Fin W.card) (Fin W.card) K) (a b : Fin n) :
    ctBlockMat W M a b = if h : a ∈ W ∧ b ∈ W then M (W.equivFin ⟨a, h.1⟩) (W.equivFin ⟨b, h.2⟩)
      else (1 : Matrix (Fin n) (Fin n) K) a b := by
  rw [ctBlockMat, blockMatrix_apply]
  split_ifs with h
  · rw [reindex_apply, submatrix_apply]
    rfl
  · rfl

theorem ctBlockMat_map (σ : K ≃+* K) (M : Matrix (Fin W.card) (Fin W.card) K) :
    ctBlockMat W (M.map σ) = (ctBlockMat W M).map σ := by
  ext a b
  rw [map_apply, ctBlockMat_apply, ctBlockMat_apply]
  split_ifs with h
  · rfl
  · by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

theorem ctBlockMat_transpose (M : Matrix (Fin W.card) (Fin W.card) K) :
    ctBlockMat W Mᵀ = (ctBlockMat W M)ᵀ := by
  ext a b
  rw [transpose_apply, ctBlockMat_apply, ctBlockMat_apply]
  by_cases h : a ∈ W ∧ b ∈ W
  · simp only [h, and_self, ↓reduceDIte, transpose_apply]
  · have h' : ¬(b ∈ W ∧ a ∈ W) := fun h' => h ⟨h'.2, h'.1⟩
    simp only [h, h', ↓reduceDIte, Matrix.one_apply, eq_comm]

@[expose] noncomputable def ctBlockEquiv :
    SpecialLinearGroup (Fin W.card) K ≃* blockSpecialLinear (K := K) W :=
  (LinearPilot.reindexSpecialLinear W.equivFin).symm.trans
    ((MonoidHom.ofInjective (LinearPilot.blockEmbed_injective W)).trans
      (MulEquiv.subgroupCongr (LinearPilot.range_blockEmbed W)))

theorem coe_ctBlockEquiv (g : SpecialLinearGroup (Fin W.card) K) :
    (((ctBlockEquiv W g : blockSpecialLinear (K := K) W) : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = ctBlockMat W g :=
  rfl

theorem ctBlockMat_mul_inv (A : GL (Fin W.card) K) :
    ctBlockMat W (A : Matrix (Fin W.card) (Fin W.card) K) *
      ctBlockMat W ((A⁻¹ : GL (Fin W.card) K) : Matrix (Fin W.card) (Fin W.card) K) = 1 := by
  rw [← ctBlockMat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, ctBlockMat_one]

theorem ctBlockMat_inv_mul (A : GL (Fin W.card) K) :
    ctBlockMat W ((A⁻¹ : GL (Fin W.card) K) : Matrix (Fin W.card) (Fin W.card) K) *
      ctBlockMat W (A : Matrix (Fin W.card) (Fin W.card) K) = 1 := by
  rw [← ctBlockMat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, ctBlockMat_one]

@[expose] noncomputable def ctBlockGL : GL (Fin W.card) K →* GL (Fin n) K where
  toFun A := Units.mk (ctBlockMat W (A : Matrix (Fin W.card) (Fin W.card) K))
    (ctBlockMat W ((A⁻¹ : GL (Fin W.card) K) : Matrix (Fin W.card) (Fin W.card) K))
    (ctBlockMat_mul_inv W A) (ctBlockMat_inv_mul W A)
  map_one' := by
    ext1
    change ctBlockMat W ((1 : GL (Fin W.card) K) : Matrix (Fin W.card) (Fin W.card) K) = 1
    rw [Units.val_one]
    exact ctBlockMat_one W
  map_mul' A B := by
    ext1
    change ctBlockMat W ((A * B : GL (Fin W.card) K) : Matrix (Fin W.card) (Fin W.card) K) =
      ctBlockMat W (A : Matrix (Fin W.card) (Fin W.card) K) *
        ctBlockMat W (B : Matrix (Fin W.card) (Fin W.card) K)
    rw [Units.val_mul]
    exact ctBlockMat_mul W _ _

theorem coe_ctBlockGL (A : GL (Fin W.card) K) :
    ((ctBlockGL W A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ctBlockMat W A :=
  rfl

theorem coe_ctBlockGL_inv (A : GL (Fin W.card) K) :
    (((ctBlockGL W A)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ctBlockMat W ((A⁻¹ : GL (Fin W.card) K) : Matrix _ _ K) := by
  rw [← map_inv, coe_ctBlockGL]

end BlockMat

section Form

variable {K : Type} [Field K] [Finite K] {n : ℕ} (W : Finset (Fin n))

theorem exists_matrix_form_of_mulAut_block (h3 : 3 ≤ W.card)
    (θ : MulAut (blockSpecialLinear (K := K) W)) :
    ∃ (A₀ : GL (Fin W.card) K) (σ : K ≃+* K),
      (∀ x : blockSpecialLinear (K := K) W,
        (((θ x : blockSpecialLinear (K := K) W) : SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) = ((ctBlockGL W A₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)).map σ *
              (((ctBlockGL W A₀)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ∨
      (∀ x : blockSpecialLinear (K := K) W,
        (((θ x : blockSpecialLinear (K := K) W) : SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) = ((ctBlockGL W A₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((((x⁻¹ : blockSpecialLinear (K := K) W) : SpecialLinearGroup (Fin n) K) :
              Matrix (Fin n) (Fin n) K))ᵀ.map σ *
              (((ctBlockGL W A₀)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  set ι := ctBlockEquiv (K := K) W with hι
  set θ' : MulAut (SpecialLinearGroup (Fin W.card) K) := MulAut.congr ι.symm θ with hθ'
  obtain ⟨A₀, σ, h⟩ := CFSG.RankThree.PartOne.AUTSL.exists_matrix_form_of_mulAut_sl h3 θ'
  refine ⟨A₀, σ, ?_⟩
  have hx : ∀ x, θ x = ι (θ' (ι.symm x)) := by
    intro x
    simp [hθ', MulAut.congr_apply]
  have hιm : ∀ x : blockSpecialLinear (K := K) W,
      ctBlockMat W ((ι.symm x : SpecialLinearGroup (Fin W.card) K) :
        Matrix (Fin W.card) (Fin W.card) K) =
        ((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    intro x
    rw [← coe_ctBlockEquiv, MulEquiv.apply_symm_apply]
  rcases h with h | h
  · left
    intro x
    rw [hx x, coe_ctBlockEquiv, h, ctBlockMat_mul, ctBlockMat_mul, ctBlockMat_map, hιm,
      coe_ctBlockGL, coe_ctBlockGL_inv]
  · right
    intro x
    rw [hx x, coe_ctBlockEquiv, h, ctBlockMat_mul, ctBlockMat_mul, ctBlockMat_map,
      ctBlockMat_transpose, ← map_inv, hιm, coe_ctBlockGL, coe_ctBlockGL_inv]

end Form

section Commute

variable {K : Type} [Field K] {n : ℕ}

theorem col_row_of_commute_single {M : Matrix (Fin n) (Fin n) K} {a b : Fin n}
    (h : M * single a b (1 : K) = single a b 1 * M) :
    (∀ i, M i a = if i = a then M b b else 0) ∧ (∀ j, M b j = if j = b then M a a else 0) := by
  constructor
  · intro i
    have h1 := congrFun (congrFun h i) b
    rw [mul_single_apply_same, mul_one] at h1
    by_cases hi : i = a
    · subst hi
      rw [ite_eq_left rfl, h1, single_mul_apply_same, one_mul]
    · rw [ite_eq_right hi, h1, single_mul_apply_of_ne _ _ _ _ _ hi]
  · intro j
    have h1 := congrFun (congrFun h a) j
    rw [single_mul_apply_same, one_mul] at h1
    by_cases hj : j = b
    · subst hj
      rw [ite_eq_left rfl, ← h1, mul_single_apply_same, mul_one]
    · rw [ite_eq_right hj, ← h1, mul_single_apply_of_ne _ _ _ _ _ hj]

theorem commute_of_commute_one_add {M X : Matrix (Fin n) (Fin n) K}
    (h : M * (1 + X) = (1 + X) * M) : M * X = X * M := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
  exact add_left_cancel h

theorem mul_apply_of_row {M : Matrix (Fin n) (Fin n) K} {a : Fin n} {c : K}
    (h : ∀ j, M a j = if j = a then c else 0) (X : Matrix (Fin n) (Fin n) K) (b : Fin n) :
    (M * X) a b = c * X a b := by
  rw [mul_apply, Finset.sum_eq_single a (fun k _ hk => by rw [h k, ite_eq_right hk, zero_mul])
    (fun h' => absurd (Finset.mem_univ a) h'), h a, ite_eq_left rfl]

theorem mul_apply_of_col {M : Matrix (Fin n) (Fin n) K} {b : Fin n} {c : K}
    (h : ∀ i, M i b = if i = b then c else 0) (X : Matrix (Fin n) (Fin n) K) (a : Fin n) :
    (X * M) a b = X a b * c := by
  rw [mul_apply, Finset.sum_eq_single b (fun k _ hk => by rw [h k, ite_eq_right hk, mul_zero])
    (fun h' => absurd (Finset.mem_univ b) h'), h b, ite_eq_left rfl]

theorem mul_apply_of_row_perm {M : Matrix (Fin n) (Fin n) K} {a a' : Fin n}
    (h : ∀ j, M a j = if j = a' then 1 else 0) (X : Matrix (Fin n) (Fin n) K) (b : Fin n) :
    (M * X) a b = X a' b := by
  rw [mul_apply, Finset.sum_eq_single a' (fun k _ hk => by rw [h k, ite_eq_right hk, zero_mul])
    (fun h' => absurd (Finset.mem_univ a') h'), h a', ite_eq_left rfl, one_mul]

theorem mul_apply_of_col_perm {M : Matrix (Fin n) (Fin n) K} {b b' : Fin n}
    (h : ∀ i, M i b = if i = b' then 1 else 0) (X : Matrix (Fin n) (Fin n) K) (a : Fin n) :
    (X * M) a b = X a b' := by
  rw [mul_apply, Finset.sum_eq_single b' (fun k _ hk => by rw [h k, ite_eq_right hk, mul_zero])
    (fun h' => absurd (Finset.mem_univ b') h'), h b', ite_eq_left rfl, mul_one]

end Commute

section SpCommute

variable {K : Type} [Field K] [CharP K 2] {N ε : ℕ}

noncomputable abbrev ctE (N ε : ℕ) (p : Fin N) : Fin (2 * N + ε) := q2Coord N ε (Sum.inl (Sum.inl p))

noncomputable abbrev ctF (N ε : ℕ) (p : Fin N) : Fin (2 * N + ε) := q2Coord N ε (Sum.inl (Sum.inr p))

theorem ctE_injective : Function.Injective (ctE N ε) := fun _ _ h =>
  Sum.inl.inj (Sum.inl.inj ((q2Coord N ε).injective h))

theorem ctF_injective : Function.Injective (ctF N ε) := fun _ _ h =>
  Sum.inr.inj (Sum.inl.inj ((q2Coord N ε).injective h))

theorem ctE_ne_ctF (p q : Fin N) : ctE N ε p ≠ ctF N ε q := fun h =>
  Sum.inl_ne_inr (Sum.inl.inj ((q2Coord N ε).injective h))

theorem coe_ctEmbed_elt_difference {p q : Fin N} (hpq : p ≠ q) (c : K) :
    ((ctEmbed ε (CFSG.LieType.Universal.Symplectic.SpExtras.elt (.difference p q hpq) c) :
      SpecialLinearGroup (Fin (2 * N + ε)) K) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) =
        1 + (single (ctE N ε p) (ctE N ε q) c + single (ctF N ε q) (ctF N ε p) c) := by
  ext a b
  obtain ⟨w, rfl⟩ := (q2Coord N ε).surjective a
  obtain ⟨w', rfl⟩ := (q2Coord N ε).surjective b
  rw [ctEmbed_apply_q2Coord, CFSG.LieType.Universal.Symplectic.SpExtras.mat_elt]
  simp only [CFSG.LieType.Universal.Symplectic.SpExtras.E, Matrix.add_apply, single_apply,
    (q2Coord N ε).injective.eq_iff, ctE, ctF]
  rcases w with u | i <;> rcases w' with v | j
  · rw [fromBlocks_apply₁₁]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, single_apply,
      Matrix.one_apply, Sum.inl.injEq, smul_eq_mul]
    by_cases h1 : Sum.inl p = u <;> by_cases h2 : Sum.inl q = v <;>
      by_cases h3 : Sum.inr q = u <;> by_cases h4 : Sum.inr p = v <;>
        simp_all [CharTwo.sub_eq_add, CharTwo.add_self_eq_zero]
  · rw [fromBlocks_apply₁₂]
    simp
  · rw [fromBlocks_apply₂₁]
    simp
  · rw [fromBlocks_apply₂₂]
    simp [Matrix.one_apply]

omit [CharP K 2] in
theorem rowcol_of_commute_ctSp {M : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K}
    {R : Finset (Fin N)} {p₀ : Fin N} (hp₀ : p₀ ∉ R)
    (hU : ∀ p, p ∉ R → M * single (ctE N ε p) (ctF N ε p) 1 =
      single (ctE N ε p) (ctF N ε p) 1 * M)
    (hL : ∀ p, p ∉ R → M * single (ctF N ε p) (ctE N ε p) 1 =
      single (ctF N ε p) (ctE N ε p) 1 * M)
    (hD : ∀ p q, p ∉ R → q ∉ R → p ≠ q →
      M * (single (ctE N ε p) (ctE N ε q) 1 + single (ctF N ε q) (ctF N ε p) 1) =
        (single (ctE N ε p) (ctE N ε q) 1 + single (ctF N ε q) (ctF N ε p) 1) * M) :
    ∀ p, p ∉ R → ∀ a, (a = ctE N ε p ∨ a = ctF N ε p) →
      (∀ i, M i a = if i = a then M (ctE N ε p₀) (ctE N ε p₀) else 0) ∧
        (∀ j, M a j = if j = a then M (ctE N ε p₀) (ctE N ε p₀) else 0) := by
  have hplane : ∀ p, p ∉ R → ∀ a, (a = ctE N ε p ∨ a = ctF N ε p) →
      (∀ i, M i a = if i = a then M (ctE N ε p) (ctE N ε p) else 0) ∧
        (∀ j, M a j = if j = a then M (ctE N ε p) (ctE N ε p) else 0) := by
    intro p hp a ha
    obtain ⟨hcU, hrU⟩ := col_row_of_commute_single (hU p hp)
    obtain ⟨hcL, hrL⟩ := col_row_of_commute_single (hL p hp)
    have hef : M (ctE N ε p) (ctE N ε p) = M (ctF N ε p) (ctF N ε p) := by
      have := hcU (ctE N ε p)
      rwa [ite_eq_left rfl] at this
    rcases ha with rfl | rfl
    · exact ⟨fun i => by rw [hcU i, ← hef], fun j => by rw [hrL j, ← hef]⟩
    · exact ⟨fun i => by rw [hcL i], fun j => by rw [hrU j]⟩
  have hlam : ∀ p, p ∉ R → M (ctE N ε p) (ctE N ε p) = M (ctE N ε p₀) (ctE N ε p₀) := by
    intro p hp
    by_cases hpp : p = p₀
    · rw [hpp]
    have h1 := congrFun (congrFun (hD p p₀ hp hp₀ hpp) (ctE N ε p)) (ctE N ε p₀)
    rw [mul_apply_of_row (hplane p hp _ (Or.inl rfl)).2,
      mul_apply_of_col (hplane p₀ hp₀ _ (Or.inl rfl)).1] at h1
    have hD1 : ((single (ctE N ε p) (ctE N ε p₀) (1 : K) + single (ctF N ε p₀) (ctF N ε p) 1 :
        Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K)) (ctE N ε p) (ctE N ε p₀) = 1 := by
      rw [Matrix.add_apply, single_apply_same, single_apply_of_row_ne (ctE_ne_ctF _ _).symm,
        add_zero]
    rw [hD1, mul_one, one_mul] at h1
    exact h1
  intro p hp a ha
  rw [← hlam p hp]
  exact hplane p hp a ha

theorem coe_ctEmbed_longBlock_upper (p : Fin N) (c : K) :
    ((ctEmbed ε (longBlock K N p (CFSG.LieType.Steinberg.sl2Upper c)) :
      SpecialLinearGroup (Fin (2 * N + ε)) K) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) =
        1 + single (ctE N ε p) (ctF N ε p) c := by
  rw [ctEmbed_longBlock, pairEmbed_sl2Upper]
  rfl

theorem coe_ctEmbed_longBlock_lower (p : Fin N) (c : K) :
    ((ctEmbed ε (longBlock K N p (CFSG.LieType.Steinberg.sl2Lower c)) :
      SpecialLinearGroup (Fin (2 * N + ε)) K) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) =
        1 + single (ctF N ε p) (ctE N ε p) c := by
  rw [ctEmbed_longBlock, pairEmbed_sl2Lower]
  rfl

omit [CharP K 2] in
theorem map_one_add_single {n : ℕ} (σ : K ≃+* K) (a b : Fin n) (c : K) :
    ((1 : Matrix (Fin n) (Fin n) K) + single a b c).map σ = 1 + single a b (σ c) := by
  ext i j
  simp only [map_apply, Matrix.add_apply, Matrix.one_apply, single_apply]
  split_ifs <;> simp_all

omit [CharP K 2] in
theorem map_one_add_single_add_single {n : ℕ} (σ : K ≃+* K) (a b a' b' : Fin n) :
    ((1 : Matrix (Fin n) (Fin n) K) + (single a b 1 + single a' b' 1)).map σ =
      1 + (single a b 1 + single a' b' 1) := by
  ext i j
  simp only [map_apply, Matrix.add_apply, Matrix.one_apply, single_apply]
  split_ifs <;> simp_all

theorem eq_one_and_rowcol_of_fix_ctSp [Finite K] {R : Finset (Fin N)} {p₀ : Fin N}
    (hp₀ : p₀ ∉ R) {M : GL (Fin (2 * N + ε)) K} {σ : K ≃+* K}
    (h : ∀ y ∈ spBlock K Rᶜ, (M : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) *
      ((ctEmbed ε y : SpecialLinearGroup (Fin (2 * N + ε)) K) :
        Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K).map σ =
      ((ctEmbed ε y : SpecialLinearGroup (Fin (2 * N + ε)) K) :
        Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) * M) :
    σ = 1 ∧ (M : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) (ctE N ε p₀) (ctE N ε p₀) ≠ 0 ∧
      ∀ p, p ∉ R → ∀ a, (a = ctE N ε p ∨ a = ctF N ε p) →
        (∀ i, (M : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) i a =
          if i = a then (M : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K)
            (ctE N ε p₀) (ctE N ε p₀) else 0) ∧
        (∀ j, (M : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) a j =
          if j = a then (M : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K)
            (ctE N ε p₀) (ctE N ε p₀) else 0) := by
  set A := (M : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) with hA
  have hmem : ∀ p, p ∉ R → p ∈ Rᶜ := fun p hp => Finset.mem_compl.2 hp
  have hU : ∀ p, p ∉ R → A * single (ctE N ε p) (ctF N ε p) 1 =
      single (ctE N ε p) (ctF N ε p) 1 * A := by
    intro p hp
    have h1 := h _ (longBlock_mem_spBlock (hmem p hp) (CFSG.LieType.Steinberg.sl2Upper 1))
    rw [coe_ctEmbed_longBlock_upper, map_one_add_single, map_one] at h1
    exact commute_of_commute_one_add h1
  have hL : ∀ p, p ∉ R → A * single (ctF N ε p) (ctE N ε p) 1 =
      single (ctF N ε p) (ctE N ε p) 1 * A := by
    intro p hp
    have h1 := h _ (longBlock_mem_spBlock (hmem p hp) (CFSG.LieType.Steinberg.sl2Lower 1))
    rw [coe_ctEmbed_longBlock_lower, map_one_add_single, map_one] at h1
    exact commute_of_commute_one_add h1
  have hD : ∀ p q, p ∉ R → q ∉ R → p ≠ q →
      A * (single (ctE N ε p) (ctE N ε q) 1 + single (ctF N ε q) (ctF N ε p) 1) =
        (single (ctE N ε p) (ctE N ε q) 1 + single (ctF N ε q) (ctF N ε p) 1) * A := by
    intro p q hp hq hpq
    have h1 := h _ (elt_difference_mem_spBlock hpq (hmem p hp) (hmem q hq) 1)
    rw [coe_ctEmbed_elt_difference, map_one_add_single_add_single] at h1
    exact commute_of_commute_one_add h1
  have hrc := rowcol_of_commute_ctSp hp₀ hU hL hD
  have hne : A (ctE N ε p₀) (ctE N ε p₀) ≠ 0 := by
    intro h0
    apply Matrix.GeneralLinearGroup.det_ne_zero M
    refine Matrix.det_eq_zero_of_row_eq_zero (ctE N ε p₀) fun j => ?_
    show A (ctE N ε p₀) j = 0
    rw [(hrc p₀ hp₀ _ (Or.inl rfl)).2 j]
    split_ifs
    · exact h0
    · rfl
  refine ⟨?_, hne, hrc⟩
  refine RingEquiv.ext fun c => ?_
  have h1 := h _ (longBlock_mem_spBlock (hmem p₀ hp₀) (CFSG.LieType.Steinberg.sl2Upper c))
  rw [coe_ctEmbed_longBlock_upper, map_one_add_single] at h1
  have h2 := congrFun (congrFun h1 (ctE N ε p₀)) (ctF N ε p₀)
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.add_apply,
    Matrix.add_apply, mul_single_apply_same, single_mul_apply_same,
    (hrc p₀ hp₀ _ (Or.inr rfl)).2 (ctF N ε p₀), ite_eq_left rfl,
    (hrc p₀ hp₀ _ (Or.inl rfl)).2 (ctF N ε p₀), ite_eq_right (ctE_ne_ctF _ _).symm] at h2
  have h3 : A (ctE N ε p₀) (ctE N ε p₀) * (σ c - c) = 0 := by linear_combination h2
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact absurd h4 hne
  · exact sub_eq_zero.1 h4

end SpCommute

section Rigid

variable {K : Type} [Field K] [CharP K 2] [Finite K] {N : ℕ}

omit [CharP K 2] [Finite K] in
theorem exists_plane_of_mem_compl {R : Finset (Fin N)} {a : Fin (2 * N + 0)}
    (ha : a ∈ (planeCoordsQ2 0 R)ᶜ) : ∃ p, p ∉ R ∧ (a = ctE N 0 p ∨ a = ctF N 0 p) := by
  obtain ⟨w, rfl⟩ := (q2Coord N 0).surjective a
  rw [Finset.mem_compl, q2Coord_mem_planeCoordsQ2] at ha
  rcases w with (u | u) | i
  · exact ⟨u, ha, Or.inl rfl⟩
  · exact ⟨u, ha, Or.inr rfl⟩
  · exact i.elim0

omit [CharP K 2] [Finite K] in
theorem ctBlockGL_apply_of_notMem {n : ℕ} {W : Finset (Fin n)} (A : GL (Fin W.card) K)
    {a : Fin n} (ha : a ∉ W) :
    (∀ j, ((ctBlockGL W A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a j =
      if j = a then 1 else 0) ∧
    (∀ i, ((ctBlockGL W A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i a =
      if i = a then 1 else 0) := by
  refine ⟨fun j => ?_, fun i => ?_⟩
  · rw [coe_ctBlockGL, ctBlockMat_apply, dite_eq_right (fun h => ha h.1), Matrix.one_apply]
    simp only [eq_comm]
  · rw [coe_ctBlockGL, ctBlockMat_apply, dite_eq_right (fun h => ha h.2), Matrix.one_apply]

omit [CharP K 2] [Finite K] in
theorem apply_eq_zero_of_mem_blockSpecialLinear {n : ℕ} {W : Finset (Fin n)}
    {x : SpecialLinearGroup (Fin n) K} (hx : x ∈ blockSpecialLinear W) {i j : Fin n}
    (hij : i ≠ j) (h : i ∉ W ∨ j ∉ W) : (x : Matrix (Fin n) (Fin n) K) i j = 0 := by
  rw [(mem_blockSpecialLinear.mp hx) i j h, Matrix.one_apply_ne hij]

theorem eq_one_of_fix_of_conj_form {R : Finset (Fin N)} {p₀ : Fin N} (hp₀ : p₀ ∉ R)
    (θ : MulAut (q2Block 0 K R)) (hθ : ∀ s ∈ ctSpBlock 0 K R, θ s = s)
    (A₀ : GL (Fin ((planeCoordsQ2 0 R)ᶜ.card)) K) (σ : K ≃+* K)
    (h : ∀ x : q2Block 0 K R,
      (((θ x : q2Block 0 K R) : SpecialLinearGroup (Fin (2 * N + 0)) K) :
        Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K) =
        ((ctBlockGL (planeCoordsQ2 0 R)ᶜ A₀ : GL (Fin (2 * N + 0)) K) :
          Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K) *
          (((x : SpecialLinearGroup (Fin (2 * N + 0)) K) :
            Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K)).map σ *
          (((ctBlockGL (planeCoordsQ2 0 R)ᶜ A₀)⁻¹ : GL (Fin (2 * N + 0)) K) :
            Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K)) :
    θ = 1 := by
  set M : GL (Fin (2 * N + 0)) K := ctBlockGL (planeCoordsQ2 0 R)ᶜ A₀ with hM
  have hfix : ∀ y ∈ spBlock K Rᶜ, (M : Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K) *
      ((ctEmbed 0 y : SpecialLinearGroup (Fin (2 * N + 0)) K) :
        Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K).map σ =
      ((ctEmbed 0 y : SpecialLinearGroup (Fin (2 * N + 0)) K) :
        Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K) * M := by
    intro y hy
    have h1 := h ⟨ctEmbed 0 y, ctEmbed_mem_q2Block_iff.2 hy⟩
    rw [hθ _ (mem_ctSpBlock.2 ⟨y, hy, rfl⟩)] at h1
    have h2 := congrArg (· * (M : Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K)) h1
    simp only [Matrix.mul_assoc] at h2
    rw [Units.inv_mul, Matrix.mul_one] at h2
    exact h2.symm
  obtain ⟨hσ, -, hrc⟩ := eq_one_and_rowcol_of_fix_ctSp hp₀ hfix
  have hcomm : ∀ x : q2Block 0 K R, (M : Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K) *
      ((x : SpecialLinearGroup (Fin (2 * N + 0)) K) : Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K) =
      ((x : SpecialLinearGroup (Fin (2 * N + 0)) K) :
        Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K) * M := by
    intro x
    ext i j
    by_cases hi : i ∈ (planeCoordsQ2 0 R)ᶜ
    · obtain ⟨p, hp, hpi⟩ := exists_plane_of_mem_compl hi
      rw [mul_apply_of_row ((hrc p hp i hpi).2)]
      by_cases hj : j ∈ (planeCoordsQ2 0 R)ᶜ
      · obtain ⟨q, hq, hqj⟩ := exists_plane_of_mem_compl hj
        rw [mul_apply_of_col ((hrc q hq j hqj).1), mul_comm]
      · rw [mul_apply_of_col_perm ((ctBlockGL_apply_of_notMem A₀ hj).2),
          apply_eq_zero_of_mem_blockSpecialLinear x.2 (fun h' : i = j => hj (h' ▸ hi))
            (Or.inr hj), mul_zero]
    · rw [mul_apply_of_row_perm ((ctBlockGL_apply_of_notMem A₀ hi).1)]
      by_cases hj : j ∈ (planeCoordsQ2 0 R)ᶜ
      · obtain ⟨q, hq, hqj⟩ := exists_plane_of_mem_compl hj
        rw [mul_apply_of_col ((hrc q hq j hqj).1),
          apply_eq_zero_of_mem_blockSpecialLinear x.2 (fun h' : i = j => hi (h' ▸ hj))
            (Or.inl hi), zero_mul]
      · rw [mul_apply_of_col_perm ((ctBlockGL_apply_of_notMem A₀ hj).2)]
  refine MulEquiv.ext fun x => ?_
  rw [MulAut.one_apply]
  apply Subtype.ext
  apply Subtype.ext
  have hx := h x
  rw [hσ] at hx
  have hmap : (((x : SpecialLinearGroup (Fin (2 * N + 0)) K) :
      Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K)).map ((1 : K ≃+* K) : K → K) =
      ((x : SpecialLinearGroup (Fin (2 * N + 0)) K) :
        Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K) := by
    ext
    rfl
  rw [hmap, hcomm x, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at hx
  exact hx

omit [Finite K] in
theorem inv_transpose_ctEmbed {ε : ℕ} (y : StatedSp N K) :
    ((((ctEmbed ε y)⁻¹ : SpecialLinearGroup (Fin (2 * N + ε)) K) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K))ᵀ =
      q2GramMat ε * ((ctEmbed ε y : SpecialLinearGroup (Fin (2 * N + ε)) K) :
        Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) * q2GramMat ε := by
  have h1 := congrArg (fun z : SpecialLinearGroup (Fin (2 * N + ε)) K =>
    (z : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K)) (ctGraph_ctEmbed (ε := ε) y)
  simp only [coe_ctGraph] at h1
  rw [← h1]
  simp only [← Matrix.mul_assoc, q2GramMat_mul_self, Matrix.one_mul]
  rw [Matrix.mul_assoc, q2GramMat_mul_self, Matrix.mul_one]

omit [Finite K] in
theorem map_q2GramMat {ε : ℕ} (σ : K ≃+* K) :
    (q2GramMat (K := K) (N := N) ε).map σ = q2GramMat ε := by
  ext a b
  rw [map_apply, q2GramMat_apply]
  split_ifs <;> simp

theorem eq_ctGraphBlock_of_fix_of_dual_form {R : Finset (Fin N)} {p₀ : Fin N} (hp₀ : p₀ ∉ R)
    (θ : MulAut (q2Block 0 K R)) (hθ : ∀ s ∈ ctSpBlock 0 K R, θ s = s)
    (A₀ : GL (Fin ((planeCoordsQ2 0 R)ᶜ.card)) K) (σ : K ≃+* K)
    (h : ∀ x : q2Block 0 K R,
      (((θ x : q2Block 0 K R) : SpecialLinearGroup (Fin (2 * N + 0)) K) :
        Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K) =
        ((ctBlockGL (planeCoordsQ2 0 R)ᶜ A₀ : GL (Fin (2 * N + 0)) K) :
          Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K) *
          ((((x⁻¹ : q2Block 0 K R) : SpecialLinearGroup (Fin (2 * N + 0)) K) :
            Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K))ᵀ.map σ *
          (((ctBlockGL (planeCoordsQ2 0 R)ᶜ A₀)⁻¹ : GL (Fin (2 * N + 0)) K) :
            Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K)) :
    θ = ctGraphBlock 0 R := by
  set M : GL (Fin (2 * N + 0)) K := ctBlockGL (planeCoordsQ2 0 R)ᶜ A₀ with hM
  set P : Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K := q2GramMat 0 with hP
  set PG : GL (Fin (2 * N + 0)) K := SpecialLinearGroup.toGL (ctEmbed 0 (q2SpJ (N := N) (K := K)))
    with hPG
  have hPGm : (PG : Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K) = P := by
    change q2EmbedMat 0 (mat N K q2SpJ) = q2GramMat 0
    rw [mat_q2SpJ]
    rfl
  have hP2 : P * P = 1 := q2GramMat_mul_self
  set T : GL (Fin (2 * N + 0)) K := M * PG with hT
  have hTm : (T : Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K) =
      (M : Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K) * P := by
    rw [hT, Units.val_mul, hPGm]
  have hfix : ∀ y ∈ spBlock K Rᶜ, (T : Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K) *
      ((ctEmbed 0 y : SpecialLinearGroup (Fin (2 * N + 0)) K) :
        Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K).map σ =
      ((ctEmbed 0 y : SpecialLinearGroup (Fin (2 * N + 0)) K) :
        Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K) * T := by
    intro y hy
    have h1 := h ⟨ctEmbed 0 y, ctEmbed_mem_q2Block_iff.2 hy⟩
    rw [hθ _ (mem_ctSpBlock.2 ⟨y, hy, rfl⟩)] at h1
    change ((ctEmbed 0 y : SpecialLinearGroup (Fin (2 * N + 0)) K) :
      Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K) =
      (M : Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K) *
        ((((ctEmbed 0 y)⁻¹ : SpecialLinearGroup (Fin (2 * N + 0)) K) :
          Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K))ᵀ.map σ *
        ((M⁻¹ : GL (Fin (2 * N + 0)) K) : Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K) at h1
    rw [inv_transpose_ctEmbed, Matrix.map_mul, Matrix.map_mul, map_q2GramMat] at h1
    rw [hTm]
    conv_rhs => rw [h1]
    rw [← hP]
    simp only [Matrix.mul_assoc]
    rw [Units.inv_mul_cancel_left, hP2, Matrix.mul_one]
  obtain ⟨hσ, -, hrc⟩ := eq_one_and_rowcol_of_fix_ctSp hp₀ hfix
  have hparW : ∀ a, a ∉ (planeCoordsQ2 0 R)ᶜ → q2Par N 0 a ∉ (planeCoordsQ2 0 R)ᶜ := by
    intro a ha
    rw [Finset.mem_compl, not_not] at ha ⊢
    exact q2Par_mem_planeCoordsQ2.2 ha
  have hoffT : ∀ a, a ∉ (planeCoordsQ2 0 R)ᶜ →
      (∀ j, (T : Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K) a j =
        if j = q2Par N 0 a then 1 else 0) ∧
      (∀ i, (T : Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K) i a =
        if i = q2Par N 0 a then 1 else 0) := by
    intro a ha
    refine ⟨fun j => ?_, fun i => ?_⟩
    · rw [hTm, mul_apply_of_row_perm ((ctBlockGL_apply_of_notMem A₀ ha).1), hP,
        q2GramMat_apply]
    · have hcol : ∀ k, P k a = if k = q2Par N 0 a then 1 else 0 := by
        intro k
        rw [hP, q2GramMat_apply]
        congr 1
        exact propext ⟨fun h => by rw [h, q2Par_q2Par], fun h => by rw [h, q2Par_q2Par]⟩
      rw [hTm, mul_apply_of_col_perm hcol, (ctBlockGL_apply_of_notMem A₀ (hparW a ha)).2 i]
  have hcommT : ∀ y : SpecialLinearGroup (Fin (2 * N + 0)) K, y ∈ q2Block 0 K R →
      (T : Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K) *
        (y : Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K) =
      (y : Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K) * T := by
    intro y hyB
    ext i j
    by_cases hi : i ∈ (planeCoordsQ2 0 R)ᶜ
    · obtain ⟨p, hp, hpi⟩ := exists_plane_of_mem_compl hi
      rw [mul_apply_of_row ((hrc p hp i hpi).2)]
      by_cases hj : j ∈ (planeCoordsQ2 0 R)ᶜ
      · obtain ⟨q, hq, hqj⟩ := exists_plane_of_mem_compl hj
        rw [mul_apply_of_col ((hrc q hq j hqj).1), mul_comm]
      · rw [mul_apply_of_col_perm ((hoffT j hj).2),
          apply_eq_zero_of_mem_blockSpecialLinear hyB (fun h' : i = j => hj (h' ▸ hi))
            (Or.inr hj),
          apply_eq_zero_of_mem_blockSpecialLinear hyB
            (fun h' : i = q2Par N 0 j => hparW j hj (h' ▸ hi)) (Or.inr (hparW j hj)), mul_zero]
    · rw [mul_apply_of_row_perm ((hoffT i hi).1)]
      by_cases hj : j ∈ (planeCoordsQ2 0 R)ᶜ
      · obtain ⟨q, hq, hqj⟩ := exists_plane_of_mem_compl hj
        rw [mul_apply_of_col ((hrc q hq j hqj).1),
          apply_eq_zero_of_mem_blockSpecialLinear hyB
            (fun h' : q2Par N 0 i = j => hparW i hi (h' ▸ hj)) (Or.inl (hparW i hi)),
          apply_eq_zero_of_mem_blockSpecialLinear hyB (fun h' : i = j => hi (h' ▸ hj))
            (Or.inl hi), zero_mul]
      · rw [mul_apply_of_col_perm ((hoffT j hj).2),
          (mem_blockSpecialLinear.mp hyB) _ _ (Or.inl (hparW i hi)),
          (mem_blockSpecialLinear.mp hyB) _ _ (Or.inl hi), Matrix.one_apply, Matrix.one_apply]
        congr 1
        exact propext ⟨fun h => by rw [← h, q2Par_q2Par], fun h => by rw [h, q2Par_q2Par]⟩
  refine MulEquiv.ext fun x => ?_
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_ctGraphBlock, coe_ctGraph]
  have hx := h x
  rw [hσ] at hx
  set z : Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K :=
    ((((x : SpecialLinearGroup (Fin (2 * N + 0)) K))⁻¹ : SpecialLinearGroup (Fin (2 * N + 0)) K) :
      Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K)ᵀ with hz
  have hmap : ((((x⁻¹ : q2Block 0 K R) : SpecialLinearGroup (Fin (2 * N + 0)) K) :
      Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K))ᵀ.map ((1 : K ≃+* K) : K → K) = z := by
    ext
    rfl
  rw [hmap] at hx
  rw [hx]
  have hy : ctGraph 0 (x : SpecialLinearGroup (Fin (2 * N + 0)) K) ∈ q2Block 0 K R :=
    ctGraph_mem_q2Block x.2
  have hc := hcommT _ hy
  rw [coe_ctGraph, ← hz, ← hP, hTm] at hc
  have h1 : (M : Matrix (Fin (2 * N + 0)) (Fin (2 * N + 0)) K) * z = P * z * P * M := by
    have h2 := congrArg (· * P) hc
    simp only [Matrix.mul_assoc] at h2
    rw [hP2, Matrix.mul_one, ← Matrix.mul_assoc P P z, hP2, Matrix.one_mul] at h2
    simpa only [Matrix.mul_assoc, Matrix.mul_one] using h2
  rw [h1, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem eq_one_or_eq_ctGraphBlock_of_fix {R : Finset (Fin N)}
    (h3 : 3 ≤ ((planeCoordsQ2 0 R)ᶜ).card) {p₀ : Fin N} (hp₀ : p₀ ∉ R)
    (θ : MulAut (q2Block 0 K R)) (hθ : ∀ s ∈ ctSpBlock 0 K R, θ s = s) :
    θ = 1 ∨ θ = ctGraphBlock 0 R := by
  obtain ⟨A₀, σ, h | h⟩ := exists_matrix_form_of_mulAut_block (K := K) (planeCoordsQ2 0 R)ᶜ h3 θ
  · exact Or.inl (eq_one_of_fix_of_conj_form hp₀ θ hθ A₀ σ h)
  · exact Or.inr (eq_ctGraphBlock_of_fix_of_dual_form hp₀ θ hθ A₀ σ h)

theorem eq_or_eq_ctGraph_of_range_eq {G : Type*} [Group G] {R : Finset (Fin N)}
    (h3 : 3 ≤ ((planeCoordsQ2 0 R)ᶜ).card) {p₀ : Fin N} (hp₀ : p₀ ∉ R)
    (φP φQ : q2Block 0 K R →* G) (hP : Function.Injective φP) (hQ : Function.Injective φQ)
    (hr : φP.range = φQ.range) (hS : ∀ s ∈ ctSpBlock 0 K R, φP s = φQ s) :
    (∀ x, φP x = φQ x) ∨ ∀ x, φP x = φQ (ctGraphBlock 0 R x) := by
  set θ : MulAut (q2Block 0 K R) := ((MonoidHom.ofInjective hP).trans
    (MulEquiv.subgroupCongr hr)).trans (MonoidHom.ofInjective hQ).symm with hθdef
  have hθ : ∀ y, φQ (θ y) = φP y := by
    intro y
    have h := (MonoidHom.ofInjective hQ).apply_symm_apply
      (MulEquiv.subgroupCongr hr (MonoidHom.ofInjective hP y))
    have h2 := congrArg Subtype.val h
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  rcases eq_one_or_eq_ctGraphBlock_of_fix h3 hp₀ θ
      (fun s hs => hQ ((hθ s).trans (hS s hs))) with h1 | h1
  · left
    intro x
    rw [← hθ x, h1, MulAut.one_apply]
  · right
    intro x
    rw [← hθ x, h1]

end Rigid

end CFSG.SeitzReduction.SymplecticPilot
