module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35Lift
public import CFSG.ClassicalInvolution.WeakCT.Center
public import CFSG.ClassicalInvolution.WeakCT.AutExtend
public import CFSG.LieType.Chevalley.RankOneGaussian

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35

open Matrix
open CFSG.LieType.Chevalley (SL2 WSL coe_WSL)
open CFSG.ClassicalInvolution.Phan (blockMat_mul blockMat_one)
open CFSG.ClassicalInvolution.WeakCT (blockSL coe_blockSL blockSL_comm eq_one_of_blockSL_mem_center
  map_blockMat transpose_blockMat)
open scoped commutatorElement MatrixGroups

theorem fixedBlocks_of_generators {P : Type*} [Group P] {p r : ℕ} {α : MulAut P}
    (a b : Fin r → P)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ ({a i, b i} : Set P), ∀ y ∈ ({a j, b j} : Set P), Commute x y)
    (ha : ∀ i, α (a i) = a i) (hb : ∀ i, α (b i) = b i) (hp : ∀ i, ⁅a i, b i⁆ ^ p = 1)
    (hnc : ∀ i, ¬ Commute ⁅a i, b i⁆ (b i)) : FixedBlocks p α r := by
  have hmem : ∀ i, a i ∈ Subgroup.closure ({a i, b i} : Set P) ∧
      b i ∈ Subgroup.closure ({a i, b i} : Set P) :=
    fun i => ⟨Subgroup.subset_closure (Set.mem_insert _ _),
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
  have hcl : ∀ i j, i ≠ j → Subgroup.closure ({a i, b i} : Set P) ≤
      Subgroup.centralizer (Subgroup.closure ({a j, b j} : Set P) : Set P) := fun i j hij => by
    rw [Subgroup.centralizer_closure, Subgroup.closure_le]
    exact fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => (hcomm i j hij x hx y hy).symm.eq
  refine ⟨fun i => Subgroup.closure {a i, b i}, fun i => ⁅a i, b i⁆, fun i j hij x hx y hy =>
    (Subgroup.mem_centralizer_iff.1 (hcl i j hij hx) y hy).symm, fun i x hx => ?_, fun i =>
    Subgroup.commutator_mem_commutator (hmem i).1 (hmem i).2, hp,
    fun i => ⟨b i, (hmem i).2, hnc i⟩⟩
  have hle : Subgroup.closure ({a i, b i} : Set P) ≤
      MonoidHom.eqLocus (α : P →* P) (MonoidHom.id P) :=
    (Subgroup.closure_le _).2 (by
      rintro _ (rfl | rfl)
      · exact ha i
      · exact hb i)
  exact hle hx

variable {n : ℕ} {K : Type} [Field K]

theorem two_mul_add_two_le (hn : 8 ≤ n) (i : Fin 4) : 2 * (i : ℕ) + 2 ≤ n := by
  have := i.isLt
  omega

theorem blockSL_two_mul_commute (hn : 8 ≤ n) {i j : Fin 4} (hij : i ≠ j) (g g' : SL(2, K)) :
    Commute (blockSL K n 2 (2 * i) (two_mul_add_two_le hn i) g)
      (blockSL K n 2 (2 * j) (two_mul_add_two_le hn j) g') :=
  blockSL_comm _ _ (by have : (i : ℕ) ≠ j := fun h => hij (Fin.ext h); omega) g g'

theorem map_blockSL {m k i : ℕ} (h : i + k ≤ m) (σ : K →+* K) (g : SL(k, K)) :
    Matrix.SpecialLinearGroup.map σ (blockSL K m k i h g) =
      blockSL K m k i h (Matrix.SpecialLinearGroup.map σ g) :=
  Subtype.ext (map_blockMat σ _)

theorem blockSL_unitary {m k i : ℕ} (h : i + k ≤ m) (σ : K →+* K) (g : SL(k, K))
    (hg : ((g : Matrix (Fin k) (Fin k) K).map σ)ᵀ * (g : Matrix (Fin k) (Fin k) K) = 1) :
    ((blockSL K m k i h g : Matrix (Fin m) (Fin m) K).map σ)ᵀ *
      (blockSL K m k i h g : Matrix (Fin m) (Fin m) K) = 1 := by
  rw [coe_blockSL, map_blockMat, transpose_blockMat, ← blockMat_mul h, hg, blockMat_one]

theorem eq_one_of_blockSL_eq_scalar {m k i : ℕ} (h : i + k ≤ m) (hk : k < m) {g : SL(k, K)}
    {c : K} (hc : (blockSL K m k i h g : Matrix (Fin m) (Fin m) K) = Matrix.scalar (Fin m) c) :
    g = 1 := by
  refine eq_one_of_blockSL_mem_center h hk
    (Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨c, ?_, hc.symm⟩)
  have hdet := Matrix.SpecialLinearGroup.det_coe (blockSL K m k i h g)
  rwa [hc, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ] at hdet

@[expose] def omegaSL (ω : K) (hω : ω ^ 3 = 1) : SL2 K :=
  ⟨!![ω ^ 2, 0; 0, ω], by rw [Matrix.det_fin_two_of]; linear_combination hω⟩

theorem coe_omegaSL (ω : K) (hω : ω ^ 3 = 1) :
    (omegaSL ω hω : Matrix (Fin 2) (Fin 2) K) = !![ω ^ 2, 0; 0, ω] :=
  rfl

theorem coe_comm_omegaSL_WSL (ω : K) (hω : ω ^ 3 = 1) :
    ((⁅omegaSL ω hω, WSL⁆ : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![ω, 0; 0, ω ^ 2] := by
  rw [commutatorElement_def, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.SpecialLinearGroup.coe_inv, coe_omegaSL, coe_WSL, Matrix.adjugate_fin_two_of,
    Matrix.adjugate_fin_two_of,
    Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext k l
  fin_cases k <;> fin_cases l <;> simp <;>
    first | linear_combination | linear_combination ω * hω

theorem comm_omegaSL_WSL_pow_three (ω : K) (hω : ω ^ 3 = 1) :
    (⁅omegaSL ω hω, WSL⁆ : SL2 K) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_comm_omegaSL_WSL, Matrix.SpecialLinearGroup.coe_one,
    pow_three', Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.one_fin_two]
  ext k l
  fin_cases k <;> fin_cases l <;> simp <;>
    first | linear_combination | linear_combination hω | linear_combination (ω ^ 3 + 1) * hω

theorem not_commute_comm_omegaSL_WSL (ω : K) (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ¬ Commute (⁅omegaSL ω hω, WSL⁆ : SL2 K) WSL := by
  intro hc
  have h : ((⁅omegaSL ω hω, WSL⁆ * WSL : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 1 =
      ((WSL * ⁅omegaSL ω hω, WSL⁆ : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 1 := by
    rw [hc.eq]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_comm_omegaSL_WSL,
    coe_WSL, Matrix.mul_fin_two, Matrix.mul_fin_two] at h
  simp at h
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω
  have h' : ω * (ω - 1) = 0 := by
    first | linear_combination -h | linear_combination h
  rcases mul_eq_zero.1 h' with h0 | h1
  · exact hω0 h0
  · exact hω1 (sub_eq_zero.1 h1)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35
