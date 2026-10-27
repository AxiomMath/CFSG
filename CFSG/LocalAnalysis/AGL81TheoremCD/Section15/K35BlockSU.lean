module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35BlockSL
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LieType.Chevalley (SL2 WSL coe_WSL)
open CFSG.ClassicalInvolution.WeakCT (blockSL coe_blockSL)
open scoped commutatorElement MatrixGroups

variable {p f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem toGL_blockSL_mem_gramSU (hn : 8 ≤ n) (i : Fin 4) {g : SL(2, K)}
    (hg : ((g : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * (g : Matrix (Fin 2) (Fin 2) K) = 1) :
    Matrix.SpecialLinearGroup.toGL (blockSL K n 2 (2 * i) (two_mul_add_two_le hn i) g) ∈
      gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  refine mem_gramSU.2 ⟨?_, (blockSL K n 2 (2 * i) (two_mul_add_two_le hn i) g).2⟩
  rw [Units.val_one, Matrix.mul_one]
  exact blockSL_unitary (two_mul_add_two_le hn i) h.bar g hg

@[expose] def suBlock (hn : 8 ≤ n) (i : Fin 4) (g : SL(2, K))
    (hg : ((g : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * (g : Matrix (Fin 2) (Fin 2) K) = 1) :
    gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  ⟨Matrix.SpecialLinearGroup.toGL (blockSL K n 2 (2 * i) (two_mul_add_two_le hn i) g),
    toGL_blockSL_mem_gramSU h hn i hg⟩

theorem coe_suBlock (hn : 8 ≤ n) (i : Fin 4) (g : SL(2, K))
    (hg : ((g : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * (g : Matrix (Fin 2) (Fin 2) K) = 1) :
    ((suBlock h hn i g hg : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
      GL (Fin n) K) =
        Matrix.SpecialLinearGroup.toGL (blockSL K n 2 (2 * i) (two_mul_add_two_le hn i) g) :=
  rfl

theorem suBlock_commute (hn : 8 ≤ n) {i j : Fin 4} (hij : i ≠ j) {g g' : SL(2, K)}
    (hg : ((g : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * (g : Matrix (Fin 2) (Fin 2) K) = 1)
    (hg' : ((g' : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * (g' : Matrix (Fin 2) (Fin 2) K) = 1) :
    Commute (suBlock h hn i g hg) (suBlock h hn j g' hg') :=
  Subtype.ext ((blockSL_two_mul_commute hn hij g g').map Matrix.SpecialLinearGroup.toGL).eq

theorem primeFormFieldHom_mk_suBlock (hn : 8 ≤ n) (hC : IsPrimeFormGram (1 : GL (Fin n) K))
    (σ : K ≃+* K) (i : Fin 4) {g : SL(2, K)}
    (hg : ((g : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * (g : Matrix (Fin 2) (Fin 2) K) = 1)
    (hσ : Matrix.SpecialLinearGroup.map (σ : K →+* K) g = g) :
    primeFormFieldHom h hC σ (QuotientGroup.mk' _ (suBlock h hn i g hg)) =
      QuotientGroup.mk' (normOneScalars h (gramSU h ((1 : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)) n) (suBlock h hn i g hg) := by
  change primeFormFieldAut h hC σ (suBlock h hn i g hg :
      primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
    (suBlock h hn i g hg : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
  rw [primeFormFieldAut_mk]
  congr 1
  apply Subtype.ext
  apply Units.ext
  have hmap := congrArg Subtype.val (map_blockSL (two_mul_add_two_le hn i) (σ : K →+* K) g)
  rw [hσ] at hmap
  exact hmap

theorem fixedBlocks_primeFormFieldHom (hn : 8 ≤ n) (hC : IsPrimeFormGram (1 : GL (Fin n) K))
    {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hbar : h.bar ω * ω = 1) (σ : K ≃+* K)
    (hσω : σ ω = ω) : FixedBlocks 3 (primeFormFieldHom h hC σ) 4 := by
  have hcU : ((omegaSL ω hω : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ *
      (omegaSL ω hω : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [coe_omegaSL]
    ext k l
    fin_cases k <;> fin_cases l <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination hbar | linear_combination (h.bar ω * ω + 1) * hbar
  have hwU : (((WSL : SL2 K) : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ *
      ((WSL : SL2 K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [coe_WSL]
    ext k l
    fin_cases k <;> fin_cases l <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hW : Matrix.SpecialLinearGroup.map (σ : K →+* K) (WSL : SL2 K) = WSL := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, coe_WSL]
    ext k l
    fin_cases k <;> fin_cases l <;> simp
  have hcoe : ∀ x y : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      ((⁅x, y⁆ : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) : GL (Fin n) K) =
        ⁅(x : GL (Fin n) K), (y : GL (Fin n) K)⁆ := fun x y =>
    map_commutatorElement (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).subtype x y
  refine fixedBlocks_of_hom (QuotientGroup.mk' (normOneScalars h
    (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n))
    (fun i => suBlock h hn i (omegaSL ω hω) hcU) (fun i => suBlock h hn i WSL hwU) ?_
    (fun i => primeFormFieldHom_mk_suBlock h hn hC σ i hcU (map_omegaSL hω hσω))
    (fun i => primeFormFieldHom_mk_suBlock h hn hC σ i hwU hW) (fun i => ?_)
    (fun i => ?_)
  · rintro i j hij _ (rfl | rfl) _ (rfl | rfl) <;> exact suBlock_commute h hn hij _ _
  · apply Subtype.ext
    rw [Subgroup.coe_pow, hcoe, coe_suBlock, coe_suBlock, Subgroup.coe_one,
      ← map_commutatorElement, ← map_commutatorElement, ← map_pow, ← map_pow,
      comm_omegaSL_WSL_pow_three, map_one, map_one]
  · rw [QuotientGroup.ker_mk']
    rintro ⟨u, -, -, hu⟩
    have h1 : ((⁅⁅suBlock h hn i (omegaSL ω hω) hcU, suBlock h hn i WSL hwU⁆,
        suBlock h hn i WSL hwU⁆ : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
          GL (Fin n) K) =
        Matrix.SpecialLinearGroup.toGL (blockSL K n 2 (2 * i) (two_mul_add_two_le hn i)
          ⁅(⁅omegaSL ω hω, WSL⁆ : SL2 K), WSL⁆) := by
      rw [hcoe, hcoe, coe_suBlock, coe_suBlock, ← map_commutatorElement, ← map_commutatorElement,
        ← map_commutatorElement, ← map_commutatorElement]
    have h2 := congrArg Units.val (h1.symm.trans hu)
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.GeneralLinearGroup.coe_scalar] at h2
    exact not_commute_comm_omegaSL_WSL ω hω hω1
      (commutatorElement_eq_one_iff_commute.1 (eq_one_of_blockSL_eq_scalar _ (by omega) h2))

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35
