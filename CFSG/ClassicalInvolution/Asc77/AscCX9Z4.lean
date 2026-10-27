module

public import CFSG.ClassicalInvolution.Asc77.AscCX9Z3
public import CFSG.ClassicalInvolution.Asc77.AscCX9X2

public noncomputable section

namespace CFSG.ClassicalInvolution.Asc77.CX.MF2U

open Matrix CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Asc77.CX.MF2L (spForm spM mem_spM kappa kappa_range kappa_injective)
open scoped MatrixGroups

variable {K : Type} [Field K] {σ : K ≃+* K} {F : Type} [Field F]

structure DescData (σ : K ≃+* K) (F : Type) [Field F] where
  c : K
  t : K
  m : K
  n : K
  ι : F →+* K
  invol : ∀ a, σ (σ a) = a
  normc : σ c * c = -1
  normm : σ m * m = 1
  normn : σ n * n = 1
  ht : t - σ t ≠ 0
  fix : ∀ a, σ (ι a) = ι a
  onto : ∀ b, σ b = b → ∃ a, ι a = b

namespace DescData

variable (D : DescData σ F)

theorem hc : D.c ≠ 0 := fun h => by
  have h1 := D.normc
  rw [h, mul_zero] at h1
  exact one_ne_zero (neg_eq_zero.mp h1.symm)

theorem hm : D.m ≠ 0 := fun h => by
  have h1 := D.normm
  rw [h, mul_zero] at h1
  exact zero_ne_one h1

theorem hn : D.n ≠ 0 := fun h => by
  have h1 := D.normn
  rw [h, mul_zero] at h1
  exact zero_ne_one h1

@[expose] def hGL : GL (Fin 4) K :=
  ⟨descH σ D.c D.t D.m D.n, descHInv σ D.c D.t D.m D.n, descH_mul_inv D.hc D.ht D.hm D.hn,
    descHInv_mul D.hc D.ht D.hm D.hn⟩

theorem map_spForm_one : (spForm (1 : F) 1).map D.ι = spForm 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spForm]

theorem map_fix (Y : Matrix (Fin 4) (Fin 4) F) : (Y.map D.ι).map σ = Y.map D.ι := by
  rw [Matrix.map_map]
  congr 1
  funext a
  exact D.fix a

theorem map_form {y : SL(4, F)} (hy : y ∈ spM (spForm 1 1)) :
    (y : Matrix (Fin 4) (Fin 4) F).map D.ι * spForm 1 1 *
      ((y : Matrix (Fin 4) (Fin 4) F).map D.ι)ᵀ =
      spForm 1 1 := by
  have h := congrArg (fun M => M.map D.ι) (mem_spM.mp hy)
  simp only [Matrix.map_mul, Matrix.transpose_map, D.map_spForm_one] at h
  exact h

theorem det_conj (Y : Matrix (Fin 4) (Fin 4) K) :
    (descH σ D.c D.t D.m D.n * Y * descHInv σ D.c D.t D.m D.n).det = Y.det := by
  have h := congrArg Matrix.det (descH_mul_inv D.hc D.ht D.hm D.hn (σ := σ))
  rw [det_mul, det_one] at h
  rw [det_mul, det_mul]
  linear_combination Y.det * h

theorem det_conj' (Y : Matrix (Fin 4) (Fin 4) K) :
    (descHInv σ D.c D.t D.m D.n * Y * descH σ D.c D.t D.m D.n).det = Y.det := by
  have h := congrArg Matrix.det (descHInv_mul D.hc D.ht D.hm D.hn (σ := σ))
  rw [det_mul, det_one] at h
  rw [det_mul, det_mul]
  linear_combination Y.det * h

theorem coe_conj (y : SL(4, F)) :
    ((D.hGL * Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map D.ι y) * D.hGL⁻¹ :
      GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      descH σ D.c D.t D.m D.n * (y : Matrix (Fin 4) (Fin 4) F).map D.ι *
        descHInv σ D.c D.t D.m D.n := rfl

theorem conj_mem {y : SL(4, F)} (hy : y ∈ spM (spForm 1 1)) :
    D.hGL * Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map D.ι y) * D.hGL⁻¹ ∈
      SUid σ 4 := by
  refine ⟨?_, ?_⟩
  · rw [D.coe_conj, D.det_conj, ← RingHom.mapMatrix_apply, ← RingHom.map_det, y.2, map_one]
  · rw [D.coe_conj]
    refine unitary_conj D.hc D.ht D.hm D.hn D.invol D.normm D.normn D.normc (D.map_fix _)
      (D.map_form hy) (y' := ((y⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F).map D.ι) ?_
    rw [← Matrix.map_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.map_one _ (map_zero _) (map_one _)]

@[expose] def kap1 (F : Type) [Field F] : StatedSp 2 F →* SL(4, F) :=
  kappa (F := F) one_ne_zero one_ne_zero

theorem kap1_mem (x : StatedSp 2 F) : kap1 F x ∈ spM (spForm 1 1) := by
  rw [← kappa_range one_ne_zero one_ne_zero]
  exact ⟨x, rfl⟩

@[expose] def kU : StatedSp 2 F →* SUid σ 4 :=
  ((MulAut.conj D.hGL).toMonoidHom.comp (Matrix.SpecialLinearGroup.toGL.comp
    ((Matrix.SpecialLinearGroup.map D.ι).comp (kap1 F)))).codRestrict (SUid σ 4)
    fun x => D.conj_mem (kap1_mem x)

theorem suMat_kU (x : StatedSp 2 F) :
    suMat (D.kU x) = descH σ D.c D.t D.m D.n *
      ((kap1 F x : SL(4, F)) : Matrix (Fin 4) (Fin 4) F).map D.ι * descHInv σ D.c D.t D.m D.n :=
  rfl

theorem kU_mem_spU (x : StatedSp 2 F) : D.kU x ∈ spU (spForm D.m D.n) := by
  rw [mem_spU, suMat_kU]
  exact form_conj D.hc D.ht D.hm D.hn (D.map_form (kap1_mem x))

theorem conj_conj (X : Matrix (Fin 4) (Fin 4) K) :
    descH σ D.c D.t D.m D.n * (descHInv σ D.c D.t D.m D.n * X * descH σ D.c D.t D.m D.n) *
      descHInv σ D.c D.t D.m D.n = X := by
  simp only [← Matrix.mul_assoc]
  rw [descH_mul_inv D.hc D.ht D.hm D.hn, Matrix.one_mul, Matrix.mul_assoc,
    descH_mul_inv D.hc D.ht D.hm D.hn, Matrix.mul_one]

theorem kU_injective : Function.Injective D.kU := by
  intro x y h
  have h1 := congrArg (fun z : SUid σ 4 =>
    descHInv σ D.c D.t D.m D.n * suMat z * descH σ D.c D.t D.m D.n) h
  simp only [suMat_kU] at h1
  have e : ∀ Y : Matrix (Fin 4) (Fin 4) K,
      descHInv σ D.c D.t D.m D.n * (descH σ D.c D.t D.m D.n * Y * descHInv σ D.c D.t D.m D.n) *
        descH σ D.c D.t D.m D.n = Y := by
    intro Y
    simp only [← Matrix.mul_assoc]
    rw [descHInv_mul D.hc D.ht D.hm D.hn, Matrix.one_mul, Matrix.mul_assoc,
      descHInv_mul D.hc D.ht D.hm D.hn, Matrix.mul_one]
  rw [e, e] at h1
  exact kappa_injective one_ne_zero one_ne_zero
    (Subtype.ext (Matrix.map_injective D.ι.injective h1))

theorem range_kU : D.kU.range = spU (spForm D.m D.n) := by
  refine le_antisymm (by rintro _ ⟨x, rfl⟩; exact D.kU_mem_spU x) fun g hg => ?_
  have hg' := mem_spU.mp hg
  set Z := descHInv σ D.c D.t D.m D.n * suMat g * descH σ D.c D.t D.m D.n with hZ
  have hZσ : Z.map σ = Z := descend_fixed D.hc D.ht D.hm D.hn D.invol D.normm D.normn D.normc
    (map_suMat g) (suMat_inv_mul_suMat g) hg'
  have hZJ : Z * spForm 1 1 * Zᵀ = spForm 1 1 := descend_form D.hc D.ht D.hm D.hn hg'
  have hZdet : Z.det = 1 := by rw [hZ, D.det_conj', det_suMat]
  choose e he using fun i j => D.onto (Z i j) (congrFun (congrFun hZσ i) j)
  set Z₀ : Matrix (Fin 4) (Fin 4) F := Matrix.of e with hZ₀def
  have hZ₀ : Z₀.map D.ι = Z := by
    ext i j
    exact he i j
  have hdet₀ : Z₀.det = 1 := D.ι.injective (by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hZ₀, hZdet, map_one])
  set z₀ : SL(4, F) := ⟨Z₀, hdet₀⟩ with hz₀
  have hsp₀ : z₀ ∈ spM (spForm 1 1) := by
    refine mem_spM.mpr ?_
    show Z₀ * spForm 1 1 * Z₀ᵀ = spForm 1 1
    apply Matrix.map_injective D.ι.injective
    simp only [Matrix.map_mul, Matrix.transpose_map, D.map_spForm_one]
    rw [hZ₀, hZJ]
  rw [← kappa_range one_ne_zero one_ne_zero] at hsp₀
  obtain ⟨x, hx⟩ := hsp₀
  refine ⟨x, suMat_injective ?_⟩
  rw [suMat_kU]
  have hx' : ((kap1 F x : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = Z₀ := congrArg Subtype.val hx
  rw [hx', hZ₀, hZ, D.conj_conj]

end DescData

end CFSG.ClassicalInvolution.Asc77.CX.MF2U
