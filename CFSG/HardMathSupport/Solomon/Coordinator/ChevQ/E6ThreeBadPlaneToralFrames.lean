module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadSingerFrame
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCompInner

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Conj

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]

theorem finrank_ker_inf_conj_sub_one (y t h : LinearMap.GeneralLinearGroup F V)
    (hyh : y * h = h * y) :
    Module.finrank F ↥(LinearMap.ker (((y * t * y⁻¹ : LinearMap.GeneralLinearGroup F V) :
        Module.End F V) - 1) ⊓ LinearMap.ker ((h : Module.End F V) - 1)) =
      Module.finrank F ↥(LinearMap.ker ((t : Module.End F V) - 1) ⊓
        LinearMap.ker ((h : Module.End F V) - 1)) := by
  let e : V ≃ₗ[F] V := LinearMap.GeneralLinearGroup.toLinearEquiv y
  have hker : LinearMap.ker (((y * t * y⁻¹ : LinearMap.GeneralLinearGroup F V) :
      Module.End F V) - 1) ⊓ LinearMap.ker ((h : Module.End F V) - 1) =
      (LinearMap.ker ((t : Module.End F V) - 1) ⊓
        LinearMap.ker ((h : Module.End F V) - 1)).map e.toLinearMap := by
    have hcomm : ∀ v, (h : Module.End F V) (e.symm v) = e.symm ((h : Module.End F V) v) := by
      intro v
      apply e.injective
      rw [e.apply_symm_apply]
      change (y : Module.End F V) ((h : Module.End F V) (e.symm v)) = _
      rw [← Module.End.mul_apply, ← Units.val_mul, hyh, Units.val_mul, Module.End.mul_apply]
      change (h : Module.End F V) (e (e.symm v)) = _
      rw [e.apply_symm_apply]
    ext v
    rw [Submodule.mem_map_equiv, Submodule.mem_inf, Submodule.mem_inf, LinearMap.mem_ker,
      LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.mem_ker]
    change (e ((t : Module.End F V) (e.symm v)) - v = 0 ∧ (h : Module.End F V) v - v = 0) ↔
      ((t : Module.End F V) (e.symm v) - e.symm v = 0 ∧
        (h : Module.End F V) (e.symm v) - e.symm v = 0)
    rw [sub_eq_zero, sub_eq_zero, sub_eq_zero, sub_eq_zero, hcomm]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · apply e.injective
        rw [h1, e.apply_symm_apply]
      · rw [h2]
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rw [h1, e.apply_symm_apply]
      · apply e.symm.injective
        rw [h2]
  rw [hker, LinearEquiv.finrank_map_eq]

end Conj

section Struct


structure ToralFrames (K : Type) [Field K] (ω : Kˣ) where
  ρ : Fin 3 → SpecialLinearGroup (Fin 3) K →* ModGL Tag.E6 K
  σ : Fin 3 → Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ
  π : (Fin 3 → SpecialLinearGroup (Fin 3) K) →* ModGL Tag.E6 K
  frame : ∀ i, IsA2Frame (ρ i) (σ i)
  range : ∀ i, (ρ i).range = e6LineFactor K i
  h01 : ∀ i, σ i 0 1 = (e6LinePair i).1
  h12 : ∀ i, σ i 1 2 = (e6LinePair i).2
  mono : ∀ i, ρ i signedCycSL ∈ monomialSubgroup Tag.E6 K
  π_apply : ∀ x, π x = ρ 0 (x 0) * ρ 1 (x 1) * ρ 2 (x 2)
  π_mem : ∀ x, π x ∈ toralRootGroup Tag.E6 K (e6LineChar ω)
  conj_ρ : ∀ b i s, rootDiagUnit Tag.E6 b * ρ i s * (rootDiagUnit Tag.E6 b)⁻¹ =
    ρ i (conjSL (diagGL3 fun j => rootChar b (σ i j 0)) s)
  conj_π : ∀ x i w, π x * ρ i w * (π x)⁻¹ = ρ i (x i * w * (x i)⁻¹)
  conj_π_d : ∀ b x, (rootDiagUnit Tag.E6 b)⁻¹ * π x * rootDiagUnit Tag.E6 b =
    π (fun i => conjSL (diagGL3 fun j => rootChar b (σ i j 0))⁻¹ (x i))
  dec : ∀ m ∈ toralRootGroup Tag.E6 K (e6LineChar ω), ∃ (c : Fin Tag.E6.rank → Kˣ)
    (x : Fin 3 → SpecialLinearGroup (Fin 3) K),
    rootDiagUnit Tag.E6 c ∈ torusGroup Tag.E6 K ∧ m = rootDiagUnit Tag.E6 c * π x

end Struct

section Frames

variable
  {K : Type} [Field K]

theorem exists_toralFrames {ω : Kˣ} (hw3 : ω ^ 3 = 1) (hw1 : ω ≠ 1) :
    Nonempty (ToralFrames K ω) := by
  choose ρ σ hfr hrange h01 h12 hmono using exists_frame_e6Line_mono K
  have htor : ∀ i b s, rootDiagUnit Tag.E6 b * ρ i s * (rootDiagUnit Tag.E6 b)⁻¹ =
      ρ i (conjSL (diagGL3 fun j => rootChar b (σ i j 0)) s) := fun i b s => by
    rw [conjSL_diagGL3]
    exact (hfr i).torus b s
  obtain ⟨π, hπ, hπL, -, hconjd, -, hπconj, hMdec⟩ := exists_commProd_of_frames
    (D := fun i b => diagGL3 fun j => rootChar b (σ i j 0)) hw3 hw1 hrange htor
  have hπM : ∀ x, π x ∈ toralRootGroup Tag.E6 K (e6LineChar ω) := fun x => by
    have hle : rootSpan Tag.E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) ≤
        toralRootGroup Tag.E6 K (e6LineChar ω) := by
      show _ ≤ torusGroup Tag.E6 K ⊔ rootSpan Tag.E6 K (rootCharKernel (e6LineChar ω))
      rw [e6Line_kernel hw3 hw1]
      exact le_sup_right
    exact hle (hπL x)
  exact ⟨⟨ρ, σ, π, hfr, hrange, h01, h12, hmono, hπ, hπM, fun b i s => htor i b s, hπconj, hconjd,
    hMdec⟩⟩

namespace ToralFrames

variable {ω : Kˣ} (T : ToralFrames K ω)

@[expose] def D (i : Fin 3) (b : Fin Tag.E6.rank → Kˣ) : GL (Fin 3) K :=
  diagGL3 fun j => rootChar b (T.σ i j 0)

theorem act (c : Fin Tag.E6.rank → Kˣ) (x : Fin 3 → SpecialLinearGroup (Fin 3) K) (i : Fin 3)
    (s : SpecialLinearGroup (Fin 3) K) :
    (rootDiagUnit Tag.E6 c * T.π x) * T.ρ i s * (rootDiagUnit Tag.E6 c * T.π x)⁻¹ =
      T.ρ i (conjSL (T.D i c * SpecialLinearGroup.toGL (x i)) s) := by
  rw [map_mul, MulAut.mul_apply, conjSL_toGL, MulAut.conj_apply]
  rw [show conjSL (T.D i c) (x i * s * (x i)⁻¹) = conjSL (diagGL3 fun j => rootChar c (T.σ i j 0))
    (x i * s * (x i)⁻¹) from rfl, ← T.conj_ρ c i (x i * s * (x i)⁻¹), ← T.conj_π x i s]
  group

theorem exists_cube_scalar {c : Fin Tag.E6.rank → Kˣ}
    {x : Fin 3 → SpecialLinearGroup (Fin 3) K}
    (h3 : (rootDiagUnit Tag.E6 c * T.π x) ^ 3 = 1) (i : Fin 3) :
    ∃ α : K, ((T.D i c * SpecialLinearGroup.toGL (x i) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1 := by
  refine exists_pow_three_smul_one (ρ := T.ρ i) (T.frame i).injective
    (ε := MulAut.conj (rootDiagUnit Tag.E6 c * T.π x)) ?_ (fun s => ?_)
  · rw [← map_pow, h3, map_one]
  · rw [MulAut.conj_apply]
    exact T.act c x i s

theorem conj_eq (c : Fin Tag.E6.rank → Kˣ) (x z : Fin 3 → SpecialLinearGroup (Fin 3) K) :
    T.π z * (rootDiagUnit Tag.E6 c * T.π x) * (T.π z)⁻¹ =
      rootDiagUnit Tag.E6 c *
        T.π (fun i => conjSL (T.D i c)⁻¹ (z i) * x i * (z i)⁻¹) := by
  have h := T.conj_π_d c z
  have e : T.π (fun i => conjSL (T.D i c)⁻¹ (z i) * x i * (z i)⁻¹) =
      T.π (fun i => conjSL (T.D i c)⁻¹ (z i)) * T.π x * (T.π z)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e]
  change _ = rootDiagUnit Tag.E6 c * (T.π (fun i => conjSL (diagGL3 fun j =>
    rootChar c (T.σ i j 0))⁻¹ (z i)) * T.π x * (T.π z)⁻¹)
  rw [← h]
  group

theorem D_mul_toGL_w (c : Fin Tag.E6.rank → Kˣ) (x z : Fin 3 → SpecialLinearGroup (Fin 3) K)
    (i : Fin 3) :
    T.D i c * SpecialLinearGroup.toGL (conjSL (T.D i c)⁻¹ (z i) * x i * (z i)⁻¹) =
      SpecialLinearGroup.toGL (z i) * (T.D i c * SpecialLinearGroup.toGL (x i)) *
        (SpecialLinearGroup.toGL (z i))⁻¹ := by
  rw [map_mul, map_mul, map_inv SpecialLinearGroup.toGL (z i), toGL_conjSL_eq_mul]
  group

end ToralFrames

end Frames

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
