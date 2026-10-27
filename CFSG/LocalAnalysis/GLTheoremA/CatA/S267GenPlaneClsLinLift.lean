module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsLinBlock
import CFSG.GroupTheory.Fitting.LayerProjection
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearBlocks

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.CALinearPrimary CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement Matrix

theorem map_eq_self_of_perfect {G H : Type*} [Group G] [Group H] (π : G →* H)
    (hker : π.ker ≤ Subgroup.center G) {F : Subgroup G} (hF : ⁅F, F⁆ = F) (ψ : G →* G)
    (hψ : ∀ g ∈ F, π (ψ g) = π g) {g : G} (hg : g ∈ F) : ψ g = g := by
  have hz : ∀ a ∈ F, a⁻¹ * ψ a ∈ Subgroup.center G := fun a ha =>
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hψ a ha, inv_mul_cancel])
  rw [← hF, Subgroup.commutator_def] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have e1 : ψ a = a * (a⁻¹ * ψ a) := by group
    have e2 : ψ b = b * (b⁻¹ * ψ b) := by group
    have za := Subgroup.mem_center_iff.mp (hz a ha)
    have zb := Subgroup.mem_center_iff.mp (hz b hb)
    rw [map_commutatorElement, e1, e2]
    exact CFSG.HardMathSupport.Solomon.Coordinator.commutatorElement_mul_mul' (za b).symm
      (za _).symm (zb a).symm
  | one => exact map_one ψ
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  | inv x _ hx => rw [map_inv, hx]

variable {n : ℕ} {K : Type*} [Field K]

theorem slConjugation_map_eq_of_fix {F : Subgroup (Matrix.SpecialLinearGroup (Fin n) K)}
    (hF : ⁅F, F⁆ = F) (B : GL (Fin n) K) (σ : K ≃+* K)
    (hfix : ∀ g ∈ F, (LinearFlag.conjAut n K B * LinearFlag.fieldAut n K σ)
      (LinearFlag.proj n K g) = LinearFlag.proj n K g)
    {g : Matrix.SpecialLinearGroup (Fin n) K} (hg : g ∈ F) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K B
      (Matrix.SpecialLinearGroup.map σ.toRingHom g) = g := by
  have hker : (LinearFlag.proj n K).ker ≤ Subgroup.center _ := by
    rw [LinearFlag.ker_proj]
    exact LinearFlag.scalars_le_center n K
  refine map_eq_self_of_perfect (LinearFlag.proj n K) hker hF
    ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K
      B).toMonoidHom.comp (Matrix.SpecialLinearGroup.map σ.toRingHom)) (fun g' hg' => ?_) hg
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← LinearFlag.conjAut_proj,
    ← LinearFlag.fieldAut_proj, ← MulAut.mul_apply]
  exact hfix g' hg'

@[expose] def plSemiVec (B : GL (Fin n) K) (σ : K ≃+* K) : (Fin n → K) →+ (Fin n → K) where
  toFun v := (B : Matrix (Fin n) (Fin n) K) *ᵥ fun i => σ (v i)
  map_zero' := by
    have : (fun i => σ ((0 : Fin n → K) i)) = 0 := by
      ext i
      simp
    simp only [this, Matrix.mulVec_zero]
  map_add' v w := by
    have : (fun i => σ ((v + w) i)) = (fun i => σ (v i)) + fun i => σ (w i) := by
      ext i
      simp
    rw [this, Matrix.mulVec_add]

theorem plSemiVec_apply (B : GL (Fin n) K) (σ : K ≃+* K) (v : Fin n → K) :
    plSemiVec B σ v = (B : Matrix (Fin n) (Fin n) K) *ᵥ fun i => σ (v i) := rfl

theorem plSemiVec_smul (B : GL (Fin n) K) (σ : K ≃+* K) (c : K) (v : Fin n → K) :
    plSemiVec B σ (c • v) = σ c • plSemiVec B σ v := by
  rw [plSemiVec_apply, plSemiVec_apply, ← Matrix.mulVec_smul]
  congr 1
  ext i
  simp

theorem plSemiVec_injective (B : GL (Fin n) K) (σ : K ≃+* K) :
    Function.Injective (plSemiVec B σ) := by
  intro v w hvw
  rw [plSemiVec_apply, plSemiVec_apply] at hvw
  have h1 := congrArg (fun u => ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u) hvw
  simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec] at h1
  ext i
  exact σ.injective (congrFun h1 i)

theorem plSemiVec_mulVec (B : GL (Fin n) K) (σ : K ≃+* K)
    {g : Matrix.SpecialLinearGroup (Fin n) K}
    (hg : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K B
      (Matrix.SpecialLinearGroup.map σ.toRingHom g) = g) (v : Fin n → K) :
    plSemiVec B σ ((g : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      (g : Matrix (Fin n) (Fin n) K) *ᵥ plSemiVec B σ v := by
  have hm := congrArg (fun u : Matrix.SpecialLinearGroup (Fin n) K =>
    (u : Matrix (Fin n) (Fin n) K)) hg
  simp only [LinearFlag.coe_slConjugation] at hm
  have hBg : (B : Matrix (Fin n) (Fin n) K) *
      ((Matrix.SpecialLinearGroup.map σ.toRingHom g : Matrix.SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) := by
    rw [← hm, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.mul_one]
  have hσ : (fun i => σ (((g : Matrix (Fin n) (Fin n) K) *ᵥ v) i)) =
      ((Matrix.SpecialLinearGroup.map σ.toRingHom g : Matrix.SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ fun i => σ (v i) := by
    ext i
    exact RingHom.map_mulVec σ.toRingHom _ v i
  rw [plSemiVec_apply, plSemiVec_apply, hσ, Matrix.mulVec_mulVec, hBg, ← Matrix.mulVec_mulVec]

variable [Finite K]

theorem exists_smul_of_fix_specialFactor {p : ℕ} (hpk : (p : K) ≠ 0) {A : GL (Fin n) K} {c : Kˣ}
    (hA : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c) {h : K[X]}
    (hh : h ∈ primaryFactors (glA A : Module.End K (Fin n → K))) (hgood : IsGoodFactor A h)
    (B : GL (Fin n) K) (σ : K ≃+* K)
    (hfix : ∀ g ∈ specialFactor A h, (LinearFlag.conjAut n K B * LinearFlag.fieldAut n K σ)
      (LinearFlag.proj n K g) = LinearFlag.proj n K g) :
    ∃ e : AdjoinRoot h, ∀ w : primaryComponent (glA A : Module.End K (Fin n → K)) h,
      plSemiVec B σ (w : Fin n → K) =
        ((e • w : primaryComponent (glA A : Module.End K (Fin n → K)) h) : Fin n → K) := by
  have hsq := squarefree_minpoly_glA hpk hA
  have hperf : ⁅specialFactor A h, specialFactor A h⁆ = specialFactor A h := by
    haveI := (isQuasisimple_specialFactor hsq hh hgood).1
    exact CFSG.GroupTheory.commutator_eq_self_of_isPerfect_subgroup
  have hm : 2 ≤ finrank (AdjoinRoot h) (primaryComponent (glA A : Module.End K (Fin n → K)) h) := by
    rcases hgood with h3 | ⟨h2, -⟩
    · exact le_trans (by norm_num) h3
    · exact h2
  refine exists_smul_of_commute_linearSpecialBlock hsq hh hm (plSemiVec B σ) fun g' hg' v => ?_
  have hle : linearSpecialBlock (glA A) h ≤ (slGL n K).range := fun _ hg =>
    mem_range_slGL (det_eq_one_of_mem_linearSpecialBlock hsq hh hg)
  obtain ⟨g, rfl⟩ := hle hg'
  have hgF : g ∈ specialFactor A h := hg'
  rw [coe_slGL]
  exact plSemiVec_mulVec B σ (slConjugation_map_eq_of_fix hperf B σ hfix hgF) v

theorem eq_one_of_fix_specialFactor {p : ℕ} (hpk : (p : K) ≠ 0) {A : GL (Fin n) K} {c : Kˣ}
    (hA : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c) {h : K[X]}
    (hh : h ∈ primaryFactors (glA A : Module.End K (Fin n → K))) (hgood : IsGoodFactor A h)
    (B : GL (Fin n) K) (σ : K ≃+* K)
    (hfix : ∀ g ∈ specialFactor A h, (LinearFlag.conjAut n K B * LinearFlag.fieldAut n K σ)
      (LinearFlag.proj n K g) = LinearFlag.proj n K g) : σ = 1 := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  obtain ⟨e, he⟩ := exists_smul_of_fix_specialFactor hpk hA hh hgood B σ hfix
  have hm : 2 ≤ finrank (AdjoinRoot h) (primaryComponent (glA A : Module.End K (Fin n → K)) h) := by
    rcases hgood with h3 | ⟨h2, -⟩
    · exact le_trans (by norm_num) h3
    · exact h2
  obtain ⟨w, hw⟩ : ∃ w : primaryComponent (glA A : Module.End K (Fin n → K)) h, w ≠ 0 := by
    have : Nontrivial (primaryComponent (glA A : Module.End K (Fin n → K)) h) :=
      Module.nontrivial_of_finrank_pos (R := AdjoinRoot h) (by omega)
    exact exists_ne 0
  have he0 : e ≠ 0 := by
    rintro rfl
    have h1 := he w
    rw [zero_smul, Submodule.coe_zero] at h1
    exact hw (Subtype.ext (plSemiVec_injective B σ (by rw [h1, Submodule.coe_zero, map_zero])))
  ext a
  have h1 := he (a • w)
  rw [Submodule.coe_smul, plSemiVec_smul, he w] at h1
  have h2 : ((e • (a • w) : primaryComponent (glA A : Module.End K (Fin n → K)) h) :
      Fin n → K) = (((algebraMap K (AdjoinRoot h) a * e) • w :
        primaryComponent (glA A : Module.End K (Fin n → K)) h) : Fin n → K) := by
    rw [mul_smul, algebraMap_smul, smul_comm]
  have h3 : σ a • ((e • w : primaryComponent (glA A : Module.End K (Fin n → K)) h) :
      Fin n → K) = (((algebraMap K (AdjoinRoot h) (σ a) * e) • w :
        primaryComponent (glA A : Module.End K (Fin n → K)) h) : Fin n → K) := by
    rw [mul_smul, algebraMap_smul]
    rfl
  rw [h3, h2] at h1
  have h4 : (algebraMap K (AdjoinRoot h) (σ a) * e) • w =
      (algebraMap K (AdjoinRoot h) a * e) • w := Subtype.ext h1
  have h5 := smul_left_injective (AdjoinRoot h) hw h4
  have h6 : algebraMap K (AdjoinRoot h) (σ a) = algebraMap K (AdjoinRoot h) a :=
    mul_right_cancel₀ he0 h5
  exact (algebraMap K (AdjoinRoot h)).injective h6

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
