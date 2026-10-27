module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.FixDim
public import CFSG.RankThree.PartOne.S11d.OrthRankBase
public import CFSG.HardMathSupport.GuralnickMalle.BasicGeneral

public section

namespace CFSG.LieType.SpecialLinear.SLModel

open Matrix Module CFSG.HardMathSupport.GuralnickMalle
  CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc

variable {F k : Type*} [Field F] [Field k] [Algebra F k] {G V I : Type*} [Group G]
  [AddCommGroup V] [Module k V] [Fintype I] [DecidableEq I]

theorem finrank_fixSubGen_eq_finrank_fixF (σ : Representation k G V)
    (β : V ≃ₗ[k] (I → k)) (M : G → Matrix I I F)
    (hβ : ∀ g v, β (σ g v) = (M g).map (algebraMap F k) *ᵥ β v)
    (A : Subgroup G) [Finite A] :
    finrank k (fixSubGen σ A) = finrank F (fixF (fun a : A => M a)) := by
  have hmap : Submodule.map (β : V →ₗ[k] (I → k)) (fixSubGen σ A) =
      fixK (fun a : A => M a) := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [mem_fixK]
      intro a
      change (M (a : G)).map (algebraMap F k) *ᵥ β w = β w
      rw [← hβ]
      exact congrArg β ((mem_fixSubGen.mp hw) a.1 a.2)
    · intro hv
      refine ⟨β.symm v, ?_, β.apply_symm_apply v⟩
      change β.symm v ∈ fixSubGen σ A
      rw [mem_fixSubGen]
      intro a ha
      apply β.injective
      rw [hβ, β.apply_symm_apply]
      simpa using (mem_fixK.mp hv) ⟨a, ha⟩
  rw [← LinearEquiv.finrank_map_eq β (fixSubGen σ A), hmap, finrank_fixK]

theorem finrank_range_sub_one_eq_rank (σ : Representation k G V)
    (β : V ≃ₗ[k] (I → k)) (M : G → Matrix I I F)
    (hβ : ∀ g v, β (σ g v) = (M g).map (algebraMap F k) *ᵥ β v)
    (g : G) :
    finrank k (LinearMap.range (σ g - 1)) = Matrix.rank (M g - 1) := by
  let A : Matrix I I k := (M g).map (algebraMap F k)
  have hA : A - 1 = ((M g - 1).map (algebraMap F k)) := by
    dsimp only [A]
    rw [Matrix.map_sub (algebraMap F k) (map_sub (algebraMap F k)),
      Matrix.map_one (algebraMap F k) (map_zero _) (map_one _)]
  have hconj : (A - 1).mulVecLin =
      (β : V →ₗ[k] (I → k)).comp ((σ g - 1).comp (β.symm : (I → k) →ₗ[k] V)) := by
    apply LinearMap.ext
    intro v
    funext i
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply,
      Matrix.mulVecLin_apply, Matrix.one_mulVec, map_sub]
    change (A *ᵥ v - v) i = (β ((σ g) (β.symm v)) - β (β.symm v)) i
    rw [hβ g (β.symm v), β.apply_symm_apply]
  have hrange : LinearMap.range ((A - 1).mulVecLin) =
      (LinearMap.range (σ g - 1)).map (β : V →ₗ[k] (I → k)) := by
    rw [hconj, LinearMap.range_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr β.symm.surjective, Submodule.map_top]
  have h1 : finrank k (LinearMap.range ((A - 1).mulVecLin)) =
      finrank k (LinearMap.range (σ g - 1)) := by
    rw [hrange, LinearEquiv.finrank_map_eq]
  have h2 : Matrix.rank (A - 1) =
      finrank k (LinearMap.range ((A - 1).mulVecLin)) := by
    rw [Matrix.rank_eq_finrank_range_toLin (A - 1) (Pi.basisFun k I) (Pi.basisFun k I),
      Matrix.toLin_eq_toLin', Matrix.toLin'_apply']
  calc finrank k (LinearMap.range (σ g - 1))
      = finrank k (LinearMap.range ((A - 1).mulVecLin)) := h1.symm
    _ = Matrix.rank (A - 1) := h2.symm
    _ = Matrix.rank (M g - 1) := by
        rw [hA, CFSG.RankThree.PartOne.FieldFix.rank_map_eq]

theorem sub_one_mul_sub_one_eq_zero_of_model (σ : Representation k G V)
    (β : V ≃ₗ[k] (I → k)) (M : G → Matrix I I F)
    (hβ : ∀ g v, β (σ g v) = (M g).map (algebraMap F k) *ᵥ β v)
    {a b : G} (h : (σ a - 1) * (σ b - 1) = 0) : (M a - 1) * (M b - 1) = 0 := by
  let A : G → Matrix I I k := fun g => (M g).map (algebraMap F k)
  have hA : ∀ g, A g - 1 = ((M g - 1).map (algebraMap F k)) := by
    intro g
    dsimp only [A]
    rw [Matrix.map_sub (algebraMap F k) (map_sub (algebraMap F k)),
      Matrix.map_one (algebraMap F k) (map_zero _) (map_one _)]
  have hconj : ∀ g, (A g - 1).mulVecLin =
      (β : V →ₗ[k] (I → k)).comp ((σ g - 1).comp (β.symm : (I → k) →ₗ[k] V)) := by
    intro g
    apply LinearMap.ext
    intro v
    funext i
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply,
      Matrix.mulVecLin_apply, Matrix.one_mulVec, map_sub]
    change (A g *ᵥ v - v) i = (β ((σ g) (β.symm v)) - β (β.symm v)) i
    rw [hβ g (β.symm v), β.apply_symm_apply]
  have hlin : ((A a - 1) * (A b - 1)).mulVecLin = 0 := by
    rw [Matrix.mulVecLin_mul, hconj a, hconj b]
    ext v
    simp only [LinearMap.comp_apply, LinearMap.zero_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [← Module.End.mul_apply, h, LinearMap.zero_apply, map_zero]
  have hzero : (A a - 1) * (A b - 1) = 0 := by
    apply Matrix.toLin'.injective
    simpa [Matrix.toLin'_apply', Matrix.mulVecLin_zero] using hlin
  have hmap : ((M a - 1) * (M b - 1)).map (algebraMap F k) = 0 := by
    rw [Matrix.map_mul, ← hA a, ← hA b, hzero]
  have hinj : Function.Injective (fun Z : Matrix I I F => Z.map (algebraMap F k)) :=
    Matrix.map_injective (f := algebraMap F k) (RingHom.injective (algebraMap F k))
  exact hinj (by simpa [Matrix.map_zero] using hmap)

end CFSG.LieType.SpecialLinear.SLModel
