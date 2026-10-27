module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneUnitaryData

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix CFSG.ClassicalGroups.UnitaryFlag UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {r ε : ℕ}

theorem hypUnitary_le_linearSimilitudes : hypUnitary h r ε ≤ linearSimilitudes h r ε :=
  fun _ hA => mem_linearSimilitudes.2 ⟨1, one_ne_zero, map_one _, by rw [one_smul]; exact hA⟩

theorem hypSU_le_hypUnitary : hypSU h r ε ≤ hypUnitary h r ε :=
  fun _ hg => hg.1

variable (hr : 1 ≤ r) (hε : ε ≤ 1)

theorem linearSimAut_hypSU (g : hypSU h r ε) :
    linearSimAut h hr hε ⟨g, hypUnitary_le_linearSimilitudes h (hypSU_le_hypUnitary h g.2)⟩ =
      MulAut.conj (hypProj h r ε g) := by
  apply MulEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := hypProj_surjective h r ε y
  rw [linearSimAut_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

variable (hn : 3 ≤ 2 * r + ε)

include hn in
theorem exists_isometry_linearSimAut (A : linearSimilitudes h r ε) :
    ∃ A' : hypUnitary h r ε,
      linearSimAut h hr hε ⟨A', hypUnitary_le_linearSimilitudes h A'.2⟩ =
        linearSimAut h hr hε A := by
  obtain ⟨x, hxΦ, hxr, hxU⟩ := exists_unitary_rep h hr hε hn (linearToSemilinear h A)
  rw [linearToSemilinear_right] at hxr
  have hx : SemidirectProduct.inl (x : SemiGL (HypIndex r ε) K).left =
      (x : SemiGL (HypIndex r ε) K) := SemidirectProduct.ext rfl hxr.symm
  refine ⟨⟨_, hxU⟩, ?_⟩
  simp only [linearSimAut, MonoidHom.comp_apply]
  rw [← hxΦ]
  exact congrArg (semilinearAutHom h hr hε) (Subtype.ext hx)

include hn in
theorem isCyclic_map_linearSimAutGroup [Finite K] :
    IsCyclic ((linearSimAutGroup h hr hε).map (QuotientGroup.mk' (inner (hypPSU h r ε)))) := by
  classical
  set φ := (QuotientGroup.mk' (inner (hypPSU h r ε))).comp ((linearSimAut h hr hε).comp
    (Subgroup.inclusion (hypUnitary_le_linearSimilitudes h (r := r) (ε := ε)))) with hφ
  set δ : hypUnitary h r ε →* Kˣ :=
    Matrix.GeneralLinearGroup.det.comp (hypUnitary h r ε).subtype with hδ
  have hker : δ.rangeRestrict.ker ≤ φ.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.ker_rangeRestrict]
    intro A hA
    rw [MonoidHom.mem_ker] at hA ⊢
    have hdet : ((A : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).det = 1 :=
      congrArg Units.val hA
    have hSU : (A : GL (HypIndex r ε) K) ∈ hypSU h r ε := ⟨A.2, hdet⟩
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨hypProj h r ε ⟨_, hSU⟩, (linearSimAut_hypSU h hr hε ⟨_, hSU⟩).symm⟩
  have hψ : Function.Surjective (δ.rangeRestrict.liftOfSurjective δ.rangeRestrict_surjective
      ⟨φ.rangeRestrict, hker⟩) := by
    intro y
    obtain ⟨A, hA⟩ := φ.rangeRestrict_surjective y
    refine ⟨δ.rangeRestrict A, ?_⟩
    rw [← hA]
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ A
  have : IsCyclic φ.range := isCyclic_of_surjective _ hψ
  have hle : (linearSimAutGroup h hr hε).map (QuotientGroup.mk' (inner (hypPSU h r ε))) ≤
      φ.range := by
    rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    obtain ⟨A', hA'⟩ := exists_isometry_linearSimAut h hr hε hn A
    exact ⟨A', by rw [← hA']; rfl⟩
  exact Subgroup.isCyclic_of_le hle

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
