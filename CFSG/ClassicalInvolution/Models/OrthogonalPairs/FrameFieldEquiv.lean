module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame
public import CFSG.ClassicalGroups.Orthogonal.RingEquivDerived
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent

public noncomputable section

open QuadraticMap Matrix
open scoped MatrixGroups

namespace CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Transport

open CFSG.ClassicalGroups.Orthogonal

variable {K₀ K V : Type*} [Field K₀] [Field K] [AddCommGroup V]
  [Module K V] [Module K₀ V] {Q : QuadraticForm K V}
  (e : K₀ ≃+* K) (hsmul : ∀ (c : K₀) (v : V), c • v = e c • v)

@[expose] def fieldFrame (F : Frame Q) : Frame (formOfRingEquiv e hsmul Q) := by
  refine
    { P :=
        { e := F.P.e
          f := F.P.f
          Q_e := ?_
          Q_f := ?_
          polar_ef := ?_ }
      P' :=
        { e := F.P'.e
          f := F.P'.f
          Q_e := ?_
          Q_f := ?_
          polar_ef := ?_ }
      orth := { ee := ?_, ef := ?_, fe := ?_, ff := ?_ } }
  all_goals
    simp only [formOfRingEquiv_apply, polar_formOfRingEquiv, F.P.Q_e, F.P.Q_f,
      F.P'.Q_e, F.P'.Q_f, F.P.polar_ef, F.P'.polar_ef,
      F.orth.ee, F.orth.ef, F.orth.fe, F.orth.ff, map_zero, map_one]

theorem fieldFrame_incl (F : Frame Q) (X : Matrix (Fin 2) (Fin 2) K₀) :
    (fieldFrame e hsmul F).incl X = F.incl ((e : K₀ →+* K).mapMatrix X) := by
  simp [Frame.incl_apply, fieldFrame, Frame.e₁, Frame.f₁, Frame.e₂, Frame.f₂,
    hsmul, RingHom.mapMatrix_apply, Matrix.map_apply, map_neg]

theorem fieldFrame_coords (F : Frame Q) (v : V) :
    (fieldFrame e hsmul F).coords v = (e.symm : K →+* K₀).mapMatrix (F.coords v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Frame.coords_apply, fieldFrame, Frame.e₁, Frame.f₁, Frame.e₂, Frame.f₂,
      polar_formOfRingEquiv, RingHom.mapMatrix_apply, Matrix.map_apply, map_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]

theorem fieldFrame_La (F : Frame Q) (A : SL(2, K₀)) :
    restrictScalarsHom e hsmul ((fieldFrame e hsmul F).La A) =
      F.La (Matrix.SpecialLinearGroup.map (e : K₀ →+* K) A) := by
  apply LinearEquiv.ext
  intro v
  simp only [restrictScalarsHom_apply, Frame.La_apply, fieldFrame_incl, fieldFrame_coords]
  congr 1
  apply congrArg F.incl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, map_sub, map_mul,
      RingEquiv.apply_symm_apply]

private theorem sl2Map_surjective_of_ringEquiv :
    Function.Surjective (Matrix.SpecialLinearGroup.map (n := Fin 2) (e : K₀ →+* K)) := by
  intro A
  refine ⟨Matrix.SpecialLinearGroup.map (e.symm : K →+* K₀) A, ?_⟩
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem fieldFrame_La_range (F : Frame Q) :
    ((fieldFrame e hsmul F).La.range).map (restrictScalarsHom e hsmul) = F.La.range := by
  ext g
  constructor
  · rintro ⟨u, ⟨A, rfl⟩, rfl⟩
    rw [fieldFrame_La]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  · rintro ⟨B, rfl⟩
    obtain ⟨A, hA⟩ := sl2Map_surjective_of_ringEquiv e B
    refine ⟨(fieldFrame e hsmul F).La A, ⟨A, rfl⟩, ?_⟩
    rw [fieldFrame_La, hA]

end Transport

section Derived

open CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open QuadraticMap Subgroup

variable {K₀ K V : Type} [Field K₀] [Field K] [AddCommGroup V]
  [Module K V] [Module K₀ V] {Q : QuadraticForm K V}
  (e : K₀ ≃+* K) (hsmul : ∀ (c : K₀) (v : V), c • v = e c • v)

theorem fieldFrame_La_subgroupOf_map (F : Frame Q) :
    (((fieldFrame e hsmul F).La.range).subgroupOf
      (orthDerived (formOfRingEquiv e hsmul Q))).map
      (derivedFieldEquiv e hsmul Q).toMonoidHom =
    F.La.range.subgroupOf (orthDerived Q) := by
  let E := derivedFieldEquiv e hsmul Q
  have hmap := fieldFrame_La_range e hsmul F
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    change (E a : V ≃ₗ[K] V) ∈ F.La.range
    rw [derivedFieldEquiv_coe]
    exact hmap ▸ mem_map_of_mem (restrictScalarsHom e hsmul) ha
  · intro hz
    refine ⟨E.symm z, ?_, E.apply_symm_apply z⟩
    change (E.symm z : V ≃ₗ[K₀] V) ∈ (fieldFrame e hsmul F).La.range
    change (z : V ≃ₗ[K] V) ∈ F.La.range at hz
    have hz' := hmap.symm ▸ hz
    obtain ⟨a, ha, hza⟩ := hz'
    have heq : restrictScalarsHom e hsmul (E.symm z : V ≃ₗ[K₀] V) =
        (z : V ≃ₗ[K] V) := by
      rw [← derivedFieldEquiv_coe]
      exact congrArg Subtype.val (E.apply_symm_apply z)
    have heq' : (E.symm z : V ≃ₗ[K₀] V) = a :=
      restrictScalarsHom_injective (heq.trans hza.symm)
    rw [heq']
    exact ha

end Derived

end CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

end
