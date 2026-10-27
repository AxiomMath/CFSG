module

public import CFSG.Assembly.E6FourNeighbourFacts
public import CFSG.Assembly.GL83HalfSplitSection16
public import CFSG.Assembly.StandardTypeRecognitionDefs

public section

namespace CFSG.Assembly

open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem largeEvenRawDatum_exists' {lab : LargeEvenLabel} {Q : LargeEvenRawCont}
    (h : LargeEvenRawDatum lab Q) :
    ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)), Q R I F := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [CFSG.Assembly.LargeEvenRawDatum] at h ⊢
  all_goals try split_ifs at h
  all_goals first
    | (obtain ⟨K, _, _, -, b, c, -, hq⟩ := h; exact ⟨_, _, _, _, hq⟩)
    | (obtain ⟨K, _, _, -, hq⟩ := h; exact ⟨_, _, _, _, hq⟩)

theorem e6four_J_facts {p : ℕ} {J : Subgroup G}
    (hJ : LargeEvenMarking J fun lab _ _ _ _ _ =>
      LargeEvenHalfSplitE6FourException p lab (center J = ⊥)) :
    p = 5 ∧ center J = ⊥ ∧ E6FourMark J ∧ IsQuasisimple J := by
  have hJmark := hJ
  obtain ⟨hperf, lab, hlab, hraw⟩ := hJ
  obtain ⟨R, _, I, F, hs, hna, θ, hP⟩ := largeEvenRawDatum_exists' hraw
  obtain ⟨-, -, hZ, hp5⟩ := hP
  refine ⟨hp5, hZ, ?_, ?_⟩
  · exact standardTypeRecognitionMarking_mono (fun lab R _ I F θ h => ⟨h.1, h.2.1⟩) hJmark
  · exact ⟨hperf, θ.isSimpleGroup⟩

theorem E6FourInnerFive.of_mulEquiv {J J' : Type} [Group J] [Group J'] (e : J ≃* J')
    (h : E6FourInnerFive J) : E6FourInnerFive J' := by
  intro α hα
  have hα' : ((MulAut.congr e).symm α) ^ 5 = 1 := by
    apply (MulAut.congr e).injective
    rw [map_pow, MulEquiv.apply_symm_apply, hα, map_one]
  obtain ⟨j, hj⟩ := h ((MulAut.congr e).symm α) hα'
  refine ⟨e j, ?_⟩
  have hcongr : MulAut.congr e (MulAut.conj j) = MulAut.conj (e j) := by
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply, mul_assoc]
  calc MulAut.conj (e j) = MulAut.congr e (MulAut.conj j) := hcongr.symm
    _ = MulAut.congr e ((MulAut.congr e).symm α) := by rw [hj]
    _ = α := MulEquiv.apply_symm_apply _ α

theorem E6FourInnerPerfect.of_mulEquiv {J J' : Type} [Group J] [Group J'] (e : J ≃* J')
    (h : E6FourInnerPerfect J) : E6FourInnerPerfect J' := by
  intro P' hP'
  let P : Subgroup (MulAut J) := P'.map (MulAut.congr e).symm.toMonoidHom
  have hPperf : Group.IsPerfect P := by
    haveI : Group.IsPerfect P' := hP'
    exact Group.IsPerfect.map (H := P') (f := (MulAut.congr e).symm.toMonoidHom)
  have hle := h P hPperf
  intro α hα
  have hψα : (MulAut.congr e).symm α ∈ P := ⟨α, hα, rfl⟩
  obtain ⟨j, hj⟩ := hle hψα
  refine ⟨e j, ?_⟩
  have hcongr : MulAut.congr e (MulAut.conj j) = MulAut.conj (e j) := by
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply, mul_assoc]
  calc MulAut.conj (e j) = MulAut.congr e (MulAut.conj j) := hcongr.symm
    _ = MulAut.congr e ((MulAut.congr e).symm α) := by rw [hj]
    _ = α := MulEquiv.apply_symm_apply _ α

end CFSG.Assembly

end
