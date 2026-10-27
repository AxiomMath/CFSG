module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.FrameConjCharTwo

public noncomputable section

open QuadraticMap Matrix
open scoped MatrixGroups

namespace CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Transport

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] {Q : QuadraticForm K V} {Q' : QuadraticForm K W}

@[expose] def isoFrame (e : Q.IsometryEquiv Q') (F : Frame Q) : Frame Q' := by
  refine
    { P :=
        { e := e F.P.e
          f := e F.P.f
          Q_e := ?_
          Q_f := ?_
          polar_ef := ?_ }
      P' :=
        { e := e F.P'.e
          f := e F.P'.f
          Q_e := ?_
          Q_f := ?_
          polar_ef := ?_ }
      orth := { ee := ?_, ef := ?_, fe := ?_, ff := ?_ } }
  all_goals
    simp only [e.map_app, e.polar_apply, F.P.Q_e, F.P.Q_f,
      F.P'.Q_e, F.P'.Q_f, F.P.polar_ef, F.P'.polar_ef,
      F.orth.ee, F.orth.ef, F.orth.fe, F.orth.ff]

theorem isoFrame_incl (e : Q.IsometryEquiv Q') (F : Frame Q)
    (X : Matrix (Fin 2) (Fin 2) K) :
    (isoFrame e F).incl X = e (F.incl X) := by
  simp [Frame.incl_apply, isoFrame, Frame.e₁, Frame.f₁, Frame.e₂, Frame.f₂,
    map_add, map_smul]

theorem isoFrame_coords (e : Q.IsometryEquiv Q') (F : Frame Q) (v : V) :
    (isoFrame e F).coords (e v) = F.coords v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Frame.coords_apply, isoFrame, Frame.e₁, Frame.f₁, Frame.e₂, Frame.f₂,
      e.polar_apply]

theorem isoFrame_La (e : Q.IsometryEquiv Q') (F : Frame Q) (A : SL(2, K)) :
    LinearEquiv.autCongr e.toLinearEquiv (F.La A) = (isoFrame e F).La A := by
  apply LinearEquiv.ext
  intro w
  rw [LinearEquiv.autCongr_apply_apply]
  change e (F.La A (e.symm w)) = (isoFrame e F).La A w
  have hc : (isoFrame e F).coords w = F.coords (e.symm w) := by
    simpa only [e.apply_symm_apply] using isoFrame_coords e F (e.symm w)
  simp only [Frame.La_apply, map_add, e.apply_symm_apply, ← isoFrame_incl, hc]

end Transport

section CharTwo

variable {K V W : Type} [Field K] [CharP K 2] [Finite K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {Q : QuadraticForm K V} {Q' : QuadraticForm K W}

theorem exists_matched_isometry (e : Q.IsometryEquiv Q')
    (hQ' : (polarBilin Q').Nondegenerate) (F : Frame Q) (F' : Frame Q') :
    ∃ e' : Q.IsometryEquiv Q',
      (∀ X, e' (F.incl X) = F'.incl X) ∧
      ∀ A : SL(2, K), LinearEquiv.autCongr e'.toLinearEquiv (F.La A) = F'.La A := by
  obtain ⟨g, hg, hmap, hincl, hLa⟩ :=
    exists_isometry_conj_charTwo hQ' (isoFrame e F) F'
  let gIso : Q'.IsometryEquiv Q' :=
    { toLinearEquiv := g
      map_app' := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg }
  let e' := e.trans gIso
  have hframe : isoFrame e' F = F' := by
    have htrans : isoFrame e' F = (isoFrame e F).map hg := rfl
    exact htrans.trans hmap
  refine ⟨e', ?_, ?_⟩
  · intro X
    rw [← isoFrame_incl, hframe]
  · intro A
    rw [isoFrame_La, hframe]

end CharTwo

end CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

end
