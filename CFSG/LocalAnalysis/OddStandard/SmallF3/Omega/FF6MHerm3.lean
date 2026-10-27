module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2HermForm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2PocketAbs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCplxConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem quadSign_hermForm_three : quadSign (hermForm 3) = -1 := by
  have h := (exists_mul_self_eq_piOrth_iff (hermForm_nondegenerate 3)).mp
    ⟨omegaOrth 3, omegaOrth_mul_self 3⟩
  rw [finrank_hermSpace] at h
  rw [h.2]
  decide

theorem ff6m_exists_iso3 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {y : OGroup Q} (hy : y * y = piOrth Q) :
    ∃ e : (hermForm 3).IsometryEquiv Q,
      ∀ x, e (omega9 • x) = (y : V ≃ₗ[ZMod 3] V) (e x) := by
  obtain ⟨e0⟩ := equivalent_of_quadSign_eq (hermForm_nondegenerate 3) hQ
    (by rw [finrank_hermSpace, hdim]) (quadSign_hermForm_three.trans hsgn.symm)
  set E0 := TauCeti.QuadraticMap.orthogonalGroupCongr e0 with hE0
  have hp : E0 (omegaOrth 3) * E0 (omegaOrth 3) = piOrth Q := by
    rw [← map_mul, omegaOrth_mul_self, hE0, orthogonalGroupCongr_piOrth]
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_mul_self_eq_piOrth hQ hp hy)
  let ec : Q.IsometryEquiv Q :=
    { toLinearEquiv := (c : V ≃ₗ[ZMod 3] V)
      map_app' := fun x => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp c.2 x }
  refine ⟨e0.trans ec, fun x => ?_⟩
  have key : ∀ v, (y : V ≃ₗ[ZMod 3] V) v =
      (c : V ≃ₗ[ZMod 3] V) ((E0 (omegaOrth 3) : V ≃ₗ[ZMod 3] V)
        ((c : V ≃ₗ[ZMod 3] V).symm v)) := by
    intro v
    have h := congrArg (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V) v) hc
    exact h.symm
  have h3 : (E0 (omegaOrth 3) : V ≃ₗ[ZMod 3] V) (e0 x) = e0 (omega9 • x) := by
    rw [hE0, TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply]
    change e0.toLinearEquiv (omega9 • e0.toLinearEquiv.symm (e0.toLinearEquiv x)) =
      e0.toLinearEquiv (omega9 • x)
    rw [LinearEquiv.symm_apply_apply]
  have h4 := key ((c : V ≃ₗ[ZMod 3] V) (e0 x))
  rw [LinearEquiv.symm_apply_apply, h3] at h4
  exact h4.symm

theorem ff6m_exists_frame_iso3 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {y : OGroup Q} (hy : y * y = piOrth Q) :
    ∃ E : OGroup (hermForm 3) ≃* OGroup Q, E (omegaOrth 3) = y ∧
      E (piOrth (hermForm 3)) = piOrth Q ∧
      ∀ g, E g ∈ omegaGroup hQ ↔ g ∈ omegaGroup (hermForm_nondegenerate 3) := by
  obtain ⟨e, he⟩ := ff6m_exists_iso3 hQ hdim hsgn hy
  have h2 : 2 ≤ Module.finrank (ZMod 3) (Fin 3 → F9) := by
    rw [finrank_hermSpace]
    norm_num
  refine ⟨TauCeti.QuadraticMap.orthogonalGroupCongr e, ?_, orthogonalGroupCongr_piOrth e,
    fun g => mem_omegaGroup_orthogonalGroupCongr_iff (hermForm_nondegenerate 3) hQ h2 e g⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  rw [TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply]
  change e.toLinearEquiv (omega9 • e.toLinearEquiv.symm v) = (y : V ≃ₗ[ZMod 3] V) v
  have h := he (e.toLinearEquiv.symm v)
  change e.toLinearEquiv (omega9 • e.toLinearEquiv.symm v) =
    (y : V ≃ₗ[ZMod 3] V) (e.toLinearEquiv (e.toLinearEquiv.symm v)) at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h

end CFSG.OddStandard.SmallF3.Omega
