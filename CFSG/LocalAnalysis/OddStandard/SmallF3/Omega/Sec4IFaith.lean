module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ICent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeHigh
import CFSG.LieType.Simplicity.Classical

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem isSimpleGroup_omegaProj_seven (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) (hσ : quadSign Q = 1) :
    IsSimpleGroup (omegaProj hQ) := by
  have hmodel : LieModel (omegaProj hQ) .POmegaOdd 3 3 1 :=
    isOmegaStar_seven_iff.mp ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, hdim, hσ,
      ⟨MulEquiv.refl _⟩⟩
  have hm := hmodel.statedClassicalModel_of_ne_zero (by norm_num : (3 : ℕ) ≠ 0)
  exact (CFSG.LieType.Simplicity.fam_classical_converse (omegaProj hQ)
    ⟨.POmegaOdd, 3, 3, 1, hm⟩).2.2

theorem eq_one_of_central_omegaProj_seven (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) (hσ : quadSign Q = 1) {w : ProjOrth Q}
    (hw : w ∈ omegaProj hQ) (hc : ∀ w' ∈ omegaProj hQ, w * w' = w' * w) : w = 1 := by
  haveI := isSimpleGroup_omegaProj_seven hQ hdim hσ
  have hcen : (⟨w, hw⟩ : omegaProj hQ) ∈ Subgroup.center (omegaProj hQ) := by
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (hc z z.2).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (omegaProj hQ)) with h | h
  · rw [h, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  · exfalso
    letI : CommGroup (omegaProj hQ) := Group.commGroupOfCenterEqTop h
    have hp := IsSimpleGroup.prime_card (α := omegaProj hQ)
    rw [natCard_omegaProj_seven hQ hdim] at hp
    exact absurd hp (by norm_num)

theorem sec4I_eq_one_of_commute (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) (hσ : quadSign Q = 1) {g : ProjOrth Q}
    (hg : ∀ w ∈ omegaProj hQ, g * w = w * g) : g = 1 := by
  by_contra hg1
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (piGroup Q) g
  have hsq : toProj Q h * toProj Q h ∈ omegaProj hQ :=
    (mem_omegaProj_iff hQ).mpr ⟨h * h, mul_self_mem_omegaGroup hQ h, by rw [map_mul]⟩
  have hgg : toProj Q h * toProj Q h = 1 := by
    refine eq_one_of_central_omegaProj_seven hQ hdim hσ hsq (fun w' hw' => ?_)
    calc toProj Q h * toProj Q h * w' = toProj Q h * (toProj Q h * w') := by group
      _ = toProj Q h * (w' * toProj Q h) := by rw [hg w' hw']
      _ = (toProj Q h * w') * toProj Q h := by group
      _ = (w' * toProj Q h) * toProj Q h := by rw [hg w' hw']
      _ = w' * (toProj Q h * toProj Q h) := by group
  have hle : omegaProj hQ ≤ Subgroup.centralizer ({toProj Q h} : Set (ProjOrth Q)) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hg w hw).symm
  have hdvd := Subgroup.card_dvd_of_le hle
  obtain ⟨hpos, hlt⟩ := natCard_centralizer_lt_seven hQ hdim hσ hgg hg1
  exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt)

theorem conjNormal_injective_seven (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) (hσ : quadSign Q = 1) :
    Function.Injective (MulAut.conjNormal : ProjOrth Q →* MulAut (omegaProj hQ)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  refine sec4I_eq_one_of_commute hQ hdim hσ (fun w hw => ?_)
  have h := congrArg (fun φ : MulAut (omegaProj hQ) => ((φ ⟨w, hw⟩ : omegaProj hQ) : ProjOrth Q))
    hg
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
  exact mul_inv_eq_iff_eq_mul.mp h

end CFSG.OddStandard.SmallF3.Omega
