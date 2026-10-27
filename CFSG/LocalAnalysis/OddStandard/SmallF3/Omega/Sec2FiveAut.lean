module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveInv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLow

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem eq_one_of_central_omegaProj_five (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) {w : ProjOrth Q} (hw : w ∈ omegaProj hQ)
    (hc : ∀ w' ∈ omegaProj hQ, w * w' = w' * w) : w = 1 := by
  obtain ⟨y, hy, rfl⟩ := (mem_omegaProj_iff hQ).mp hw
  have hπ := piOrth_not_mem_omegaGroup_five hQ hdim
  have hcen : (⟨y, hy⟩ : omegaGroup hQ) ∈ Subgroup.center (omegaGroup hQ) := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h1 : toProj Q ((y : OGroup Q) * z) = toProj Q ((z : OGroup Q) * y) := by
      rw [map_mul, map_mul]
      exact hc _ ((mem_omegaProj_iff hQ).mpr ⟨z, z.2, rfl⟩)
    have h2 : ((y : OGroup Q) * z)⁻¹ * ((z : OGroup Q) * y) ∈ piGroup Q := QuotientGroup.eq.mp h1
    rcases mem_piGroup_iff.mp h2 with h3 | h3
    · apply Subtype.ext
      exact (inv_mul_eq_one.mp h3).symm
    · exfalso
      apply hπ
      rw [← h3]
      exact (omegaGroup hQ).mul_mem ((omegaGroup hQ).inv_mem ((omegaGroup hQ).mul_mem hy z.2))
        ((omegaGroup hQ).mul_mem z.2 hy)
  have hbot : Subgroup.center (omegaGroup hQ) = ⊥ :=
    Subgroup.card_eq_one.mp (natCard_center_omegaGroup_five hQ hdim)
  rw [hbot, Subgroup.mem_bot] at hcen
  have h1 : y = 1 := congrArg Subtype.val hcen
  rw [h1, map_one]

theorem eq_one_of_commute_omegaProj_five (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) (hσ : quadSign Q = 1) {g : ProjOrth Q}
    (hg : ∀ w ∈ omegaProj hQ, g * w = w * g) : g = 1 := by
  by_contra hg1
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (piGroup Q) g
  have hsq : toProj Q h * toProj Q h ∈ omegaProj hQ :=
    (mem_omegaProj_iff hQ).mpr ⟨h * h, mul_self_mem_omegaGroup hQ h, by rw [map_mul]⟩
  have hgg : toProj Q h * toProj Q h = 1 := by
    refine eq_one_of_central_omegaProj_five hQ hdim hsq (fun w' hw' => ?_)
    calc toProj Q h * toProj Q h * w' = toProj Q h * (toProj Q h * w') := by group
      _ = toProj Q h * (w' * toProj Q h) := by rw [hg w' hw']
      _ = (toProj Q h * w') * toProj Q h := by group
      _ = (w' * toProj Q h) * toProj Q h := by rw [hg w' hw']
      _ = w' * (toProj Q h * toProj Q h) := by group
  have hle : omegaProj hQ ≤ Subgroup.centralizer ({toProj Q h} : Set (ProjOrth Q)) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hg w hw).symm
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [natCard_omegaProj_five hQ hdim] at hdvd
  rcases natCard_centralizer_involution_five hQ hdim hσ hgg hg1 with h1 | h1 | h1 | h1 <;>
    rw [h1.2] at hdvd <;> exact absurd hdvd (by decide)

theorem conjNormal_injective_five (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) (hσ : quadSign Q = 1) :
    Function.Injective (MulAut.conjNormal : ProjOrth Q →* MulAut (omegaProj hQ)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  refine eq_one_of_commute_omegaProj_five hQ hdim hσ (fun w hw => ?_)
  have h := congrArg (fun φ : MulAut (omegaProj hQ) => ((φ ⟨w, hw⟩ : omegaProj hQ) : ProjOrth Q))
    hg
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
  exact mul_inv_eq_iff_eq_mul.mp h

theorem center_eq_bot_of_mulEquiv_omegaProj_five {L : Type} [Group L] (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) (e : L ≃* omegaProj hQ) :
    Subgroup.center L = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hzc : ∀ w : omegaProj hQ, e z * w = w * e z := by
    intro w
    obtain ⟨l, rfl⟩ := e.surjective w
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz l).symm]
  have h1 : ((e z : omegaProj hQ) : ProjOrth Q) = 1 :=
    eq_one_of_central_omegaProj_five hQ hdim (e z).2
      (fun w' hw' => congrArg Subtype.val (hzc ⟨w', hw'⟩))
  exact (map_eq_one_iff e e.injective).mp (Subtype.ext h1)

theorem exists_model_five {L : Type} [Group L] (h : LieModel L .PSp 2 3 1) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
      (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate),
      Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1 ∧
        Nonempty (L ⧸ Subgroup.center L ≃* omegaProj hQ) := by
  obtain ⟨V, i1, i2, i3, Q, hQ, hdim, hs, ⟨e⟩⟩ := (isOmegaStar_five_iff (X := L)).mpr h
  refine ⟨V, i1, i2, i3, Q, hQ, hdim, hs, ⟨?_⟩⟩
  have hbot : Subgroup.center L = ⊥ := center_eq_bot_of_mulEquiv_omegaProj_five hQ hdim e
  exact ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).trans e

end CFSG.OddStandard.SmallF3.Omega
