module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.F11

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu
open CFSG.Quasithin (pairVec)
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

theorem conj_t0_ne_t0
    {c : Q3} (hc : c ∈ Zq) (h0 : c • x0 = x0) (h1 : c • x1 = x2) : c * t0 * c⁻¹ ≠ t0 := by
  intro h
  let x : ↥E0q := e0.symm (cocodeCoords.κ (pairVec (tauM24 0) (tauM24 1)))
  let n : ↥Zq := ⟨c, hc⟩
  have hxt : ((x : ↥Zq) : Q3) = t0 := rfl
  have hnt : (n : Q3) = c := rfl
  have hx : e0 x = cocodeCoords.κ (pairVec (tauM24 0) (tauM24 1)) :=
    MulEquiv.apply_symm_apply e0 _
  have hconj : cocodeExtension_Zq.conjE n x = x := by
    apply Subtype.ext
    apply Subtype.ext
    rw [cocodeExtension_Zq.coe_conjE]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hnt, hxt]
    exact h
  have hκ : rho11 AutPerm le_rfl (cocodeExtension_Zq.π n)
      (cocodeCoords.κ (pairVec (tauM24 0) (tauM24 1))) =
      cocodeCoords.κ (pairVec (tauM24 0) (tauM24 1)) := by
    have hp := cocodeExtension_Zq.π_apply_e n x
    rw [hconj, hx] at hp
    exact hp
  have hp0 : planeHom n 0 = 0 := by
    refine (smul_planePt_eq_planePt_iff n 0 0).1 ?_
    simpa only [planePt_zero] using h0
  have hp1 : planeHom n 1 = 2 := by
    refine (smul_planePt_eq_planePt_iff n 1 2).1 ?_
    simpa only [planePt_one, planePt_two] using h1
  have hpi0 : ((cocodeExtension_Zq.π n : ↥AutPerm) : Equiv.Perm (Fin 24)) (tauM24 0) =
      tauM24 0 := by
    rw [π_cocodeExtension_Zq]
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply, hp0]
  have hpi1 : ((cocodeExtension_Zq.π n : ↥AutPerm) : Equiv.Perm (Fin 24)) (tauM24 1) =
      tauM24 2 := by
    rw [π_cocodeExtension_Zq]
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply, hp1]
  have hκ' : cocodeCoords.κ (pairVec (tauM24 0) (tauM24 2)) =
      cocodeCoords.κ (pairVec (tauM24 0) (tauM24 1)) := by
    rw [rho11_kappa_pairVec] at hκ
    rwa [hpi0, hpi1] at hκ
  rcases kappa11_pairVec_inj (tauM24.injective.ne (by decide : (0 : Fin 24) ≠ 2))
    tauM24_zero_ne_one hκ' with ⟨-, h21⟩ | ⟨h01, -⟩
  · exact (by decide : (2 : Fin 24) ≠ 1) (tauM24.injective h21)
  · exact tauM24_zero_ne_one h01

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
