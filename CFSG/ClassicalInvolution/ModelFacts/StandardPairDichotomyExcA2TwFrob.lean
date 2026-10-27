module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E6Factor
public import CFSG.ClassicalInvolution.ModelFacts.TwistedE6PairCore
public import CFSG.ClassicalInvolution.ModelFacts.TwistedE6PairLevi
public import CFSG.ClassicalInvolution.ModelFacts.TwistedLeviDescent
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExc

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LocalAnalysis.ComponentInitial

theorem thetaE6_eq_leviE6 : thetaE6 = LeviE6.thetaE6 := thetaE6_eq.trans rfl

section Frob

variable (p : ℕ) [Fact p.Prime] (e : ℕ)

local notation "kE6" => LeviE6.E6Closure p e

theorem frobE6_pinnedX_of_fixed {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (hρ : permLattice TwistTag.E6.perm γ = γ) {s : kE6} (hs0 : s ≠ 0)
    (hs : iterateFrobenius kE6 p e s = s)
    (hfix : LeviE6.frobE6 p e (pinnedX .E6 kE6 γ s) = pinnedX .E6 kE6 γ s) (c : kE6) :
    LeviE6.frobE6 p e (pinnedX .E6 kE6 γ c) = pinnedX .E6 kE6 γ (iterateFrobenius kE6 p e c) := by
  obtain ⟨μ, hμ⟩ := exists_frobTwistGL_diagram_pinnedX_unit p TwistTag.E6 (k := kE6) e hγ
  rw [hρ] at hμ
  have h1 := hμ s
  rw [hs] at h1
  have h2 : pinnedX TwistTag.E6.tag kE6 γ ((μ : kE6) * s) = pinnedX TwistTag.E6.tag kE6 γ s :=
    h1.symm.trans hfix
  have h3 := pinnedX_injective (τ := TwistTag.E6.tag) (R := kE6) γ h2
  have hμ1 : (μ : kE6) = 1 := mul_right_cancel₀ hs0 (h3.trans (one_mul _).symm)
  have h4 := hμ c
  rw [hμ1, one_mul] at h4
  exact h4

theorem frobE6_pinnedX_thetaE6 (hp2 : p ≠ 2) (he : 1 ≤ e) (c : kE6) :
    LeviE6.frobE6 p e (pinnedX .E6 kE6 LeviE6.thetaE6 c) =
      pinnedX .E6 kE6 LeviE6.thetaE6 (iterateFrobenius kE6 p e c) := by
  have hfix := (mem_fixedPointsIn.1 (twistedE6Phi_mem_fixedPointsIn p e hp2 he
    (xFixed (frobQ p e) LeviE6.isRoot_thetaE6 LeviE6.rho_thetaE6 (1 : GaloisField p (2 * e))
      (map_one _)))).2
  have hΦ := LeviE6.phiE6_xFixed_thetaE6_one p e
  have hfix' : LeviE6.frobE6 p e (LeviE6.phiE6 p e (xFixed (frobQ p e) LeviE6.isRoot_thetaE6
      LeviE6.rho_thetaE6 (1 : GaloisField p (2 * e)) (map_one _))) =
      LeviE6.phiE6 p e (xFixed (frobQ p e) LeviE6.isRoot_thetaE6
        LeviE6.rho_thetaE6 (1 : GaloisField p (2 * e)) (map_one _)) := hfix
  rw [hΦ] at hfix'
  exact frobE6_pinnedX_of_fixed p e LeviE6.isRoot_thetaE6 LeviE6.rho_thetaE6 (e6Sign_ne_zero _)
    (map_intCast _ _) hfix' c

theorem frobE6_pinnedX_neg_thetaE6 (hp2 : p ≠ 2) (he : 1 ≤ e) (c : kE6) :
    LeviE6.frobE6 p e (pinnedX .E6 kE6 (-LeviE6.thetaE6) c) =
      pinnedX .E6 kE6 (-LeviE6.thetaE6) (iterateFrobenius kE6 p e c) := by
  have hfix := (mem_fixedPointsIn.1 (twistedE6Phi_mem_fixedPointsIn p e hp2 he
    (xFixed (frobQ p e) (IsRoot.neg LeviE6.isRoot_thetaE6) LeviE6.rho_neg_thetaE6
      (1 : GaloisField p (2 * e)) (map_one _)))).2
  have hΦ := LeviE6.phiE6_xFixed_neg_thetaE6_one p e
  have hfix' : LeviE6.frobE6 p e (LeviE6.phiE6 p e (xFixed (frobQ p e)
      (IsRoot.neg LeviE6.isRoot_thetaE6) LeviE6.rho_neg_thetaE6
      (1 : GaloisField p (2 * e)) (map_one _))) =
      LeviE6.phiE6 p e (xFixed (frobQ p e) (IsRoot.neg LeviE6.isRoot_thetaE6)
        LeviE6.rho_neg_thetaE6 (1 : GaloisField p (2 * e)) (map_one _)) := hfix
  rw [hΦ] at hfix'
  exact frobE6_pinnedX_of_fixed p e (IsRoot.neg LeviE6.isRoot_thetaE6) LeviE6.rho_neg_thetaE6
    (e6Sign_ne_zero _) (map_intCast _ _) hfix' c

theorem frobE6_rootSL2_thetaE6 (hp2 : p ≠ 2) (he : 1 ≤ e) (A : SL2 kE6) :
    LeviE6.frobE6 p e (rootSL2 .E6 kE6 thetaE6 A) =
      rootSL2 .E6 kE6 thetaE6 (Matrix.SpecialLinearGroup.map (iterateFrobenius kE6 p e) A) := by
  rw [thetaE6_eq_leviE6]
  have h := MonoidHom.eq_of_eqOn_dense (sl2_closure_upper_lower (K := kE6))
    (f := (LeviE6.frobE6 p e).comp (rootSL2 .E6 kE6 LeviE6.thetaE6))
    (g := (rootSL2 .E6 kE6 LeviE6.thetaE6).comp
      (Matrix.SpecialLinearGroup.map (iterateFrobenius kE6 p e))) ?_
  · exact DFunLike.congr_fun h A
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · change LeviE6.frobE6 p e (rootSL2 .E6 kE6 LeviE6.thetaE6 (uSL c)) =
      rootSL2 .E6 kE6 LeviE6.thetaE6
        (Matrix.SpecialLinearGroup.map (iterateFrobenius kE6 p e) (uSL c))
    rw [map_uSL, rootSL2_uSL_eq, rootSL2_uSL_eq, frobE6_pinnedX_thetaE6 p e hp2 he, map_zsmul]
  · obtain ⟨η, hη, hv⟩ := exists_rootSL2_vSL_eq (K := kE6) LeviE6.isRoot_thetaE6
    change LeviE6.frobE6 p e (rootSL2 .E6 kE6 LeviE6.thetaE6 (vSL c)) =
      rootSL2 .E6 kE6 LeviE6.thetaE6
        (Matrix.SpecialLinearGroup.map (iterateFrobenius kE6 p e) (vSL c))
    rw [map_vSL, hv, hv, frobE6_pinnedX_neg_thetaE6 p e hp2 he, map_mul]
    rcases mul_self_eq_one_iff.1 hη with rfl | rfl
    · rw [map_one]
    · rw [map_neg, map_one]

theorem perm_mem_JE6 {j : Fin (Tag.rank .E6)} (hj : j ∈ JE6) : TwistTag.E6.perm j ∈ JE6 := by
  have hj' : j.val ≠ 1 := hj
  show (TwistTag.E6.perm j).val ≠ 1
  revert hj'
  fin_cases j <;> decide

theorem frobE6_mem_h1E6 (hp2 : p ≠ 2) (he : 1 ≤ e) {g : ModGL .E6 kE6} (hg : g ∈ h1E6 kE6) :
    LeviE6.frobE6 p e g ∈ h1E6 kE6 := by
  obtain ⟨n, hn, A, rfl⟩ := hg
  refine ⟨LeviE6.frobE6 p e n, ?_,
    Matrix.SpecialLinearGroup.map (iterateFrobenius kE6 p e) A, ?_⟩
  · exact frobTwistGL_mem_parabolicLevi_diagram p TwistTag.E6 e (fun _ hj => perm_mem_JE6 hj) hn
  · rw [map_mul, frobE6_rootSL2_thetaE6 p e hp2 he]

theorem frobE6_mem_levi {g : ModGL .E6 kE6} (hg : g ∈ parabolicLevi .E6 kE6 JE6) :
    LeviE6.frobE6 p e g ∈ parabolicLevi .E6 kE6 JE6 :=
  frobTwistGL_mem_parabolicLevi_diagram p TwistTag.E6 e (fun _ hj => perm_mem_JE6 hj) hg

theorem frobE6_signDiagE6 {δ : Fin (Tag.rank .E6) → ℤ}
    (hδρ : permLattice TwistTag.E6.perm δ = δ) :
    LeviE6.frobE6 p e (signDiagE6 kE6 δ) = signDiagE6 kE6 δ := by
  have hsign : ∀ i, thetaDiag δ (-1 : kE6ˣ) i = 1 ∨ thetaDiag δ (-1 : kE6ˣ) i = -1 :=
    thetaDiag_neg_one_sign_E6 δ
  have h := frobTwistGL_diagramMap_rootDiagUnit_of_sign p TwistTag.E6 e (k := kE6)
    (b := thetaDiag δ (-1 : kE6ˣ)) hsign
  have h2 : (fun i => thetaDiag δ (-1 : kE6ˣ) (TwistTag.E6.perm.symm i)) =
      thetaDiag δ (-1 : kE6ˣ) := by
    funext i
    simp only [thetaDiag]
    congr 1
    have h1 := iform_permLattice_E6 δ (Pi.single (TwistTag.E6.perm.symm i) 1)
    rw [hδρ, permLattice_single, Equiv.apply_symm_apply] at h1
    exact h1.symm
  unfold signDiagE6
  exact h.trans (congrArg (rootDiagUnit TwistTag.E6.tag) h2)

end Frob

end CFSG.ClassicalInvolution.ModelFacts.Levi
