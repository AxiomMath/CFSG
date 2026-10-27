module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2TwDescent
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E6Rational

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional

theorem perm_deltaE6 : permLattice TwistTag.E6.perm deltaE6 = deltaE6 :=
  List.ofFn_injective (by decide : List.ofFn (permLattice TwistTag.E6.perm deltaE6) =
    List.ofFn deltaE6)

theorem exists_split_or_anti_TwE6 {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e)
    {c g : twistedE6Group p e}
    (hc2 : LeviE6.phiE6 p e c * LeviE6.phiE6 p e c = 1)
    (hcd : LeviE6.phiE6 p e c * signDiagE6 (LeviE6.E6Closure p e) thetaE6 =
      signDiagE6 (LeviE6.E6Closure p e) thetaE6 * LeviE6.phiE6 p e c)
    (hgc : LeviE6.phiE6 p e g * signDiagE6 (LeviE6.E6Closure p e) thetaE6 *
      (LeviE6.phiE6 p e g)⁻¹ = LeviE6.phiE6 p e c)
    (hnc : ¬ ∀ A : SL2 (LeviE6.E6Closure p e),
      LeviE6.phiE6 p e c * rootSL2 .E6 (LeviE6.E6Closure p e) thetaE6 A =
        rootSL2 .E6 (LeviE6.E6Closure p e) thetaE6 A * LeviE6.phiE6 p e c) :
    (∃ x : twistedE6Group p e,
      LeviE6.phiE6 p e x * signDiagE6 (LeviE6.E6Closure p e) thetaE6 =
        signDiagE6 (LeviE6.E6Closure p e) thetaE6 * LeviE6.phiE6 p e x ∧
      LeviE6.phiE6 p e x * LeviE6.phiE6 p e c * (LeviE6.phiE6 p e x)⁻¹ =
        signDiagE6 (LeviE6.E6Closure p e) deltaE6) ∨
    (∃ v ∈ h1E6 (LeviE6.E6Closure p e),
      v * LeviE6.phiE6 p e c * v⁻¹ = signDiagE6 (LeviE6.E6Closure p e) deltaE6 ∧
      ∃ m ∈ parabolicLevi .E6 (LeviE6.E6Closure p e) JE6,
        LeviE6.frobE6 p e v * v⁻¹ = m * rootSL2 .E6 (LeviE6.E6Closure p e) thetaE6 WSL) := by
  classical
  have hfin : Finite (GaloisField p (2 * e)) := Nat.finite_of_card_ne_zero (by
    rw [card_galoisField_two_mul' p e he]
    exact (pow_pos (pow_pos (Fact.out : p.Prime).pos e) _).ne')
  have hk : ringChar (LeviE6.E6Closure p e) ≠ 2 := by
    rw [ringChar.eq (LeviE6.E6Closure p e) p]
    exact hp2
  have halg := LeviE6.isAlgebraic_zmod_E6Closure (p := p) (e := e)
  set y := LeviE6.phiE6 p e c with hy_def
  obtain ⟨hycG, hFy0⟩ := mem_fixedPointsIn.1 (twistedE6Phi_mem_fixedPointsIn p e hp2 he c)
  have hFy : LeviE6.frobE6 p e y = y := hFy0
  have hg'G : LeviE6.phiE6 p e g ∈ adjointGroup .E6 (LeviE6.E6Closure p e) :=
    (mem_fixedPointsIn.1 (twistedE6Phi_mem_fixedPointsIn p e hp2 he g)).1
  have hyH : y ∈ h1E6 (LeviE6.E6Closure p e) := by
    have hcT : y ∈ toralCentralizer .E6 (LeviE6.E6Closure p e)
        (thetaDiag thetaE6 (-1 : (LeviE6.E6Closure p e)ˣ)) := by
      rw [mem_toralCentralizer]
      refine ⟨hycG, ?_⟩
      show signDiagE6 (LeviE6.E6Closure p e) thetaE6 * y *
        (signDiagE6 (LeviE6.E6Closure p e) thetaE6)⁻¹ = y
      rw [mul_inv_eq_iff_eq_mul, hcd]
    have hM := toralCentralizer_le_toralRootGroup_of_sign (Or.inr (Or.inr (Or.inl rfl))) hk
      (thetaDiag_neg_one_sign_E6 thetaE6) hcT
    exact toralRootGroup_le_h1E6 hk hM
  obtain ⟨v, hv, hvy⟩ := exists_conj_signDiag_deltaE6 halg hp2 hg'G hc2 hyH hgc hnc
  have hFv : LeviE6.frobE6 p e v * v⁻¹ ∈ h1E6 (LeviE6.E6Closure p e) :=
    mul_mem (frobE6_mem_h1E6 p e hp2 he hv) (inv_mem hv)
  have hFd : LeviE6.frobE6 p e (signDiagE6 (LeviE6.E6Closure p e) deltaE6) =
      signDiagE6 (LeviE6.E6Closure p e) deltaE6 := frobE6_signDiagE6 p e perm_deltaE6
  have hud : (LeviE6.frobE6 p e v * v⁻¹) * signDiagE6 (LeviE6.E6Closure p e) deltaE6 =
      signDiagE6 (LeviE6.E6Closure p e) deltaE6 * (LeviE6.frobE6 p e v * v⁻¹) := by
    have hF1 : LeviE6.frobE6 p e v * y * (LeviE6.frobE6 p e v)⁻¹ =
        signDiagE6 (LeviE6.E6Closure p e) deltaE6 := by
      have := congrArg (LeviE6.frobE6 p e) hvy
      rw [map_mul, map_mul, map_inv, hFy, hFd] at this
      exact this
    have hy' : v⁻¹ * signDiagE6 (LeviE6.E6Closure p e) deltaE6 * v = y := by rw [← hvy]; group
    have h1 : (LeviE6.frobE6 p e v * v⁻¹) * signDiagE6 (LeviE6.E6Closure p e) deltaE6 *
        (LeviE6.frobE6 p e v * v⁻¹)⁻¹ = signDiagE6 (LeviE6.E6Closure p e) deltaE6 := by
      calc (LeviE6.frobE6 p e v * v⁻¹) * signDiagE6 (LeviE6.E6Closure p e) deltaE6 *
          (LeviE6.frobE6 p e v * v⁻¹)⁻¹ =
          LeviE6.frobE6 p e v * (v⁻¹ * signDiagE6 (LeviE6.E6Closure p e) deltaE6 * v) *
            (LeviE6.frobE6 p e v)⁻¹ := by group
        _ = _ := by rw [hy', hF1]
    calc (LeviE6.frobE6 p e v * v⁻¹) * signDiagE6 (LeviE6.E6Closure p e) deltaE6 =
        ((LeviE6.frobE6 p e v * v⁻¹) * signDiagE6 (LeviE6.E6Closure p e) deltaE6 *
          (LeviE6.frobE6 p e v * v⁻¹)⁻¹) * (LeviE6.frobE6 p e v * v⁻¹) := by group
      _ = _ := by rw [h1]
  rcases eq_levi_or_eq_levi_mul_WSL_E6 hk isPartnerE6_deltaE6 hFv hud with hJ | ⟨m, hm, hmu⟩
  · left
    obtain ⟨h, hh, hFh, hhy⟩ := exists_h1_fixed_conj_TwE6 p hp2 he isPartnerE6_deltaE6
      perm_deltaE6 hv hFy hvy hJ
    have hhG : h ∈ adjointGroup .E6 (LeviE6.E6Closure p e) := h1E6_le_adjointGroup hh
    obtain ⟨u, huT, x, hx⟩ : ∃ u : ModGL .E6 (LeviE6.E6Closure p e),
        u ∈ torusGroup .E6 (LeviE6.E6Closure p e) ∧ ∃ x : twistedE6Group p e,
          h = u * LeviE6.phiE6 p e x := by
      obtain ⟨u, huT, -, x, hx⟩ := exists_torus_mul_of_mem_fixedPointsIn p e hp2 he
        (mem_fixedPointsIn.2 ⟨hhG, hFh⟩)
      exact ⟨u, huT, x, hx⟩
    have hΦx : LeviE6.phiE6 p e x = u⁻¹ * h := eq_inv_mul_of_mul_eq hx.symm
    refine ⟨x, ?_, ?_⟩
    · rw [hΦx]
      have h1 := mul_signDiagE6_theta_of_mem_h1E6 hh
      have h2 := rootDiagUnit_mul_comm_of_mem_torusGroup (τ := .E6)
        (thetaDiag thetaE6 (-1 : (LeviE6.E6Closure p e)ˣ)) (inv_mem huT)
      change u⁻¹ * h * signDiagE6 _ thetaE6 = signDiagE6 _ thetaE6 * (u⁻¹ * h)
      calc u⁻¹ * h * signDiagE6 (LeviE6.E6Closure p e) thetaE6 =
          u⁻¹ * (h * signDiagE6 (LeviE6.E6Closure p e) thetaE6) := by group
        _ = u⁻¹ * (signDiagE6 (LeviE6.E6Closure p e) thetaE6 * h) := by rw [h1]
        _ = (u⁻¹ * signDiagE6 (LeviE6.E6Closure p e) thetaE6) * h := by group
        _ = (signDiagE6 (LeviE6.E6Closure p e) thetaE6 * u⁻¹) * h := by
          rw [show u⁻¹ * signDiagE6 (LeviE6.E6Closure p e) thetaE6 =
            signDiagE6 (LeviE6.E6Closure p e) thetaE6 * u⁻¹ from h2.symm]
        _ = _ := by group
    · rw [hΦx]
      have h3 := rootDiagUnit_mul_comm_of_mem_torusGroup (τ := .E6)
        (thetaDiag deltaE6 (-1 : (LeviE6.E6Closure p e)ˣ)) (inv_mem huT)
      calc u⁻¹ * h * y * (u⁻¹ * h)⁻¹ = u⁻¹ * (h * y * h⁻¹) * u := by group
        _ = u⁻¹ * signDiagE6 (LeviE6.E6Closure p e) deltaE6 * u := by rw [hhy]
        _ = (signDiagE6 (LeviE6.E6Closure p e) deltaE6 * u⁻¹) * u := by
          rw [show u⁻¹ * signDiagE6 (LeviE6.E6Closure p e) deltaE6 =
            signDiagE6 (LeviE6.E6Closure p e) deltaE6 * u⁻¹ from h3.symm]
        _ = _ := by group
  · right
    exact ⟨v, hv, hvy, m, hm, hmu⟩

end CFSG.ClassicalInvolution.ModelFacts.Levi
