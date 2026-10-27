module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryTwGen
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryE6Main
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2TwPair
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2InterfaceTw
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

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits

section Frob

variable (p : ℕ) [Fact p.Prime] (e : ℕ)

local notation "kE6" => LeviE6.E6Closure p e

theorem frobE6_pinnedX_of_rho_fixed (hp2 : p ≠ 2) (he : 1 ≤ e) {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : IsRoot .E6 γ) (hρ : rho γ = γ) (c : kE6) :
    LeviE6.frobE6 p e (pinnedX .E6 kE6 γ c) = pinnedX .E6 kE6 γ (c ^ p ^ e) := by
  have hfix : LeviE6.frobE6 p e (LeviE6.phiE6 p e (xFixed (frobQ p e) hγ hρ
        (1 : GaloisField p (2 * e)) (map_one _))) =
      LeviE6.phiE6 p e (xFixed (frobQ p e) hγ hρ (1 : GaloisField p (2 * e)) (map_one _)) :=
    (mem_fixedPointsIn.1 (twistedE6Phi_mem_fixedPointsIn p e hp2 he
      (xFixed (frobQ p e) hγ hρ (1 : GaloisField p (2 * e)) (map_one _)))).2
  have hΦ : LeviE6.phiE6 p e (xFixed (frobQ p e) hγ hρ (1 : GaloisField p (2 * e))
      (map_one _)) =
      pinnedX .E6 kE6 γ ((e6Sign γ : kE6) * algebraMap (GaloisField p (2 * e)) kE6 1) :=
    twistedE6Phi_xFixed p e kE6 hγ hρ (1 : GaloisField p (2 * e)) (map_one _)
  rw [map_one, mul_one] at hΦ
  rw [hΦ] at hfix
  have hfix' := hfix
  rw [frobE6_pinnedX_of_fixed p e hγ hρ (e6Sign_ne_zero _) (map_intCast _ _) hfix' c,
    iterateFrobenius_def]

theorem a2FrobAct_twE6 (hp2 : p ≠ 2) (he : 1 ≤ e) :
    A2FrobAct (LeviE6.frobE6 p e) (p ^ e) thetaE6 deltaE6 :=
  ⟨fun x => frobE6_pinnedX_of_rho_fixed p e hp2 he isRoot_thetaE6 rho_thetaE6' x,
    fun x => frobE6_pinnedX_of_rho_fixed p e hp2 he (IsRoot.neg isRoot_thetaE6)
      (rho_neg_of_fixed rho_thetaE6') x,
    fun x => frobE6_pinnedX_of_rho_fixed p e hp2 he isPartnerE6_deltaE6.1 perm_deltaE6 x,
    fun x => frobE6_pinnedX_of_rho_fixed p e hp2 he (IsRoot.neg isPartnerE6_deltaE6.1)
      (rho_neg_of_fixed perm_deltaE6) x⟩

end Frob

section Cocycle

variable {k : Type} [Field k] [IsAlgClosed k]

theorem cocycle_conj_pinnedX_E6_of_comm (hk : ringChar k ≠ 2) {u m : ModGL .E6 k}
    (hud : signDiagE6 k deltaE6 * u = u * signDiagE6 k deltaE6)
    (hm : m ∈ parabolicLevi .E6 k JE6) (hcoc : u = m * rootSL2 .E6 k thetaE6 WSL) :
    ∃ Λ₀ Λ₁ Λ₂ Λ₃ : k, Λ₀ * Λ₁ = 1 ∧ Λ₂ * Λ₃ = 1 ∧
      (∀ x : k, u * pinnedX .E6 k thetaE6 x * u⁻¹ = pinnedX .E6 k (-thetaE6) (Λ₀ * x)) ∧
      (∀ x : k, u * pinnedX .E6 k (-thetaE6) x * u⁻¹ = pinnedX .E6 k thetaE6 (Λ₁ * x)) ∧
      (∀ x : k, u * pinnedX .E6 k deltaE6 x * u⁻¹ = pinnedX .E6 k (-deltaE6) (Λ₂ * x)) ∧
      (∀ x : k, u * pinnedX .E6 k (-deltaE6) x * u⁻¹ = pinnedX .E6 k deltaE6 (Λ₃ * x)) := by
  have hθ := isRoot_thetaE6
  have hδ := isPartnerE6_deltaE6.1
  refine cocycle_conj_pinnedX_of_comm (J := JE6) hk hθ hδ hud hm (nWordE6_mem_levi l0E6_mem_J)
    hcoc (nuElt_comm_rootDiagUnit_thetaDiag hθ l0E6 l0E6_comm) ?_ ?_ ?_ ?_
    (fun s hs hsd => mem_diagAct_of_levi_comm_E6 hk hs hsd)
  · exact nuElt_conj_pinnedX hθ l0E6 hθ (by
      rw [thetaE6_eq]
      unfold l0E6 simpleWordAct idxE6
      decide +kernel)
  · exact nuElt_conj_pinnedX hθ l0E6 (IsRoot.neg hθ) (by
      rw [thetaE6_eq]
      unfold l0E6 simpleWordAct idxE6
      decide +kernel)
  · exact nuElt_conj_pinnedX hθ l0E6 hδ (by
      rw [thetaE6_eq]
      unfold l0E6 simpleWordAct idxE6
      decide +kernel)
  · exact nuElt_conj_pinnedX hθ l0E6 (IsRoot.neg hδ) (by
      rw [thetaE6_eq]
      unfold l0E6 simpleWordAct idxE6
      decide +kernel)

end Cocycle

section Alpha

variable {p e : ℕ} [Fact p.Prime]

local notation "kE6" => LeviE6.E6Closure p e

theorem exists_unitary_alpha_Tw (hp2 : p ≠ 2) (he : 1 ≤ e) {c v m : ModGL .E6 kE6}
    (hFc : LeviE6.frobE6 p e c = c) (hv : v ∈ h1E6 kE6)
    (hd : v * c * v⁻¹ = signDiagE6 kE6 deltaE6) (hm : m ∈ parabolicLevi .E6 kE6 JE6)
    (hcoc : LeviE6.frobE6 p e v * v⁻¹ = m * rootSL2 .E6 kE6 thetaE6 WSL) :
    ∃ α : Su (GaloisField p (2 * e)) p e 3 →* ModGL .E6 kE6, Function.Injective α ∧
      (∀ y, α y ∈ adjointGroup .E6 kE6) ∧ (∀ y, LeviE6.frobE6 p e (α y) = α y) ∧
      (∀ A : Su (GaloisField p (2 * e)) p e 2, ∃ A' : SL2 kE6,
        α (embSUid (unitaryInvolution (GaloisField p (2 * e)) p e) 2 A) =
          rootSL2 .E6 kE6 thetaE6 A') ∧
      α (embSUid (unitaryInvolution (GaloisField p (2 * e)) p e) 0
        (suNegOne (GaloisField p (2 * e)) p e)) = c := by
  have hk2 : ringChar kE6 ≠ 2 := by
    rw [ringChar.eq kE6 p]
    exact hp2
  have hFd : LeviE6.frobE6 p e (signDiagE6 kE6 deltaE6) = signDiagE6 kE6 deltaE6 :=
    frobE6_signDiagE6 p e perm_deltaE6
  have hud : signDiagE6 kE6 deltaE6 * (LeviE6.frobE6 p e v * v⁻¹) =
      (LeviE6.frobE6 p e v * v⁻¹) * signDiagE6 kE6 deltaE6 := by
    have hF : LeviE6.frobE6 p e v * c * (LeviE6.frobE6 p e v)⁻¹ = signDiagE6 kE6 deltaE6 := by
      have := congrArg (LeviE6.frobE6 p e) hd
      rw [map_mul, map_mul, map_inv, hFc, hFd] at this
      exact this
    have hy' : v⁻¹ * signDiagE6 kE6 deltaE6 * v = c := by
      rw [← hd]
      group
    have h1 : (LeviE6.frobE6 p e v * v⁻¹) * signDiagE6 kE6 deltaE6 *
        (LeviE6.frobE6 p e v * v⁻¹)⁻¹ = signDiagE6 kE6 deltaE6 := by
      calc (LeviE6.frobE6 p e v * v⁻¹) * signDiagE6 kE6 deltaE6 *
          (LeviE6.frobE6 p e v * v⁻¹)⁻¹ =
          LeviE6.frobE6 p e v * (v⁻¹ * signDiagE6 kE6 deltaE6 * v) *
            (LeviE6.frobE6 p e v)⁻¹ := by group
        _ = _ := by rw [hy', hF]
    calc signDiagE6 kE6 deltaE6 * (LeviE6.frobE6 p e v * v⁻¹) =
        ((LeviE6.frobE6 p e v * v⁻¹) * signDiagE6 kE6 deltaE6 *
          (LeviE6.frobE6 p e v * v⁻¹)⁻¹) * (LeviE6.frobE6 p e v * v⁻¹) := by rw [h1]
      _ = _ := by group
  have hcocycle := cocycle_conj_pinnedX_E6_of_comm hk2 hud hm hcoc
  have hv' : ∀ t ∈ torusGroup .E6 kE6, t * v ∈ h1E6 kE6 := fun t ht =>
    mul_mem (levi_le_h1E6 (torusGroup_le_parabolicLevi JE6 ht)) hv
  obtain ⟨Em⟩ := nonempty_a2Embedding_E6 (GaloisField p (2 * e))
  exact exists_unitary_alpha_F (p := p) (e := e) hp2 isRoot_thetaE6 isPartnerE6_deltaE6.1
    a2Pairing_E6 Em (algebraMap (GaloisField p (2 * e)) kE6) (LeviE6.frobE6 p e)
    (a2FrobAct_twE6 p e hp2 he) hd hcocycle
    (fun t ht => rootDiagUnit_mul_comm_of_mem_torusGroup (thetaDiag deltaE6 (-1)) ht)
    (fun t ht => h1E6_le_adjointGroup (hv' t ht))
    (fun t ht A => conj_rootSL2_of_mem_h1E6 (hv' t ht) A)
    (by
      rw [rootSL2_HSL_eq_thetaDiag_E6 isPartnerE6_deltaE6.1,
        baseChangeGL_rootDiagUnit_thetaDiag_E6 _ deltaE6]
      rfl)

end Alpha

end CFSG.ClassicalInvolution.ModelFacts.Levi
