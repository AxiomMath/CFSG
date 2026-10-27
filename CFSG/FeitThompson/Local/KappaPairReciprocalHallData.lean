module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.KappaFixedIntersectionSigmaContainment
import CFSG.FeitThompson.Local.TwoBetaFixedCoresHallPosition
import CFSG.FeitThompson.Local.KappaResidualPrimeOvergroupIntersection
import CFSG.FeitThompson.Local.KappaResidualInPrescribedComplement
import CFSG.FeitThompson.Local.HallKappaSubgroupTI
import CFSG.FeitThompson.Local.SignalizerAuxiliaryBase
import CFSG.FeitThompson.Local.MixedElementsKappaCandidateTorus
import CFSG.FeitThompson.Local.NilpotentSigmaPrimeSeparation
import CFSG.FeitThompson.Local.MixedFittingCentralizerConstrained
import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep03

universe u

variable {G : Type*} [Group G]

theorem le_centralizer_singleton_of_isCyclic {Z : Subgroup G} (hZ : IsCyclic ↥Z) {x : G}
    (hx : x ∈ Z) : Z ≤ centralizer ({x} : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (hZ.isMulCommutative.is_comm.comm (⟨z, hz⟩ : ↥Z) ⟨x, hx⟩)

theorem FNI_kappa_pair_hall_intersection
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_kappa_local_pair.{u})
    (h₃ : Statements.FNI_kappa_normalizer_centralizer_structure.{u})
    (h₄ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₅ : Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₆ : Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₇ : Statements.FTS_plane_maximal_overgroups.{u})
    (h₈ : Statements.FTS_sigma_prime_separation.{u})
    (h₉ : Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    Statements.FNI_kappa_pair_hall_intersection.{u} := by
  intro G _ _ M K A Z Ms hsetup hMs hex huniq
  obtain ⟨Mstar, ⟨hMstarco, hexs⟩, -, hnc, hAbot, hAhall, hKeq, hdir, hZcyc,
    hNKM, hNAMstar, -, -, hTI, -⟩ := h₂ G M K A Z hsetup
  have hMM : Mstar = Ms := huniq Mstar hMstarco hexs
  subst hMM
  have hamb := hsetup.ambient
  have hM := hsetup.isCoatom
  have hKH := hsetup.isHall_K
  have hAeq := hsetup.A_eq
  have hZeq := hsetup.Z_eq
  have hFT : IsFTAmbient G :=
    ⟨hamb.isSimpleGroup, hamb.not_isMulCommutative, hamb.odd_natCard, hamb.forall_isSolvable⟩
  have hmin : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hamb.odd_natCard, hamb.isSimpleGroup, hamb.not_isMulCommutative, hamb.forall_isSolvable⟩
  have hAS : A ≤ sigmaCore M := by rw [hAeq]; exact inf_le_left
  have hKM : K ≤ M := hKH.1
  have hAM : A ≤ M := hAS.trans (sigmaCore_le M)
  have hKZ : K ≤ Z := by rw [hZeq]; exact le_sup_left
  have hAZ : A ≤ Z := by rw [hZeq]; exact le_sup_right
  have hZM : Z ≤ M := by rw [hZeq]; exact sup_le hKM hAM
  have hZMstar : Z ≤ Mstar := by rw [← hNAMstar]; exact inf_le_right
  have hAMstar : A ≤ Mstar := hAZ.trans hZMstar
  have hKS : K ≤ sigmaCore Mstar := by rw [← hKeq]; exact inf_le_left
  have hMstarsolv : Group.IsSolvable ↥Mstar := hamb.forall_isSolvable Mstar hMs.1
  have hdisj : sigmaPrimes M ∩ sigmaPrimes Mstar = ∅ :=
    h₈ G hmin M Mstar hM hMs fun g hg => hnc ⟨g, hg.symm⟩
  have hSinf : sigmaCore M ⊓ sigmaCore Mstar = ⊥ :=
    inf_eq_bot_of_isPiSubgroup (isPiSubgroup_sigmaCore M) (isPiSubgroup_sigmaCore Mstar) hdisj
  have hApi : IsPiSubgroup (sigmaPrimes M) A := (isPiSubgroup_sigmaCore M).of_le hAS
  obtain ⟨Y, hYhall, hAY⟩ := exists_isHallPiSubgroupOf_ge_of_isPiSubgroup hMstarsolv hAMstar hApi
  have hYne : Y ⊓ (sigmaCore M ⊓ centralizer (K : Set G)) ≠ ⊥ := by
    rw [show (sigmaCore M ⊓ centralizer (K : Set G)) = A from hAeq.symm, inf_eq_right.2 hAY]
    exact hAbot
  have hYS : Y ≤ sigmaCore M :=
    FTS_kappa_fixed_intersection_sigma_containment h₁ h₄ h₅ h₆ h₇ h₈ h₉ G hFT M hM
      hsetup.kappa_nonempty K (isHallPiSubgroupOf_of_isHallPiOf hKH fun _ _ => Iff.rfl)
      Y hYhall.isPiSubgroup hYne
  have hYK : ⁅Y, K⁆ ≤ sigmaCore M := by
    have h := commutator_le_of_le_of_le_normalizer (K := sigmaCore M) (X := M) (Y := K) (A := Y)
      hKM (le_normalizer_sigmaCore M) hYS
    rwa [Subgroup.commutator_comm] at h
  have hYK' : ⁅Y, K⁆ ≤ sigmaCore Mstar :=
    commutator_le_of_le_of_le_normalizer (K := sigmaCore Mstar) (X := Mstar) (Y := Y) (A := K)
      hYhall.le (le_normalizer_sigmaCore Mstar) hKS
  have hcomm : (⁅Y, K⁆ : Subgroup G) = ⊥ := le_bot_iff.1 (hSinf ▸ le_inf hYK hYK')
  have hYC : Y ≤ centralizer (K : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hYA : Y = A := le_antisymm (by rw [hAeq]; exact le_inf hYS hYC) hAY
  have hAhallσ : IsHallPiOf (sigmaPrimes M) A Mstar := by
    rw [← hYA]; exact isHallPiOf_of_isHallPiSubgroupOf hYhall
  have hcarddvd : Nat.card ↥(sigmaCore M ⊓ Mstar) ∣ Nat.card ↥A :=
    natCard_dvd_natCard_of_isPiSubgroup (hYA ▸ hYhall) inf_le_right
      ((isPiSubgroup_sigmaCore M).of_le inf_le_left)
  have h2 : sigmaCore M ⊓ Mstar = A :=
    (eq_of_le_of_card_ge (le_inf hAS hAMstar) (Nat.le_of_dvd Nat.card_pos hcarddvd)).symm
  have h3 : M ⊓ Mstar = Z := by
    refine le_antisymm ?_ (le_inf hZM hZMstar)
    have hnorm : M ⊓ Mstar ≤ normalizer (A : Set G) := by
      rw [← h2]
      exact le_trans (inf_le_inf (le_normalizer_sigmaCore M) Subgroup.le_normalizer)
        Subgroup.inf_normalizer_le_normalizer_inf
    rw [← hNAMstar]
    exact le_inf hnorm inf_le_right
  refine ⟨hAhallσ, h2, h3, fun x hxK hx1 y hyA hy1 => ⟨?_, ?_, ?_⟩⟩
  ·
    change M ⊓ centralizer ({x} : Set G) = Z
    obtain ⟨X, hXx, hXp⟩ := exists_prime_card_subgroup_le_zpowers hx1
    have hXK : X ≤ K := hXx.trans (zpowers_le.2 hxK)
    obtain ⟨-, hNX, -⟩ := (h₃ G M K A Z hsetup).2.2 X hXK hXp
    refine le_antisymm ?_ (le_inf hZM (le_centralizer_singleton_of_isCyclic hZcyc (hKZ hxK)))
    rw [← hNKM, ← hNX]
    exact le_inf (inf_le_right.trans ((centralizer_le_centralizer_of_le_zpowers hXx).trans
      (Subgroup.centralizer_le_normalizer _))) inf_le_left
  ·
    change Mstar ⊓ centralizer ({y} : Set G) = Z
    have hkappaMstar : (kappaPrimes Mstar).Nonempty := by
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := Nat.card ↥A)
        fun h => hAbot (Subgroup.card_eq_one.1 h)
      exact ⟨p, hAhall.2.1 p (Nat.mem_primeFactors.2 ⟨hp, hpd, Nat.card_pos.ne'⟩)⟩
    have hsetupStar : IsKappaSetup G Mstar A K (A ⊔ K) :=
      { ambient := hamb, isCoatom := hMs, kappa_nonempty := hkappaMstar,
        isHall_K := hAhall, A_eq := hKeq.symm, Z_eq := rfl }
    obtain ⟨Y', hY'y, hY'p⟩ := exists_prime_card_subgroup_le_zpowers hy1
    have hY'A : Y' ≤ A := hY'y.trans (zpowers_le.2 hyA)
    obtain ⟨-, hNY, -⟩ := (h₃ G Mstar A K (A ⊔ K) hsetupStar).2.2 Y' hY'A hY'p
    refine le_antisymm ?_ (le_inf hZMstar (le_centralizer_singleton_of_isCyclic hZcyc (hAZ hyA)))
    rw [← hNAMstar, ← hNY]
    exact le_inf (inf_le_right.trans ((centralizer_le_centralizer_of_le_zpowers hY'y).trans
      (Subgroup.centralizer_le_normalizer _))) inf_le_left
  ·
    have hKA : K ⊓ A = ⊥ := hdir.2.2.2.1
    have hxyZ : x * y ∈ Z := Z.mul_mem (hKZ hxK) (hAZ hyA)
    have hxyT : x * y ∈ (Z : Set G) \ ((K : Set G) ∪ (A : Set G)) := by
      refine ⟨hxyZ, ?_⟩
      rintro (hk | ha)
      · have hyK : y ∈ K := by
          have h := K.mul_mem (K.inv_mem hxK) hk
          simpa [mul_assoc] using h
        have hmem : y ∈ (⊥ : Subgroup G) := hKA ▸ Subgroup.mem_inf.2 ⟨hyK, hyA⟩
        exact hy1 (by simpa using hmem)
      · have hxA : x ∈ A := by
          have h := A.mul_mem ha (A.inv_mem hyA)
          simpa [mul_assoc] using h
        have hmem : x ∈ (⊥ : Subgroup G) := hKA ▸ Subgroup.mem_inf.2 ⟨hxK, hxA⟩
        exact hx1 (by simpa using hmem)
    obtain ⟨-, -, hTIdisj⟩ := hTI
    refine le_antisymm ?_ (le_centralizer_singleton_of_isCyclic hZcyc hxyZ)
    intro g hg
    by_contra hgZ
    have hfix : g⁻¹ * (x * y) * g = x * y := by
      have h : g * (x * y) = x * y * g := Subgroup.mem_centralizer_singleton_iff.1 hg
      calc g⁻¹ * (x * y) * g = g⁻¹ * (x * y * g) := by group
        _ = g⁻¹ * (g * (x * y)) := by rw [h]
        _ = x * y := by group
    have hmem : x * y ∈ ((Z : Set G) \ ((K : Set G) ∪ (A : Set G))) ∩
        Prep03.conjSet ((Z : Set G) \ ((K : Set G) ∪ (A : Set G))) g :=
      ⟨hxyT, ⟨x * y, hxyT, hfix⟩⟩
    rw [hTIdisj g hgZ] at hmem
    exact hmem

end

end CFSG.FeitThompson.Proofs
