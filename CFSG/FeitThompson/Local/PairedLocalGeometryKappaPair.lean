module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.KappaPairReciprocalHallData
import CFSG.FeitThompson.Local.KappaGlobalPairExhaustion
import CFSG.FeitThompson.Local.KappaResidualInPrescribedComplement
import CFSG.FeitThompson.Local.HallKappaSubgroupTI
import CFSG.FeitThompson.Local.ExceptionalInvariantSylowSeparation
import CFSG.FeitThompson.OddOrder.CommutingSubgroupsJoinProduct
import CFSG.FeitThompson.Representations.NoInducedIrreducibleFixedOrbitOrder
import CFSG.FeitThompson.Representations.PrimeTILocalTransporterTISet
import CFSG.FeitThompson.Definitions.TISubsetWithItsExactNormalizer

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson

universe u

theorem FBG_paired_local_geometry
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_kappa_local_pair.{u})
    (h₃ : Statements.FNI_kappa_normalizer_centralizer_structure.{u})
    (h₄ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₅ : Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₆ : Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₇ : Statements.FTS_plane_maximal_overgroups.{u})
    (h₈ : Statements.FTS_sigma_prime_separation.{u})
    (h₉ : Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    Statements.FBG_paired_local_geometry.{u} := by
  have hpair := FNI_kappa_pair_hall_intersection h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉
  have hexh := FNI_kappa_global_pair_exhaustion h₁ h₂ h₄ h₉
  intro G _ _ hG M hM K U hKhall hUM hsemiM hsemiE hKnormU hK Kstar hKstar
  have hamb : Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hKH : Prep03.IsHallPiOf (kappaPrimes M) K M := isHallPiOf_of_isHallPiSubgroupOf hKhall
  have hkappa : (kappaPrimes M).Nonempty := by
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := Nat.card ↥K)
      fun h => hK (Subgroup.card_eq_one.1 h)
    exact ⟨p, hKH.2.1 p (Nat.mem_primeFactors.2 ⟨hp, hpd, Nat.card_pos.ne'⟩)⟩
  have hsetup : Prep03.IsKappaSetup G M K Kstar (K ⊔ Kstar) :=
    { ambient := hamb, isCoatom := hM, kappa_nonempty := hkappa, isHall_K := hKH,
      A_eq := hKstar, Z_eq := rfl }
  obtain ⟨Mstar, ⟨hMstarco, hMstarex⟩, hMstaruniq, hnc, -, hAhall, hKeq, hdir, hZcyc,
    -, -, -, -, hTI, hres⟩ := h₂ G M K Kstar (K ⊔ Kstar) hsetup
  obtain ⟨-, -, hMM, -⟩ :=
    hpair G M K Kstar (K ⊔ Kstar) Mstar hsetup hMstarco hMstarex hMstaruniq
  have hcommKA : ∀ x ∈ K, ∀ y ∈ Kstar, Commute x y := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.1
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hdir.2.2.2.2 hx) y hy).symm
  have hD : cyclicTIset K Kstar
      = (((K ⊔ Kstar : Subgroup G) : Set G) \ ((K : Set G) ∪ (Kstar : Set G))) := by
    ext z
    simp [mem_cyclicTIset, not_or]
  refine ⟨Mstar, hMstarco, ?_, isHallPiSubgroupOf_of_isHallPiOf hAhall (fun _ _ => Iff.rfl),
    hKeq, hMM, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro g hg
    exact hnc ⟨g, (show Prep03.conjSub M g = conjSubgroup M g from rfl).trans hg.symm⟩
  ·
    exact
      { left_le := by rw [hMM]; exact le_sup_left
        right_le := by rw [hMM]; exact le_sup_right
        coe_eq_mul := by rw [hMM]; exact coe_sup_eq_mul_of_commute hcommKA
        inf_eq_bot := hdir.2.2.2.1
        commutator_eq_bot := hdir.2.2.2.2 }
  ·
    rw [hMM]; exact hZcyc
  ·
    obtain ⟨hne, hnorm, hdisj⟩ := hTI
    refine { nonempty := ?_, one_notMem := ?_, normalizer_eq := ?_, disjoint_conj_image := ?_ }
    · rw [hD]; exact hne
    · rw [hD]; exact fun h => h.2 (Or.inl (one_mem K))
    · rw [hD, hnorm, hMM]
    ·
      intro g hg
      rw [hMM] at hg
      have hg' : g⁻¹ ∉ (K ⊔ Kstar : Subgroup G) := fun hc => hg (by simpa using inv_mem hc)
      have hd := hdisj g⁻¹ hg'
      rw [hD, Set.disjoint_iff_inter_eq_empty]
      have himg : (MulAut.conj g) ''
          (((K ⊔ Kstar : Subgroup G) : Set G) \ ((K : Set G) ∪ (Kstar : Set G)))
          = Prep03.conjSet
            (((K ⊔ Kstar : Subgroup G) : Set G) \ ((K : Set G) ∪ (Kstar : Set G))) g⁻¹ := by
        refine Set.image_congr' fun x => ?_
        simp
      rw [himg]
      exact hd
  ·
    intro L hL hkL
    obtain ⟨g, hgg⟩ :=
      hexh G M K Kstar (K ⊔ Kstar) Mstar hsetup hMstarco hMstarex hMstaruniq L hL hkL
    rcases hgg with h | h
    · refine Or.inl ⟨g⁻¹, ?_⟩
      have hMm : L.map (MulAut.conj g⁻¹ : G →* G) = M := h
      have hcj : conjSubgroup M g⁻¹ = L := by
        rw [CFSG.FeitThompson.conjSubgroup_eq, inv_inv, ← hMm, map_conj_inv_map_conj]
      exact hcj.symm
    · refine Or.inr ⟨g⁻¹, ?_⟩
      have hMm : L.map (MulAut.conj g⁻¹ : G →* G) = Mstar := h
      have hcj : conjSubgroup Mstar g⁻¹ = L := by
        rw [CFSG.FeitThompson.conjSubgroup_eq, inv_inv, ← hMm, map_conj_inv_map_conj]
      exact hcj.symm
  ·
    rcases hres with ⟨U₀, hU₀ne, hsd1, hsd2⟩ | ⟨V, hVne, hsd1, hsd2⟩
    ·
      refine Or.inl ?_
      intro hUbot
      have hU₀M : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) (U₀ ⊔ K) :=
        isInternalSemidirectProduct_of_isSemidirect hsd1
      have hU₀E : FreeCore.IsInternalSemidirectProduct (U₀ ⊔ K) U₀ K :=
        isInternalSemidirectProduct_of_isSemidirect hsd2
      have e1 : Nat.card ↥M = Nat.card ↥(sigmaCore M) * (Nat.card ↥U₀ * Nat.card ↥K) := by
        rw [hU₀M.natCard_eq_mul, hU₀E.natCard_eq_mul]
      have e2 : Nat.card ↥M = Nat.card ↥(sigmaCore M) * (Nat.card ↥U * Nat.card ↥K) := by
        rw [hsemiM.natCard_eq_mul, hsemiE.natCard_eq_mul]
      have e3 : Nat.card ↥U₀ * Nat.card ↥K = Nat.card ↥U * Nat.card ↥K :=
        Nat.eq_of_mul_eq_mul_left Nat.card_pos (e1.symm.trans e2)
      have e4 : Nat.card ↥U₀ = Nat.card ↥U := Nat.eq_of_mul_eq_mul_right Nat.card_pos e3
      have hcardU : Nat.card ↥U = 1 := by rw [hUbot]; exact Subgroup.card_bot
      exact hU₀ne (Subgroup.card_eq_one.1 (e4.trans hcardU))
    ·
      exact Or.inr ⟨Kstar, V, isHallPiSubgroupOf_of_isHallPiOf hAhall (fun _ _ => Iff.rfl),
        le_sup_left.trans hsd1.2.1, isInternalSemidirectProduct_of_isSemidirect hsd1,
        isInternalSemidirectProduct_of_isSemidirect hsd2,
        le_sup_right.trans hsd2.2.2.1, hVne⟩

end

end CFSG.FeitThompson.Proofs
