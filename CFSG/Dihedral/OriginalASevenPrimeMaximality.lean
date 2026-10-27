module

public import CFSG.Dihedral.OriginalASevenPrimeNormalizer
import all CFSG.Dihedral.BlueprintDefs
public import CFSG.Dihedral.PrimeClassPartition
public import CFSG.Dihedral.PrimeNormalizerQuotientAlternatives

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem prime_isMaxNormalized_of_aSeven_model (e : G ≃* alternatingGroup (Fin 7))
    (p : ℕ) (hp : p ∈ primeSupport d.R) (P : Subgroup G) (hP : IsSylowIn p P d.R)
    (hPS : NormalizedBy P (d.S : Subgroup G)) :
    IsMaxNormalized p (d.S : Subgroup G) P := by
  let : Fact p.Prime := ⟨hp.1⟩
  have hPeq := d.prime_sylow_eq_R_of_aSeven_model e p hp P hP
  have hpodd : Odd p := d.R_odd.of_dvd_nat hp.2
  refine ⟨hP.2.1, hPS, ?_⟩
  intro Q hQp hQS hPQ
  have hRQ : d.R ≤ Q := hPeq ▸ hPQ
  have hCQ : d.C ≤ Subgroup.normalizer (Q : Set G) := by
    rw [d.decomposition]
    exact sup_le (hRQ.trans Subgroup.le_normalizer) hQS
  have hte : BenderSuzuki.PFAppendixIII.IsInvolution (e d.t) := by
    refine ⟨?_, ?_⟩
    · intro h
      exact d.t_isInvolution_general.1 (e.injective (by simpa using h))
    · simpa only [map_pow, map_one] using congrArg e d.t_isInvolution_general.2
  have hmapnorm : Subgroup.centralizer ({e d.t} : Set (alternatingGroup (Fin 7))) ≤
      Subgroup.normalizer (Q.map e.toMonoidHom : Set (alternatingGroup (Fin 7))) := by
    have h := Subgroup.map_mono (f := e.toMonoidHom) hCQ
    rw [show d.C = Subgroup.centralizer ({d.t} : Set G) by
      simpa only [t] using d.centralizer, centralizer_singleton_map,
      Subgroup.map_equiv_normalizer_eq] at h
    exact h
  have hmapcent := aSeven_invariant_oddP_subgroup_centralized p hp.1 hpodd
    (Q.map e.toMonoidHom) (IsPGroup.map hQp e.toMonoidHom) hte hmapnorm
  have hQC : Q ≤ d.C := by
    rw [d.centralizer]
    change Q ≤ Subgroup.centralizer ({d.t} : Set G)
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.mp
      (hmapcent (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
    change e x * e d.t = e d.t * e x at h
    apply e.injective
    simpa only [map_mul] using h
  obtain ⟨a, ha⟩ := hQp.exists_card_eq
  have hQR := d.odd_subgroup_le_R_of_le_C Q hQC (ha ▸ hpodd.pow)
  exact le_antisymm (hQR.trans hPeq.symm.le) hPQ

theorem prime_not_centralized_by_sylow_of_aSeven_model
    (e : G ≃* alternatingGroup (Fin 7))
    (p : ℕ) (hp : p ∈ primeSupport d.R) (P : Subgroup G) (hP : IsSylowIn p P d.R) :
    ¬ P ≤ Subgroup.centralizer (d.S : Set G) := by
  intro hcent
  have hPeq := d.prime_sylow_eq_R_of_aSeven_model e p hp P hP
  have hR : d.R ≠ ⊥ := hPeq ▸ d.prime_sylow_ne_bot p hp P hP
  have hRcent : d.R ≤ Subgroup.centralizer (d.S : Set G) := hPeq ▸ hcent
  have hE : d.commonE = d.R := inf_eq_left.mpr hRcent
  exact hR (hE.symm.trans (d.commonE_eq_bot_of_aSeven_model e))

theorem sigma_zero_eq_empty_of_aSeven_model (e : G ≃* alternatingGroup (Fin 7)) :
    sigma 0 d.R = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hprime, P, hP, hpred⟩ := (mem_sigma_iff 0 p d.R).mp hp
  have hHP : d.HP P = Subgroup.normalizer (P : Set G) := by
    rw [d.HP_eq_N_of_aSeven_model e p hprime P hP,
      d.prime_sylow_eq_R_of_aSeven_model e p hprime P hP]
    rfl
  apply not_hasNormalTwoComplement_of_card_twentyFour (d.HP P)
    (d.HP_quotient_card_of_aSeven_model e p hprime P hP)
  rw [hHP]
  exact hpred.2

end CFSG.DihedralBlueprint.OriginalData
