module

public import CFSG.Dihedral.OriginalASevenPrimeNormalizer
public import CFSG.Dihedral.NormalizerSylowLifting
public import CFSG.Dihedral.GorensteinWalter.PSL2OddCentralizerTransport
import all CFSG.Dihedral.BlueprintDefs
public import CFSG.Dihedral.PrimeClassPartition

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem prime_normalizer_eq_C_of_psl2_model (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : G ≃* PSL2 K)
    (p : ℕ) (hp : p ∈ primeSupport d.R) (P : Subgroup G) (hP : IsSylowIn p P d.R) :
    Subgroup.normalizer (P : Set G) = d.C := by
  have h := odd_centralizer_normalizer_of_psl2_equiv K hK e
    d.t_isInvolution_general P (d.prime_sylow_ne_bot p hp P hP)
    (d.R_odd.of_dvd_nat (Subgroup.card_dvd_of_le hP.1))
    (by simpa only [d.centralizer, t] using hP.1.trans d.R_le)
  simpa only [d.centralizer, t] using h

theorem HP_eq_C_of_psl2_model (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : G ≃* PSL2 K)
    (p : ℕ) (hp : p ∈ primeSupport d.R) (P : Subgroup G) (hP : IsSylowIn p P d.R) :
    d.HP P = d.C := by
  let Z := (Subgroup.center P).map P.subtype
  have hZP : Z ≤ P := Subgroup.map_subtype_le _
  have h := odd_centralizer_normalizer_of_psl2_equiv K hK e
    d.t_isInvolution_general Z (d.prime_center_ne_bot p hp P hP)
    (d.R_odd.of_dvd_nat (Subgroup.card_dvd_of_le (hZP.trans hP.1)))
    (by simpa only [d.centralizer, t] using (hZP.trans hP.1).trans d.R_le)
  change Subgroup.normalizer (Z : Set G) = d.C
  simpa only [d.centralizer, t] using h

theorem JP_eq_R_of_psl2_model (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : G ≃* PSL2 K)
    (p : ℕ) (hp : p ∈ primeSupport d.R) (P : Subgroup G) (hP : IsSylowIn p P d.R) :
    d.JP P = d.R := by
  change oddCoreOf (d.HP P) = d.R
  rw [d.HP_eq_C_of_psl2_model K hK e p hp P hP]
  exact d.centralizer_oddCore_eq_R

theorem prime_sylow_ambient_of_psl2_model (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : G ≃* PSL2 K)
    (p : ℕ) (hp : p ∈ primeSupport d.R) (P : Subgroup G) (hP : IsSylowIn p P d.R) :
    IsSylowIn p P ⊤ := by
  apply isSylowIn_top_of_normalizer p hp.1 P
  rw [d.prime_normalizer_eq_C_of_psl2_model K hK e p hp P hP]
  exact d.prime_sylow_isSylowIn_C p hp P hP

theorem not_prime_fixed_fourgroup_of_psl2_model (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : G ≃* PSL2 K)
    (p : ℕ) (hp : p ∈ primeSupport d.R) (P : Subgroup G) (hP : IsSylowIn p P d.R)
    (V : Subgroup G) (hV : IsFourGroup V) :
    ¬ P ≤ Subgroup.centralizer (V : Set G) := by
  intro hcent
  let : IsCyclic d.R := d.R_isCyclic_of_psl2_model K hK e
  have hPcyclic : IsCyclic P := Subgroup.isCyclic_of_le hP.1
  have hmapcyclic := (e.subgroupMap P).isCyclic.mp hPcyclic
  have hmapne : P.map e.toMonoidHom ≠ ⊥ := by
    intro h
    exact d.prime_sylow_ne_bot p hp P hP
      ((Subgroup.map_eq_bot_iff_of_injective P e.injective).mp h)
  have hmapodd : Odd (Nat.card (P.map e.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact d.R_odd.of_dvd_nat (Subgroup.card_dvd_of_le hP.1)
  exact psl2_no_kleinFour_centralizes_odd_cyclic K hK
    (P.map e.toMonoidHom) (V.map e.toMonoidHom) hmapcyclic hmapne hmapodd
    (isKleinFour_map_mulEquiv_cross V (isKleinFour_of_isFourGroup V hV) e)
    (centralizer_map_le_of_mulEquiv e P V (Subgroup.le_centralizer_iff.mp hcent))

theorem prime_not_centralized_by_sylow_of_psl2_model (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : G ≃* PSL2 K)
    (p : ℕ) (hp : p ∈ primeSupport d.R) (P : Subgroup G) (hP : IsSylowIn p P d.R) :
    ¬ P ≤ Subgroup.centralizer (d.S : Set G) := by
  intro hcent
  exact d.not_prime_fixed_fourgroup_of_psl2_model K hK e p hp P hP (d.V 0)
    (isFourGroup_of_isKleinFour _ (d.V_isKleinFour_general 0))
    (hcent.trans (Subgroup.centralizer_le (d.V_le_sylow 0)))

theorem sigma_one_eq_empty_of_psl2_model (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : G ≃* PSL2 K) : sigma 1 d.R = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hprime, P, hP, hpred⟩ := (mem_sigma_iff 1 p d.R).mp hp
  apply hpred.2
  rw [d.prime_normalizer_eq_C_of_psl2_model K hK e p hprime P hP]
  exact d.centralizer_hasNormalTwoComplement

end CFSG.DihedralBlueprint.OriginalData
