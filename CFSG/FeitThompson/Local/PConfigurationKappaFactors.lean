module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
import CFSG.FeitThompson.Local.KappaDerivedComplement
import CFSG.FeitThompson.Local.KappaResidualInPrescribedComplement
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived
import CFSG.FeitThompson.Local.HallCoreInSigmaCore
import CFSG.FeitThompson.Foundations.SolvableHallExistence
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
public import Mathlib.Tactic.Monotonicity.Lemmas

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G] [Finite G] {M E W₁ W₂ : Subgroup G}

theorem notMem_sigmaPrimes_of_dvd_natCard_W₁ [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    (hM : IsCoatom M) (hc : IsWitnessedPConfiguration M E W₁ W₂) {p : ℕ} (hp : p.Prime)
    (hpW : p ∣ Nat.card ↥W₁) : p ∉ sigmaPrimes M := by
  intro hpσ
  have hpM' : ¬ p ∣ Nat.card (⁅M, M⁆ : Subgroup G) := fun hdvd =>
    Nat.Prime.not_coprime_iff_dvd.2 ⟨p, hp, hpW, hdvd⟩ hc.coprime_natCard_W₁_natCard_commutator
  have hpM : p ∣ Nat.card ↥M := hpW.trans (Subgroup.card_dvd_of_le hc.le_M_W₁)
  have hSHall := CFSG.FeitThompson.Proofs.isHallSubgroup_subgroupOf_sigmaCore hna hodd hsolv hM
  have hmul : Nat.card ↥((sigmaCore M).subgroupOf M) * ((sigmaCore M).subgroupOf M).index
      = Nat.card ↥M := Subgroup.card_mul_index _
  have hpS : p ∣ Nat.card ↥(sigmaCore M) := by
    rw [natCard_subgroupOf (sigmaCore_le M)] at hmul
    rcases (Nat.Prime.dvd_mul hp).1 (hmul ▸ hpM) with h | h
    · exact h
    · exact absurd hpσ (isPiNumber_iff.1 hSHall.index p
        (Nat.mem_primeFactors.2 ⟨hp, h, Subgroup.index_ne_zero_of_finite⟩))
  exact hpM' (hpS.trans (Subgroup.card_dvd_of_le
    (CFSG.FeitThompson.Proofs.sigmaCore_le_commutator hna hodd hsolv hM)))

theorem le_centralizer_W₂ (hc : IsWitnessedPConfiguration M E W₁ W₂) :
    W₂ ≤ centralizer (W₁ : Set G) := fun _ hy =>
  Subgroup.mem_centralizer_iff.2 fun _ hg => hc.commute_W₁_W₂ hg hy

theorem le_inf_sigmaCore_centralizer_W₂ [IsSimpleGroup G] (hM : IsCoatom M)
    (hc : IsWitnessedPConfiguration M E W₁ W₂) :
    W₂ ≤ sigmaCore M ⊓ centralizer (W₁ : Set G) :=
  le_inf (hc.le_hallCore_W₂.trans (hallCoreIn_le_sigmaCore hM)) (le_centralizer_W₂ hc)

theorem mem_kappaPrimes_of_dvd_natCard_W₁ [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    (hM : IsCoatom M) (hc : IsWitnessedPConfiguration M E W₁ W₂) {p : ℕ} (hp : p.Prime)
    (hpW : p ∣ Nat.card ↥W₁) : p ∈ kappaPrimes M := by
  have : Fact p.Prime := ⟨hp⟩
  have hcyc := hc.isCyclic_W₁
  have hpM' : ¬ p ∣ Nat.card (⁅M, M⁆ : Subgroup G) := fun hdvd =>
    Nat.Prime.not_coprime_iff_dvd.2 ⟨p, hp, hpW, hdvd⟩ hc.coprime_natCard_W₁_natCard_commutator
  have hpM : p ∣ Nat.card ↥M := hpW.trans (Subgroup.card_dvd_of_le hc.le_M_W₁)
  have hfact : (Nat.card ↥M).factorization p = (Nat.card ↥W₁).factorization p := by
    rw [hc.natCard_M_eq, Nat.factorization_mul (Nat.card_pos (α := ↥(⁅M, M⁆ : Subgroup G))).ne'
      (Nat.card_pos (α := ↥W₁)).ne']
    simp [Nat.factorization_eq_zero_of_not_dvd hpM']
  set S := (default : Sylow p ↥W₁) with hSdef
  set P : Subgroup G := (S : Subgroup ↥W₁).map W₁.subtype with hPdef
  have hPW : P ≤ W₁ := Subgroup.map_subtype_le _
  have hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p := by
    rw [hPdef, Subgroup.card_subtype, hfact]
    exact S.card_eq_multiplicity
  have hPbot : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPcard
    exact hp.ne_one (Nat.dvd_one.1 (hPcard ▸ dvd_pow_self p
      (by rw [hfact]; exact (hp.factorization_pos_of_dvd (Nat.card_pos (α := ↥W₁)).ne' hpW).ne')))
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hPbot
  refine (mem_kappaPrimes_iff_exists_subgroup hp).2 ⟨hpM,
    notMem_sigmaPrimes_of_dvd_natCard_W₁ hna hodd hsolv hM hc hp hpW,
    P, hPW.trans hc.le_M_W₁, hPcard, Subgroup.isCyclic_of_le hPW, x, x.2,
    by simpa using hx1, fun h => hc.ne_bot_W₂ (le_bot_iff.1 ?_)⟩
  refine le_trans (le_inf_sigmaCore_centralizer_W₂ hM hc) ?_
  rw [← h]
  exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.2 (hPW x.2)))

theorem kappaPrimes_nonempty_of_isWitnessedPConfiguration [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M)
    (hc : IsWitnessedPConfiguration M E W₁ W₂) : (kappaPrimes M).Nonempty := by
  obtain ⟨p, hp, hpW⟩ := Nat.exists_prime_and_dvd
    (n := Nat.card ↥W₁) fun h => hc.ne_bot_W₁ (Subgroup.card_eq_one.1 h)
  exact ⟨p, mem_kappaPrimes_of_dvd_natCard_W₁ hna hodd hsolv hM hc hp hpW⟩

theorem exists_isHallPiOf_kappaPrimes (M : Subgroup G) [Group.IsSolvable ↥M] :
    ∃ K : Subgroup G, CFSG.FeitThompson.Prep03.IsHallPiOf (kappaPrimes M) K M := by
  obtain ⟨K', hK'⟩ := exists_isHallSubgroup (X := ↥M) (kappaPrimes M)
  refine ⟨K'.map M.subtype, isHallPiOf_of_isHallSubgroup_subgroupOf (Subgroup.map_subtype_le _) ?_⟩
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  exact hK'

theorem isHallPiSubgroup_subgroupOf_W₁ [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    (hM : IsCoatom M) (hc : IsWitnessedPConfiguration M E W₁ W₂) {K : Subgroup G}
    (hK : CFSG.FeitThompson.Prep03.IsHallPiOf (kappaPrimes M) K M)
    (hmain : CFSG.FeitThompson.Prep03.IsSemidirect M (⁅M, M⁆ : Subgroup G) K) :
    IsHallPiSubgroup (kappaPrimes M) (W₁.subgroupOf M) := by
  have hidx : (W₁.subgroupOf M).index = K.relIndex M := by
    rw [← Subgroup.relIndex, hc.relIndex_W₁_eq_natCard_commutator,
      natCard_commutator_eq_relIndex hK.1 hmain]
  refine ⟨isPiSubgroup_iff.2 fun p hp => ?_, fun p hp => ?_⟩
  · rw [natCard_subgroupOf hc.le_M_W₁] at hp
    exact mem_kappaPrimes_of_dvd_natCard_W₁ hna hodd hsolv hM hc
      (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  · rw [hidx] at hp
    exact hK.2.2 p hp

theorem inf_sigmaCore_centralizer_W₁_eq_W₂ [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    (hM : IsCoatom M) (hc : IsWitnessedPConfiguration M E W₁ W₂) :
    sigmaCore M ⊓ centralizer (W₁ : Set G) = W₂ := by
  refine le_antisymm ?_ (le_inf_sigmaCore_centralizer_W₂ hM hc)
  obtain ⟨w, hw, hw1, heq⟩ := hc.exists_inf_centralizer_eq_W₂
  calc sigmaCore M ⊓ centralizer (W₁ : Set G)
      ≤ (⁅M, M⁆ : Subgroup G) ⊓ centralizer ({w} : Set G) :=
        inf_le_inf (CFSG.FeitThompson.Proofs.sigmaCore_le_commutator hna hodd hsolv hM)
          (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hw))
    _ = W₂ := heq

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson

universe u

theorem FNI_p_configuration_kappa_factors (h₁ : Statements.FNI_kappa_local_pair.{u})
    (h₂ : Statements.FNI_kappa_semiprime_complement_existence.{u}) :
    Statements.FNI_p_configuration_kappa_factors.{u} := by
  intro G _ _ hG M E W₁ W₂ hM hc
  have : Fintype G := Fintype.ofFinite G
  have hsimple := hG.isSimpleGroup
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hM.1
  have hκ : (kappaPrimes M).Nonempty :=
    kappaPrimes_nonempty_of_isWitnessedPConfiguration hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hM hc
  obtain ⟨K, hK⟩ := exists_isHallPiOf_kappaPrimes M
  have hsetup : Prep03.IsKappaSetup G M K (Prep03.cent (sigmaCore M) (K : Set G))
      (K ⊔ Prep03.cent (sigmaCore M) (K : Set G)) :=
    { ambient := ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative,
        hG.isSolvable_of_ne_top⟩
      isCoatom := hM
      kappa_nonempty := hκ
      isHall_K := hK
      A_eq := rfl
      Z_eq := rfl }
  have hmain := (FNI_kappa_derived_complement h₁ h₂ G M K _ _ hsetup).1
  exact ⟨hκ, isHallPiSubgroup_subgroupOf_W₁ hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hM hc hK hmain,
    inf_sigmaCore_centralizer_W₁_eq_W₂ hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hM hc⟩

end CFSG.FeitThompson.Proofs

end
