module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.OutsideSigmaKappaSylowCoreNilpotent
import CFSG.FeitThompson.Local.SigmaCoreNontrivial
import CFSG.FeitThompson.Local.HallCoreInSigmaCore
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G]

theorem index_subgroupOf_eq_of_natCard_eq_mul [Finite G] {K M : Subgroup G} (hKM : K ≤ M) {n : ℕ}
    (h : Nat.card ↥M = Nat.card ↥K * n) : (K.subgroupOf M).index = n := by
  have h1 : Nat.card ↥(K.subgroupOf M) * (K.subgroupOf M).index = Nat.card ↥M :=
    Subgroup.card_mul_index _
  have h2 : Nat.card ↥(K.subgroupOf M) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
  rw [h2, h] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1

theorem notMem_of_isHallPiSubgroupOf_of_dvd_index [Finite G] {π : Set ℕ} {K M : Subgroup G}
    (hK : CFSG.FeitThompson.IsHallPiSubgroupOf π K M) {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ (K.subgroupOf M).index) : p ∉ π :=
  hK.2.notMem_of_mem_primeFactors_index p
    (Nat.mem_primeFactors.2 ⟨hp, hdvd, Subgroup.index_ne_zero_of_finite⟩)

theorem isNilpotent_sigmaCore_of_ne_bot [Fintype G]
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₃ : Statements.FTS_outside_sigma_plane_structure.{u})
    (hG : CFSG.FeitThompson.IsOddOrderMinimalSimple G)
    {M K U : Subgroup G} (hM : IsCoatom M)
    (hK : CFSG.FeitThompson.IsHallPiSubgroupOf (kappaPrimes M) K M)
    (hsd : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) (U ⊔ K))
    (hsd' : FreeCore.IsInternalSemidirectProduct (U ⊔ K) U K) (hU : U ≠ ⊥) :
    Group.IsNilpotent ↥(sigmaCore M) ∧
      CFSG.FeitThompson.hallCoreIn M = sigmaCore M ∧
      sigmaCore M ≠ ⊥ := by
  obtain ⟨p, hp, hpU⟩ := Nat.exists_prime_and_dvd (n := Nat.card ↥U)
    (fun h => hU (Subgroup.card_eq_one.1 h))
  have := Fact.mk hp
  have hcardM : Nat.card ↥M = Nat.card ↥(sigmaCore M) * Nat.card ↥(U ⊔ K) := hsd.natCard_eq_mul
  have hcardUK : Nat.card ↥(U ⊔ K) = Nat.card ↥U * Nat.card ↥K := hsd'.natCard_eq_mul
  have hpUK : p ∣ Nat.card ↥(U ⊔ K) := hpU.trans (Subgroup.card_dvd_of_le le_sup_left)
  have hpM : p ∣ Nat.card ↥M := by rw [hcardM]; exact dvd_mul_of_dvd_right hpUK _
  have hpσ : p ∉ sigmaPrimes M :=
    notMem_of_isHallPiSubgroupOf_of_dvd_index (h₁ G hG M hM).1 hp
      (by rw [index_subgroupOf_eq_of_natCard_eq_mul (sigmaCore_le M) hcardM]; exact hpUK)
  have hpκ : p ∉ kappaPrimes M := by
    refine notMem_of_isHallPiSubgroupOf_of_dvd_index hK hp ?_
    rw [index_subgroupOf_eq_of_natCard_eq_mul hK.1
      (n := Nat.card ↥(sigmaCore M) * Nat.card ↥U) (by rw [hcardM, hcardUK]; ring)]
    exact dvd_mul_of_dvd_right hpU _
  obtain ⟨S⟩ := (Sylow.nonempty : Nonempty (Sylow p ↥M))
  have hGmin : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨-, -, hnil⟩ := FNI_outside_sigma_kappa_sylow_core_nilpotent h₁ h₂ h₃ G hGmin p M
    ((S : Subgroup ↥M).map M.subtype) hM hp hpM
    (by rintro (h | h); exacts [hpσ h, hpκ h]) ⟨S, rfl⟩
  have hamb : CFSG.FeitThompson.IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  exact ⟨hnil, (FBG_normal_hall_core_sigma_containment.{u} G hamb M hM).2.2 hnil,
    (FBG_sigma_core_nontrivial h₁ G hG M hM).2⟩

theorem FBG_residual_complement_nilpotent_core
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₃ : Statements.FTS_outside_sigma_plane_structure.{u}) :
    Statements.FBG_residual_complement_nilpotent_core.{u} := by
  intro G _ _ hG M hM K U hK _ hsd hsd'
  have hmain := fun hU => isNilpotent_sigmaCore_of_ne_bot h₁ h₂ h₃ hG hM hK hsd hsd' hU
  exact ⟨hmain, fun hne => by by_contra hU; exact hne (hmain hU).2.1⟩

end

end CFSG.FeitThompson.Proofs
