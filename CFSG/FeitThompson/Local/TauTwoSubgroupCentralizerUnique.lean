module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.AbelianHallTauTwoControlsCentralizers
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived
import CFSG.FeitThompson.Local.QuotientFittingInvariantComplement
import CFSG.FeitThompson.Local.PrimeFreeFactorizationFixedSubgroupTransport

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson

universe u

theorem centralizer_le_and_isUniqueMaximalOvergroup_of_forall_mem_tauTwoPrimes
    (h₁ : Statements.FBG_tau_two_hall_abelian.{u})
    (h₂ : Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    {G : Type u} [Group G] [Finite G] (hG : CFSG.FeitThompson.IsOddSimpleMinimal G)
    {M X : Subgroup G} (hM : IsCoatom M) (hXM : X ≤ M) (hX : X ≠ ⊥)
    (hXτ : ∀ s ∈ (Nat.card ↥X).primeFactors, s ∈ tauTwoPrimes M)
    (hcent : sigmaCore M ⊓ centralizer (X : Set G) ≠ ⊥) :
    centralizer (X : Set G) ≤ M ∧ IsUniqueMaximalOvergroup (centralizer (X : Set G)) M := by
  have := hG.isSimpleGroup
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hM.1
  have hXσ : IsPiSubgroup (sigmaPrimes M)ᶜ (X.subgroupOf M) := by
    refine isPiSubgroup_iff.2 fun p hp => ?_
    rw [natCard_subgroupOf_of_le hXM] at hp
    exact notMem_sigmaPrimes_of_mem_tauTwoPrimes (hXτ p hp)
  obtain ⟨E', hE', hXE'⟩ := exists_isHallSubgroup_ge_of_isPiSubgroup hXσ
  set E : Subgroup G := E'.map M.subtype with hEdef
  have hEM : E ≤ M := map_subtype_le _
  have hEsub : E.subgroupOf M = E' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective E'
  have hXE : X ≤ E := by
    rw [hEdef, ← Subgroup.map_subgroupOf_eq_of_le hXM]; exact Subgroup.map_mono hXE'
  obtain ⟨hsup, hinf⟩ := sup_eq_and_inf_eq_bot_of_isHallSubgroup_compl (π := sigmaPrimes M)
    (sigmaCore_le M) hEM
    (isHallSubgroup_subgroupOf_sigmaCore hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hM)
    (hEsub ▸ hE') (hEM.trans (le_normalizer_sigmaCore M))
  have hEtop : E ≠ ⊤ := fun h => hM.1 (top_le_iff.1 (h ▸ hEM))
  have hEsolv : Group.IsSolvable ↥E := hG.isSolvable_of_ne_top E hEtop
  have hXτ' : IsPiSubgroup (tauTwoPrimes M) (X.subgroupOf E) := by
    refine isPiSubgroup_iff.2 fun p hp => ?_
    rw [natCard_subgroupOf_of_le hXE] at hp
    exact hXτ p hp
  obtain ⟨E₂', hE₂', hXE₂'⟩ := exists_isHallSubgroup_ge_of_isPiSubgroup hXτ'
  set E₂ : Subgroup G := E₂'.map E.subtype with hE₂def
  have hE₂E : E₂ ≤ E := map_subtype_le _
  have hE₂sub : E₂.subgroupOf E = E₂' :=
    Subgroup.comap_map_eq_self_of_injective E.subtype_injective E₂'
  have hXE₂ : X ≤ E₂ := by
    rw [hE₂def, ← Subgroup.map_subgroupOf_eq_of_le hXE]; exact Subgroup.map_mono hXE₂'
  have hE₂card : Nat.card ↥E₂ = Nat.card ↥E₂' := by
    rw [hE₂def]; exact Subgroup.card_subtype E E₂'
  have hE₂hall : CFSG.FeitThompson.Prep06.IsHallPiIn (tauTwoPrimes M) E₂ E := by
    refine ⟨hE₂E, fun p hp => ?_, fun p hp => ?_⟩
    · exact isPiSubgroup_iff.1 hE₂'.isPiSubgroup p (hE₂card ▸ hp)
    · have hrel : E₂.relIndex E = E₂'.index := by rw [Subgroup.relIndex, hE₂sub]
      exact isPiNumber_iff.1 hE₂'.index p (hrel ▸ hp)
  have hE₂ab : IsMulCommutative ↥E₂ := by
    let _inst : Fintype G := Fintype.ofFinite G
    exact h₁ G ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative,
      hG.isSolvable_of_ne_top⟩ M hM E ⟨hsup, le_normalizer_sigmaCore M,
      disjoint_iff.2 hinf⟩ E₂ ⟨hE₂E, hE₂sub ▸ hE₂'.isHallPiSubgroup⟩
  exact centralizer_le_and_isUniqueMaximalOvergroup_of_le_hall_tauTwo h₂ hG hM hEM hsup hinf
    hE₂E hE₂ab hE₂hall hXE₂ hX hcent

theorem FTS_tau_two_subgroup_centralizer_unique
    (h₁ : Statements.FBG_tau_two_hall_abelian.{u})
    (h₂ : Statements.FNI_outside_sigma_plane_core_disjoint.{u}) :
    Statements.FTS_tau_two_subgroup_centralizer_unique.{u} := by
  intro G _ _ hG M hM X hXM hX hXτ hcent
  exact centralizer_le_and_isUniqueMaximalOvergroup_of_forall_mem_tauTwoPrimes h₁ h₂
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
    hM hXM hX hXτ hcent

end

end CFSG.FeitThompson.Proofs
