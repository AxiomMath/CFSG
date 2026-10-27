module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
import CFSG.FeitThompson.Local.AlphaCoreNormalHall
import CFSG.FeitThompson.Local.PrimeFreeFactorizationFixedSubgroupTransport
import CFSG.FeitThompson.Local.SigmaHallInDerivedSubgroup
import CFSG.FeitThompson.Local.NilpotentHallCharacteristic
import CFSG.FeitThompson.Foundations.SolvableHallExistence
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup

universe u

theorem isHallSubgroup_piCore_of_forall_le_commutator {L : Type*} [Group L] [Finite L]
    [Group.IsSolvable L] {π : Set ℕ} (hodd : Odd (Nat.card L)) (hπ : alphaPrimes L ⊆ π)
    (hcomm : ∀ T : Subgroup L, IsHallSubgroup π T → T ≤ _root_.commutator L) :
    IsHallSubgroup π (piCore π L) := by
  have := alphaCore_normal L
  obtain ⟨T, hT⟩ := exists_isHallSubgroup (X := L) π
  have hAT : alphaCore L ≤ T := hT.le_of_isPiSubgroup ((isPiSubgroup_alphaCore L).mono hπ)
  have hmapT : IsHallSubgroup π (T.map (QuotientGroup.mk' (alphaCore L))) := by
    have h := hT.map_sup_mk' (alphaCore L)
    rwa [sup_eq_left.2 hAT] at h
  have hTF : T.map (QuotientGroup.mk' (alphaCore L)) ≤ fittingRaw (L ⧸ alphaCore L) :=
    le_trans (Subgroup.map_mono (hcomm T hT))
      (map_mk'_commutator_le_fittingRaw_quotient_alphaCore hodd)
  have : (fittingRaw (L ⧸ alphaCore L)).Normal := fittingRaw_normal _
  have : ((T.map (QuotientGroup.mk' (alphaCore L))).subgroupOf
      (fittingRaw (L ⧸ alphaCore L))).Characteristic := (hmapT.subgroupOf hTF).characteristic
  have hnorm : (T.map (QuotientGroup.mk' (alphaCore L))).Normal :=
    normal_of_characteristic_subgroupOf_of_normal hTF
  have : T.Normal := by
    have h : Subgroup.comap (QuotientGroup.mk' (alphaCore L))
        (T.map (QuotientGroup.mk' (alphaCore L))) = T :=
      Subgroup.comap_map_eq_self (by rwa [QuotientGroup.ker_mk'])
    exact h ▸ hnorm.comap _
  have hTpi : T = piCore π L := le_antisymm (le_piCore ‹T.Normal› hT.isPiSubgroup) hT.piCore_le
  exact hTpi ▸ hT

variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem isHallSubgroup_subgroupOf_sigmaCore [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    (hM : IsCoatom M) : IsHallSubgroup (sigmaPrimes M) ((sigmaCore M).subgroupOf M) := by
  have := hsolv M hM.1
  rw [subgroupOf_sigmaCore]
  exact isHallSubgroup_piCore_of_forall_le_commutator
    (hodd.of_dvd_nat M.card_subgroup_dvd_card)
    (alphaPrimes_subset_sigmaPrimes hna hodd hsolv hM)
    fun _ hT => le_commutator_of_isHallSubgroup_sigmaPrimes hna hodd hsolv hM hT

theorem isHallSubgroup_sigmaCore [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    (hM : IsCoatom M) : IsHallSubgroup (sigmaPrimes M) (sigmaCore M) where
  natCard := isPiSubgroup_iff_isPiNumber.1 (isPiSubgroup_sigmaCore M)
  index := by
    have h : sigmaCore M = ((sigmaCore M).subgroupOf M).map M.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le M)).symm
    rw [h, Subgroup.index_map_subtype]
    exact (isHallSubgroup_subgroupOf_sigmaCore hna hodd hsolv hM).index.mul
      (isPiNumber_compl_iff.2 fun _ hq hq' =>
        not_dvd_index_of_mem_sigmaPrimes hq' (Nat.dvd_of_mem_primeFactors hq))

theorem sigmaCore_le_commutator [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    (hM : IsCoatom M) : sigmaCore M ≤ ⁅M, M⁆ :=
  le_commutator_of_isHallSubgroup_sigmaPrimes_subgroupOf hna hodd hsolv hM (sigmaCore_le M)
    (isHallSubgroup_subgroupOf_sigmaCore hna hodd hsolv hM)

theorem FBG_sigma_core_normal_hall : Statements.FBG_sigma_core_normal_hall.{u} := by
  intro G _ _ hG M hM
  have := hG.isSimpleGroup
  refine ⟨⟨sigmaCore_le M, ?_⟩, ?_, ?_⟩
  · exact (isHallSubgroup_subgroupOf_sigmaCore hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hM).isHallPiSubgroup
  · exact (isHallSubgroup_sigmaCore hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hM).isHallPiSubgroup
  · exact sigmaCore_le_commutator hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hM

end

end CFSG.FeitThompson.Proofs
