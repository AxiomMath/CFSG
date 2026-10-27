module

public import CFSG.FeitThompson.Definitions.PuigSubgroupIteration
public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Sylow
import CFSG.FeitThompson.Local.PuigSylowPrimeCoreInterlace
import CFSG.FeitThompson.Local.PuigLimitsStationaryExchange
import CFSG.FeitThompson.Local.PuigTermsContainAbelianNormal
import CFSG.FeitThompson.Local.PuigSubgroupSameOnContainingSubgroup
import CFSG.FeitThompson.Local.PuigSeriesIsomorphismInvariance
import CFSG.FeitThompson.Local.PuigLambdaAbelianGeneratedPrimeCore

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {p : ℕ}

theorem subtype_comp_subgroupOfEquivOfLe {H K : Subgroup G} (hHK : H ≤ K) :
    H.subtype.comp (subgroupOfEquivOfLe hHK).toMonoidHom
      = K.subtype.comp (H.subgroupOf K).subtype := by
  ext x
  simp [subgroupOfEquivOfLe_apply_coe]

theorem map_puigSubgroup_subgroupOf {H K : Subgroup G} (hHK : H ≤ K) :
    ((puigSubgroup (H.subgroupOf K)).map (H.subgroupOf K).subtype).map K.subtype
      = (puigSubgroup H).map H.subtype := by
  rw [map_map, ← subtype_comp_subgroupOfEquivOfLe hHK, ← map_map,
    puigSubgroup_map (subgroupOfEquivOfLe hHK)]

theorem map_puigSubgroup_eq_of_map_puigSubgroup_le [Finite G] {H K : Subgroup G} (hHK : H ≤ K)
    (hL : (puigSubgroup K).map K.subtype ≤ H) :
    (puigSubgroup H).map H.subtype = (puigSubgroup K).map K.subtype := by
  have hL' : puigSubgroup K ≤ H.subgroupOf K := by
    rw [subgroupOf, ← map_le_iff_le_comap]; exact hL
  rw [← map_puigSubgroup_subgroupOf hHK, map_puigSubgroup_eq_puigSubgroup (X := K) hL']

def puigCenterPCore (p : ℕ) (G : Type*) [Group G] [Finite G] : Subgroup G :=
  (puigCenter (pCore p G)).map (pCore p G).subtype

theorem puigCenterPCore_eq (p : ℕ) (G : Type*) [Group G] [Finite G] :
    puigCenterPCore p G = (puigCenter (pCore p G)).map (pCore p G).subtype := (rfl)

instance puigCenterPCore_normal (p : ℕ) (G : Type*) [Group G] [Finite G] :
    (puigCenterPCore p G).Normal := by
  have : (pCore p G).Normal := pCore_normal p G
  rw [puigCenterPCore_eq]
  exact ConjAct.normal_of_characteristic_of_normal

instance puigCenterPCore_isMulCommutative (p : ℕ) (G : Type*) [Group G] [Finite G] :
    IsMulCommutative (puigCenterPCore p G) := by
  rw [puigCenterPCore_eq]; infer_instance

theorem puigCenterPCore_le_pCore (p : ℕ) (G : Type*) [Group G] [Finite G] :
    puigCenterPCore p G ≤ pCore p G := by
  rw [puigCenterPCore_eq]; exact map_subtype_le _

theorem isPGroup_puigCenterPCore (hp : p.Prime) (G : Type*) [Group G] [Finite G] :
    IsPGroup p (puigCenterPCore p G) :=
  (isPGroup_pCore hp G).to_le (puigCenterPCore_le_pCore p G)

theorem puigCenterPCore_le_sylow [Finite G] (hp : p.Prime) (S : Sylow p G) :
    puigCenterPCore p G ≤ (S : Subgroup G) :=
  (puigCenterPCore_le_pCore p G).trans (pCore_le_sylow hp S)

def puigCentralizerContainer (p : ℕ) (G : Type*) [Group G] [Finite G] : Subgroup G :=
  (pCore p (G ⧸ centralizer (puigCenterPCore p G : Set G))).comap
    (QuotientGroup.mk' (centralizer (puigCenterPCore p G : Set G)))

theorem puigCentralizerContainer_eq (p : ℕ) (G : Type*) [Group G] [Finite G] :
    puigCentralizerContainer p G =
      (pCore p (G ⧸ centralizer (puigCenterPCore p G : Set G))).comap
        (QuotientGroup.mk' (centralizer (puigCenterPCore p G : Set G))) := (rfl)

theorem mem_puigCentralizerContainer_iff [Finite G] {x : G} :
    x ∈ puigCentralizerContainer p G ↔
      QuotientGroup.mk' (centralizer (puigCenterPCore p G : Set G)) x
        ∈ pCore p (G ⧸ centralizer (puigCenterPCore p G : Set G)) := (Iff.rfl)

instance puigCentralizerContainer_normal (p : ℕ) (G : Type*) [Group G] [Finite G] :
    (puigCentralizerContainer p G).Normal := by
  rw [puigCentralizerContainer_eq]
  exact (pCore_normal _ _).comap _

theorem centralizer_puigCenterPCore_le_puigCentralizerContainer (p : ℕ) (G : Type*) [Group G]
    [Finite G] : centralizer (puigCenterPCore p G : Set G) ≤ puigCentralizerContainer p G := by
  intro x hx
  have h : QuotientGroup.mk' (centralizer (puigCenterPCore p G : Set G)) x = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hx
  simp [mem_puigCentralizerContainer_iff, h]

theorem puigCenterPCore_le_map_puigLower [Finite G] (hp : p.Prime) (S : Sylow p G) :
    puigCenterPCore p G ≤ (puigLower (S : Subgroup G)).map (S : Subgroup G).subtype := by
  have hcomm : IsMulCommutative ((puigCenterPCore p G).subgroupOf (S : Subgroup G)) :=
    comap_injective_isMulCommutative (H := puigCenterPCore p G)
      (Subgroup.subtype_injective (S : Subgroup G))
  have hnorm : ((puigCenterPCore p G).subgroupOf (S : Subgroup G)).Normal :=
    (puigCenterPCore_normal p G).subgroupOf _
  calc puigCenterPCore p G
      = ((puigCenterPCore p G).subgroupOf (S : Subgroup G)).map (S : Subgroup G).subtype :=
        (map_subgroupOf_eq_of_le (puigCenterPCore_le_sylow hp S)).symm
    _ ≤ _ := map_mono (le_puigLower_of_normal (X := (S : Subgroup G)) hcomm)

theorem puigCenterPCore_le_map_puigSubgroup_sylow [Finite G] [Group.IsSolvable G] (hp : p.Prime)
    (hGodd : Odd (Nat.card G)) (hp' : pComplCore p G = ⊥) (S : Sylow p G) :
    puigCenterPCore p G ≤ (puigSubgroup (S : Subgroup G)).map (S : Subgroup G).subtype :=
  calc puigCenterPCore p G ≤ (puigSubgroup (pCore p G)).map (pCore p G).subtype :=
        map_mono puigCenter_le_puigSubgroup
    _ ≤ _ := map_puigSubgroup_pCore_le_map_puigSubgroup hp hGodd hp' rfl S.isPGroup'
        (pCore_le_sylow hp S)

theorem map_puigSubgroup_sylow_le_puigCentralizerContainer [Finite G] [Group.IsSolvable G]
    (hp : p.Prime) (hGodd : Odd (Nat.card G)) (S : Sylow p G) :
    (puigSubgroup (S : Subgroup G)).map (S : Subgroup G).subtype
      ≤ puigCentralizerContainer p G := by
  set Sg : Subgroup G := (S : Subgroup G) with hSg
  set Y : Subgroup G := puigCenterPCore p G with hY
  have hYlow : Y ≤ (puigLower Sg).map Sg.subtype := puigCenterPCore_le_map_puigLower hp S
  have hX : (puigSubgroup Sg).map Sg.subtype ≤
      sSup ((fun B : Subgroup Sg => B.map Sg.subtype) ''
        {B : Subgroup Sg | IsMulCommutative B ∧ puigLower Sg ≤ normalizer (B : Set Sg)}) := by
    rw [puigSubgroup_eq_puigUpper, ← puigLambda_puigLower, map_le_iff_le_comap]
    refine puigLambda_le fun B hB hW => ?_
    rw [← map_le_iff_le_comap]
    exact le_sSup ⟨B, ⟨hB, hW⟩, rfl⟩
  have hnormY : ∀ B : Subgroup Sg, puigLower Sg ≤ normalizer (B : Set Sg) →
      Y ≤ normalizer ((B.map Sg.subtype : Subgroup G) : Set G) := fun B hB =>
    hYlow.trans ((map_mono hB).trans (le_normalizer_map Sg.subtype))
  rw [puigCentralizerContainer_eq, ← map_le_iff_le_comap]
  refine map_mk'_centralizer_le_pCore_of_le_sSup hp hGodd
    (P := Y) (isPGroup_puigCenterPCore hp G) ?_ ?_ ?_ hX
  · rintro A ⟨B, ⟨hB, -⟩, rfl⟩
    have := hB
    exact map_isMulCommutative _ _
  · rintro A ⟨B, -, rfl⟩
    exact S.isPGroup'.to_le (map_subtype_le _)
  · rintro A ⟨B, ⟨-, hW⟩, rfl⟩
    exact hnormY B hW

theorem map_puigSubgroup_sylow_le_inf [Finite G] [Group.IsSolvable G] (hp : p.Prime)
    (hGodd : Odd (Nat.card G)) (S : Sylow p G) :
    (puigSubgroup (S : Subgroup G)).map (S : Subgroup G).subtype
      ≤ puigCentralizerContainer p G ⊓ (S : Subgroup G) :=
  le_inf (map_puigSubgroup_sylow_le_puigCentralizerContainer hp hGodd S) (map_subtype_le _)

theorem map_puigSubgroup_inf_sylow [Finite G] [Group.IsSolvable G] (hp : p.Prime)
    (hGodd : Odd (Nat.card G)) (S : Sylow p G) :
    (puigSubgroup ↥(puigCentralizerContainer p G ⊓ (S : Subgroup G))).map
        (puigCentralizerContainer p G ⊓ (S : Subgroup G)).subtype
      = (puigSubgroup (S : Subgroup G)).map (S : Subgroup G).subtype :=
  map_puigSubgroup_eq_of_map_puigSubgroup_le inf_le_right
    (map_puigSubgroup_sylow_le_inf hp hGodd S)

theorem puig_centralizer_quotient_container [Finite G] [Group.IsSolvable G] (hp : p.Prime)
    (_hpodd : Odd p) (hGodd : Odd (Nat.card G)) (_hp' : pComplCore p G = ⊥) (S : Sylow p G) :
    (puigCentralizerContainer p G).Normal ∧
      (puigSubgroup (S : Subgroup G)).map (S : Subgroup G).subtype
          ≤ puigCentralizerContainer p G ⊓ (S : Subgroup G) ∧
        (puigSubgroup ↥(puigCentralizerContainer p G ⊓ (S : Subgroup G))).map
            (puigCentralizerContainer p G ⊓ (S : Subgroup G)).subtype
          = (puigSubgroup (S : Subgroup G)).map (S : Subgroup G).subtype :=
  ⟨inferInstance, map_puigSubgroup_sylow_le_inf hp hGodd S, map_puigSubgroup_inf_sylow hp hGodd S⟩

end

end CFSG.FeitThompson
