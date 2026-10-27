module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Local.P34Stmt
public import CFSG.GH74.Uniqueness.SU.SU0GH
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceAssemblyElement
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
open CFSG.ComponentClassification.LBalance (SchreierSections)

section Schreier

theorem schreierSections_of_ghGroup (hSch : GHSchreier) {X : Type} [Group X] [Finite X]
    (hGH : Uniqueness.SU.SU0.GHGroup X) : SchreierSections X := by
  intro A B _ hn hsimple hnonab
  have hGHl : GHList (A ⧸ B.subgroupOf A) :=
    hGH A (A ⧸ B.subgroupOf A) (QuotientGroup.mk' (B.subgroupOf A))
      (QuotientGroup.mk'_surjective _) hsimple hnonab
  exact hSch _ hsimple hnonab hGHl

end Schreier

section Layer

variable {G : Type} [Group G]

theorem pLayerOf_eq_map_P34 (p : ℕ) (H : Subgroup G) :
    pLayerOf p H = (pLayer ↥H p).map H.subtype := by
  apply le_antisymm
  · refine sSup_le fun L hL => ?_
    obtain ⟨hLH, hL2⟩ := hL
    rw [← Subgroup.map_subgroupOf_eq_of_le hLH]
    exact Subgroup.map_mono (le_sSup hL2)
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun M hM => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_sSup ⟨?_, ?_⟩
    · rintro _ ⟨m, -, rfl⟩
      exact m.2
    · have : (M.map H.subtype).subgroupOf H = M :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective M
      rw [this]
      exact hM

end Layer


section LBal

variable {G : Type} [Group G] [Finite G]

theorem Ixz_le_Jx_of_sections {x z : G} (hsch : SchreierSections ↥(centralizer ({x} : Set G)))
    (hzN : z ∈ centralizer ({x} : Set G)) (hz2 : orderOf z = 2) : Ixz z x ≤ Jx x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz1 : z ^ 2 ^ 1 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz2] at h
  have hC : (centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G)) = centralizer ({x, z} : Set G) := by
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq]
  have hI : Ixz z x = CFSG.Open.lBalancePLayer 2 (centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G)) := by
    rw [hC, Ixz, pLayerOf_eq_map_P34, CFSG.ComponentClassification.LBalance.Asm.lBalancePLayer_eq_map]
  have hJ : Jx x = CFSG.Open.lBalancePLayer 2 (centralizer ({x} : Set G)) := by
    rw [Jx, pLayerOf_eq_map_P34, CFSG.ComponentClassification.LBalance.Asm.lBalancePLayer_eq_map]
  rw [hI, hJ]
  have hx' : ∃ n : ℕ, (⟨z, hzN⟩ : ↥(centralizer ({x} : Set G))) ^ 2 ^ n = 1 :=
    ⟨1, Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hz1)⟩
  have hCz : ((centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G)).subgroupOf (centralizer ({x} : Set G))) =
      centralizer ({(⟨z, hzN⟩ : ↥(centralizer ({x} : Set G)))} : Set ↥(centralizer ({x} : Set G))) := by
    ext y
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, SetLike.coe_mem, true_and,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [← CFSG.ComponentClassification.LBalance.pLayer_nested_map 2
      (centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G)) (centralizer ({x} : Set G)) inf_le_left, hCz,
    ← CFSG.ComponentClassification.LBalance.pLayer_nested_map 2 (centralizer ({x} : Set G))
      (centralizer ({x} : Set G)) le_rfl, Subgroup.subgroupOf_self]
  exact Subgroup.map_mono (CFSG.ComponentClassification.LBalance.lBalancePLayer_centralizer_element_le hsch hx')

end LBal


section Nonsolv

theorem not_isSolvable_of_isPComponent {X : Type} [Group X] {L : Subgroup X} (hL : IsPComponent 2 L) :
    ¬ Group.IsSolvable ↥L := by
  intro hsolv
  obtain ⟨K, ⟨hKq, -⟩, -, hmap, -⟩ := hL
  have hsurj : Function.Surjective ((QuotientGroup.mk' (pPrimeCore 2 X)).subgroupMap L) :=
    (QuotientGroup.mk' (pPrimeCore 2 X)).subgroupMap_surjective L
  have hKsolv : Group.IsSolvable ↥K := by
    subst hmap
    exact Group.isSolvable_of_surjective hsurj
  obtain ⟨-, hs, a, b, hab⟩ := hKq
  have : Group.IsSolvable (↥K ⧸ Subgroup.center ↥K) := inferInstance
  exact hab ((IsSimpleGroup.comm_iff_isSolvable.2 this) a b)

variable {G : Type} [Group G]

theorem not_isSolvable_pLayerOf {Y : Subgroup G} (h : pLayerOf 2 Y ≠ ⊥) :
    ¬ Group.IsSolvable ↥(pLayerOf 2 Y) := by
  intro hsolv
  apply h
  rw [eq_bot_iff]
  refine sSup_le fun L hL => ?_
  exfalso
  have hLle : L ≤ pLayerOf 2 Y := le_sSup hL
  have hLs : Group.IsSolvable ↥L :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLle) (Subgroup.inclusion_injective hLle)
  have : Group.IsSolvable ↥(L.subgroupOf Y) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hL.1).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hL.1).injective
  exact not_isSolvable_of_isPComponent hL.2 this

theorem Ixz_le_Cen (z x : G) : Ixz z x ≤ Cen z := by
  refine (sSup_le fun L hL => hL.1).trans (Subgroup.centralizer_le ?_)
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  subst hw
  simp

theorem not_isSolvable_J0 {z x : G} {H : Subgroup G} (hCH : Cen z ≤ H) (hIJ : Ixz z x ≤ Jx x)
    (hI : Ixz z x ≠ ⊥) : ¬ Group.IsSolvable ↥(Jx x ⊓ H) := by
  intro hsolv
  have hIle : Ixz z x ≤ Jx x ⊓ H := le_inf hIJ ((Ixz_le_Cen z x).trans hCH)
  have : Group.IsSolvable ↥(Ixz z x) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hIle) (Subgroup.inclusion_injective hIle)
  exact not_isSolvable_pLayerOf hI this

end Nonsolv

end CFSG.GH74.GLS.Stage2.Local.P34
