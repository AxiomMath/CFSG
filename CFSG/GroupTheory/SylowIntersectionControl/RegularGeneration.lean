module

public import CFSG.GroupTheory.SylowIntersectionControl.PairSelection
public import CFSG.GroupTheory.SylowIntersectionControl.Isolated

import CFSG.GroupTheory.SylowIntersectionControl.Generation
import CFSG.Quasithin.Background.C118WeakPair
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.ABGLocalTools CFSG.Quasithin
open scoped Pointwise

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

namespace PSubgroupSelection

variable {G : Type*} [Group G] {p : ℕ} (f : PSubgroupSelection p G)

theorem eq_iSup_inf_normalizer_of_isRegular [Finite G] [Fact p.Prime] {M T : Subgroup G}
    (hreg : f.IsRegular M) (hM : ¬ IsPIsolatedOver p M ⊥) (hT : IsSylowOf p T M)
    (hne : (f.sets T).Nonempty) :
    M = ⨆ F ∈ f.sets T, M ⊓ normalizer (F : Set G) := by
  let X : Subgroup G := ⨆ F ∈ f.sets T, M ⊓ normalizer (F : Set G)
  have hmul := ControlsSylowIntersections.mul_normalizer_eq
    (f.isNormalSetIn_family M) hreg hM hT
  have hsup : (⨆ Y ∈ sylowMembers p (f.family M) T, Y) = X := by
    rw [sylowMembers_family (f := f) hT, iSup_image]
  rw [hsup] at hmul
  have hX : M ⊓ normalizer (T : Set G) ≤ X := by
    obtain ⟨F₀, hF₀⟩ := hne
    refine le_iSup₂_of_le F₀ hF₀ ?_
    exact le_inf inf_le_left
      (inf_le_right.trans (f.normalizer_le T hT.isPGroup F₀ hF₀))
  change M = X
  refine le_antisymm ?_ ?_
  · intro m hm
    have hmem : m ∈ (X : Set G) *
        ((M ⊓ normalizer (T : Set G) : Subgroup G) : Set G) := by
      rw [hmul]
      exact hm
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hmem
    exact X.mul_mem ha (hX hb)
  · dsimp only [X]
    exact iSup₂_le fun F _ => inf_le_left

end PSubgroupSelection

namespace GNPairChoice

variable {G : Type*} [Group G] [Finite G] (c : GNPairChoice G)

theorem eq_iSup_inf_normalizer_of_isRegular {M T : Subgroup G}
    (hreg : c.selection.IsRegular M) (hM : ¬ IsPIsolatedOver 2 M ⊥)
    (hT : IsSylowOf 2 T M) :
    M = ⨆ F ∈ c.selection.sets T, M ⊓ normalizer (F : Set G) := by
  refine PSubgroupSelection.eq_iSup_inf_normalizer_of_isRegular (f := c.selection)
    hreg hM hT ⟨c.C₁ T, ?_⟩
  simp [GNPairChoice.selection]

private theorem inf_normalizer_omegaOneCenterOf_le {M G₀ T S : Subgroup G}
    (hMG : M ≤ G₀) (hT : IsSylowOf 2 T M) (hTS : T ≤ S) (hS : IsPGroup 2 S)
    (hK : baum S ≤ T) :
    M ⊓ normalizer (omegaOneCenterOf T : Set G) ≤
      ⨆ F ∈ c.selection.sets S, G₀ ⊓ normalizer (F : Set G) := by
  have hBS : omegaOneCenterOf S ≤ omegaOneCenterOf T :=
    omegaOneCenterOf_le_omegaOneCenterOf_of_baum_le (S := T) (T := S) hK hTS
  have hcent : centerOf T ≤ Subgroup.centralizer (T : Set G) := by
    simp only [centerOf]
    exact inf_le_right
  have hTC : T ≤ M ⊓ Subgroup.centralizer (omegaOneCenterOf T : Set G) := by
    refine le_inf hT.le ?_
    exact Subgroup.le_centralizer_iff.mpr
      ((C1GN.omegaOneCenterOf_le_centerOf T).trans hcent)
  let C : Subgroup G := M ⊓ Subgroup.centralizer (omegaOneCenterOf T : Set G)
  let K : Subgroup G := M ⊓ Subgroup.normalizer (omegaOneCenterOf T : Set G)
  have hCK : C ≤ K := by
    refine le_inf inf_le_left ?_
    exact (inf_le_right : C ≤ Subgroup.centralizer (omegaOneCenterOf T : Set G)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hKN : K ≤ Subgroup.normalizer (C : Set G) := by
    refine (le_inf ?_ ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
    · exact (inf_le_left : K ≤ M).trans Subgroup.le_normalizer
    · exact (inf_le_right : K ≤ Subgroup.normalizer (omegaOneCenterOf T : Set G)).trans
        (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup _)
  have hTCsyl : IsSylowOf 2 T C := hT.of_le hTC inf_le_left
  have hTCsyl2 : CFSG.QuasithinUnique.IsSylowTwoOf T C := by
    obtain ⟨hle, hpg, hidx⟩ := (isSylowOf_iff (p := 2) (P := T) (K := C)).mp hTCsyl
    exact ⟨hle, hpg, hidx⟩
  have hfrac : K ≤ C ⊔ (K ⊓ Subgroup.normalizer (T : Set G)) :=
    CFSG.Quasithin.B6.frattini_two hCK hKN hTCsyl2
  have hCX : C ≤ ⨆ F ∈ c.selection.sets S, G₀ ⊓ normalizer (F : Set G) := by
    refine le_iSup₂_of_le (omegaOneCenterOf S) ?_ ?_
    · simp [GNPairChoice.selection]
    · refine le_inf (inf_le_left.trans hMG) ?_
      exact ((inf_le_right : C ≤ Subgroup.centralizer (omegaOneCenterOf T : Set G)).trans
        (Subgroup.centralizer_le hBS)).trans (Subgroup.centralizer_le_normalizer _)
  have hKTX : K ⊓ Subgroup.normalizer (T : Set G) ≤
      ⨆ F ∈ c.selection.sets S, G₀ ⊓ normalizer (F : Set G) := by
    refine le_iSup₂_of_le (c.C₁ S) ?_ ?_
    · simp [GNPairChoice.selection]
    · refine le_inf ((inf_le_left.trans inf_le_left).trans hMG) ?_
      exact (inf_le_right : K ⊓ Subgroup.normalizer (T : Set G) ≤
          Subgroup.normalizer (T : Set G)).trans
        ((normalizer_le_normalizer_baum T).trans (by
          rw [(baum_eq_of_le hK hTS).symm]
          exact c.normalizer_baum_le_normalizer_C₁ hS))
  exact hfrac.trans (sup_le hCX hKTX)

theorem iSup_inf_normalizer_le_of_baum_le {M G₀ T S : Subgroup G} (hMG : M ≤ G₀)
    (hT : IsSylowOf 2 T M) (hTS : T ≤ S) (hS : IsPGroup 2 S) (hK : baum S ≤ T) :
    ⨆ F ∈ c.selection.sets T, M ⊓ normalizer (F : Set G) ≤
      ⨆ F ∈ c.selection.sets S, G₀ ⊓ normalizer (F : Set G) := by
  have hbaum : baum T = baum S := (baum_eq_of_le hK hTS).symm
  have hC₁ : c.C₁ T = c.C₁ S := by
    rw [GNPairChoice.C₁, GNPairChoice.C₁, hbaum]
  have hC₂ : c.C₂ T = c.C₂ S := by
    rw [GNPairChoice.C₂, GNPairChoice.C₂, hbaum]
  refine iSup₂_le fun F hF => ?_
  simp only [GNPairChoice.selection, Set.mem_insert_iff, Set.mem_singleton_iff] at hF
  rcases hF with rfl | rfl | rfl
  · refine le_iSup₂_of_le (c.C₁ S) ?_ ?_
    · simp [GNPairChoice.selection]
    · exact le_inf (inf_le_left.trans hMG)
        (inf_le_right.trans (le_of_eq (congrArg
          (fun H : Subgroup G => normalizer (H : Set G)) hC₁)))
  · refine le_iSup₂_of_le (c.C₂ S) ?_ ?_
    · simp [GNPairChoice.selection]
    · exact le_inf (inf_le_left.trans hMG)
        (inf_le_right.trans (le_of_eq (congrArg
          (fun H : Subgroup G => normalizer (H : Set G)) hC₂)))
  · exact inf_normalizer_omegaOneCenterOf_le (c := c) hMG hT hTS hS hK

end GNPairChoice

end CFSG.GroupTheory

end
