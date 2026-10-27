module

public import CFSG.LocalAnalysis.ComponentInitial.InvolutionComponentTwoCore
public import CFSG.LocalAnalysis.ComponentInitial.FixedLayerNormalizes
public import CFSG.LocalAnalysis.ComponentInitial.PerfectNormalizerLayer

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification OuterAutomorphisms

variable {H : Type*} [Group H] [Finite H]

theorem fittingSubgroup_le_pCore_of_pPrimeCore_eq_bot {p : ℕ} [Fact p.Prime]
    (hcore : CFSG.pPrimeCore p H = ⊥) : CFSG.fittingSubgroup H ≤ CFSG.pCore p H :=
  le_sSup ⟨inferInstance, CFSG.isPGroup_of_nilpotent_normal _ inferInstance inferInstance hcore⟩

theorem odd_core_free_Schreier_involution_component_enters_layer
    (hcore : CFSG.pPrimeCore 2 H = ⊥) {t : H} (ht : orderOf t = 2)
    (hout : ∀ K : Subgroup H, CFSG.IsComponent K → Group.IsSolvable (Outer (K ⧸ center K)))
    (L : Subgroup (centralizer ({t} : Set H))) (hL : CFSG.IsComponent L) :
    L.map (centralizer ({t} : Set H)).subtype ≤ CFSG.layer H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLp : Group.IsPerfect L := hL.1.1
  have hA : Group.IsPerfect (L.map (centralizer ({t} : Set H)).subtype) :=
    Group.IsPerfect.map (centralizer ({t} : Set H)).subtype
  have hAF : ⁅L.map (centralizer ({t} : Set H)).subtype, CFSG.fittingSubgroup H⁆ = ⊥ :=
    le_bot_iff.1 ((Subgroup.commutator_mono le_rfl
      (fittingSubgroup_le_pCore_of_pPrimeCore_eq_bot hcore)).trans
        (involution_component_centralizes_two_core ht L hL).le)
  have hAt : L.map (centralizer ({t} : Set H)).subtype ≤ centralizer ({t} : Set H) :=
    Subgroup.map_subtype_le L
  have hEn : (CFSG.layer H).Normal := by
    have := CFSG.LocalCores.layer_characteristic (G := H)
    infer_instance
  have hN : ((CFSG.layer H).subgroupOf (centralizer ({t} : Set H))).Normal :=
    Subgroup.normal_subgroupOf
  rcases CFSG.LocalCores.component_normal_subgroup hL hN with hle | hcomm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    exact hle hy
  · have hAE : ⁅L.map (centralizer ({t} : Set H)).subtype,
        CFSG.layer H ⊓ centralizer ({t} : Set H)⁆ = ⊥ := by
      have h := congrArg (Subgroup.map (centralizer ({t} : Set H)).subtype) hcomm
      rwa [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.map_bot] at h
    exact unique_perfect_component_normalizer_enters_layer hA hAF
      (perfect_involution_fixed_layer_centralizer_normalizes_components ht hAt hA hAF hAE) hout

end CFSG.LocalAnalysis.ComponentInitial
