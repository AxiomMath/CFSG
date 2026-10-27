module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXPkLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXPkMap

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

theorem t5_isI4PlusIn_iff (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ} (h : IsCoverMap L φ)
    {w : G} (hw : w ∈ L) (hw2 : orderOf w = 2) :
    IsI4PlusIn L w ↔ IsI4PlusIn (⊤ : Subgroup ↥(omegaGroup hQ)) (φ ⟨w, hw⟩) := by
  classical
  haveI : Finite V := Module.finite_of_finite (ZMod 3)
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun e₁ e₂ he => LinearEquiv.ext (congrFun he))
  haveI : Finite (OGroup Q) :=
    Finite.of_injective (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V)) Subtype.val_injective
  constructor
  · intro hwI
    have htop : IsI4PlusIn (⊤ : Subgroup ↥L) (⟨w, hw⟩ : ↥L) := by
      have h' := l34g_x_isI4PlusIn_subgroupOf (H := L) (V := L) (y := w) (le_refl L) hw hwI
      rwa [Subgroup.subgroupOf_self] at h'
    have hmap := l34g_x_isI4PlusIn_map (h.oddCentralCover hL) (V := ⊤) htop
    rwa [Subgroup.map_top_of_surjective φ h.surjective] at hmap
  · intro hP
    have hww : w * w = 1 := by
      rw [← pow_two]
      exact hw2 ▸ pow_orderOf_eq_one w
    have haa : (⟨w, hw⟩ : ↥L) * ⟨w, hw⟩ = 1 := Subtype.ext hww
    have htop : IsI4PlusIn (⊤ : Subgroup ↥L) (⟨w, hw⟩ : ↥L) :=
      l34g_x_isI4PlusIn_top_of_cover (A := ↥L) (P := ↥(omegaGroup hQ))
        (h.oddCentralCover hL) haa hP
    have htop' : IsI4PlusIn (⊤ : Subgroup ↥(⊤ : Subgroup ↥L))
        (⟨⟨w, hw⟩, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup ↥L)) := by
      have h' := l34g_x_isI4PlusIn_subgroupOf (H := (⊤ : Subgroup ↥L))
        (V := (⊤ : Subgroup ↥L)) (y := (⟨w, hw⟩ : ↥L)) (le_refl _) (Subgroup.mem_top _) htop
      rwa [Subgroup.subgroupOf_self] at h'
    have hmap := l34g_x_isI4PlusIn_map_inj (X := ↥L) L.subtype L.subtype_injective
      (J₀ := (⊤ : Subgroup ↥L)) (Subgroup.mem_top _) htop'
    rwa [Subgroup.map_top, Subgroup.range_subtype] at hmap

end CFSG.OddStandard.SmallF3.Omega
