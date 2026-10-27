module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Fitting
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Dichotomy

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.SolomonRed

variable {G : Type*} [Group G] {B : Type*} [Group B] {t : G} {B₀ : Subgroup B}
  {ψ : ↥(centralizer ({t} : Set G)) →* Multiplicative (ZMod 2) × B}

theorem ModData.ker_eq_bot_of_central [Finite G] (h : ModData t B₀ ψ) (hO : fusionOddCore G = ⊥)
    (htc : t ∈ Subgroup.center G) : ψ.ker = ⊥ := by
  let C := centralizer ({t} : Set G)
  have hmemC : ∀ g : G, g ∈ C := fun g =>
    mem_centralizer_singleton_iff.2 (Subgroup.mem_center_iff.1 htc g)
  let N : Subgroup G := ψ.ker.map C.subtype
  have hNnormal : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_map] at hn ⊢
    obtain ⟨x, hx, hxn⟩ := hn
    refine ⟨⟨g, hmemC g⟩ * x * ⟨g, hmemC g⟩⁻¹, ?_, ?_⟩
    · exact (MonoidHom.normal_ker ψ).conj_mem x hx ⟨g, hmemC g⟩
    · rw [map_mul, map_mul, map_inv, hxn]
      rfl
  have hNodd : Odd (Nat.card N) := by
    change Odd (Nat.card (ψ.ker.map C.subtype))
    rw [Subgroup.card_map_of_injective (f := C.subtype) C.subtype_injective]
    exact h.odd
  have hle : N ≤ fusionOddCore G := le_sSup ⟨hNnormal, hNodd⟩
  rw [hO] at hle
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxN : (x : G) ∈ N := ⟨x, hx, rfl⟩
  have h1 : (x : G) ∈ (⊥ : Subgroup G) := hle hxN
  rw [Subgroup.mem_bot] at h1
  exact Subtype.ext h1

theorem lemmaRMod [Finite G] (h : ModData t B₀ ψ) (hO : fusionOddCore G = ⊥) :
    t ∈ Subgroup.center G ∨ (∃ S₁ S₂ : Subgroup G, ModSwapData G t B₀ S₁ S₂) ∨
      ∃ S : Subgroup G, FixedData G S ∧ B₀ ≤ imgOf ψ (S ⊓ centralizer ({t} : Set G)) := by
  rcases fittingSubgroup_eq_bot_or_center h hO with hF | htc
  · rcases dichotomy_mod h hF with ⟨S, hS, hle⟩ | ⟨S₁, S₂, hs⟩
    · exact Or.inr (Or.inr ⟨S, hS, hle⟩)
    · exact Or.inr (Or.inl ⟨S₁, S₂, hs⟩)
  · exact Or.inl htc

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
