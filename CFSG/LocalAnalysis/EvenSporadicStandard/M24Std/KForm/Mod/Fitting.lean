module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Setting
public import CFSG.Open.FusionDefs
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup CFSG.Open

variable {G : Type*} [Group G] {B : Type*} [Group B] {t : G} {B₀ : Subgroup B}
  {ψ : ↥(centralizer ({t} : Set G)) →* Multiplicative (ZMod 2) × B}

theorem fixed_mem_zpowers_of_normal_two [Finite G] (h : ModData t B₀ ψ) {W : Subgroup G}
    [W.Normal] (hW : IsPGroup 2 W) : ∀ w ∈ W, t * w = w * t → w ∈ zpowers t := by
  intro w hw hwt
  let C := centralizer ({t} : Set G)
  haveI : (W.subgroupOf C).Normal := (inferInstance : W.Normal).subgroupOf C
  have hP : IsPGroup 2 (W.subgroupOf C) := hW.comap_subtype (K := C)
  have hmem : (⟨w, mem_centralizer_singleton_iff.2 hwt.symm⟩ : ↥C) ∈ W.subgroupOf C := by
    rw [Subgroup.mem_subgroupOf]
    exact hw
  simpa using h.le_zpowers_of_normal_two hP _ hmem

theorem fittingSubgroup_eq_bot_or_center [Finite G] (h : ModData t B₀ ψ)
    (hO : fusionOddCore G = ⊥) : CFSG.fittingSubgroup G = ⊥ ∨ t ∈ Subgroup.center G := by
  have hfix : ∀ w ∈ CFSG.pCore 2 G, t * w = w * t → w ∈ zpowers t :=
    fixed_mem_zpowers_of_normal_two h (CFSG.pCore_isPGroup (p := 2) (G := G))
  rcases normal_two_group_eq_bot_or_center h.t_sq h.t_ne
      (CFSG.pCore_isPGroup (p := 2) (G := G)) hfix with hW | ht
  · left
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    refine iSup_eq_bot.2 fun p => ?_
    have hp : Nat.Prime (p : ℕ) := Nat.prime_of_mem_primeFactors p.2
    haveI : Fact (Nat.Prime (p : ℕ)) := ⟨hp⟩
    by_cases h2 : (p : ℕ) = 2
    · rw [h2]
      exact hW
    · have hodd : Odd (Nat.card (CFSG.pCore (p : ℕ) G)) := by
        obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := (p : ℕ)) (G := G)).exists_card_eq
        rw [hn]
        exact (hp.odd_of_ne_two h2).pow
      have h1 : CFSG.pCore (p : ℕ) G ≤ fusionOddCore G :=
        le_sSup ⟨CFSG.pCore_normal, hodd⟩
      rw [hO] at h1
      exact le_bot_iff.1 h1
  · exact Or.inr ht

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
