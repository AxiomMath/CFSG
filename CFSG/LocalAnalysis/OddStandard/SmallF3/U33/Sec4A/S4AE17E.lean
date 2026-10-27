module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathModel

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

private abbrev wmodDecEq : DecidableEq WMod := WMod.equivProd.decidableEq

attribute [local instance 2000] wmodDecEq

private instance : Fintype WMod :=
  Fintype.ofEquiv (Fin 4 × Fin 4 × Fin 2) WMod.equivProd.symm

private theorem centralizer_card_eq_filter (g : WMod) :
    Nat.card ↥(centralizer ({g} : Set WMod)) =
      (Finset.univ.filter (fun x : WMod => x * g = g * x)).card := by
  refine (Nat.card_congr (Equiv.subtypeEquivRight
    (fun x : WMod => Subgroup.mem_centralizer_singleton_iff))).trans ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

private theorem wmod_threshold : ∀ g : WMod,
    16 ≤ (Finset.univ.filter (fun x : WMod => x * g = g * x)).card → g ^ 4 = 1 := by
  decide +kernel

theorem z18_wmod_check (g : WMod) (hc : 16 ≤ Nat.card ↥(centralizer ({g} : Set WMod))) :
    g ^ 4 = 1 := by
  rw [centralizer_card_eq_filter g] at hc
  exact wmod_threshold g hc

variable {G : Type} [Group G] [Finite G]

theorem z18_Tcent_lemma {x₁ x₂ lam : G} (h : WreathRel x₁ x₂ lam) {w : G}
    (hw : w ∈ wreathGrp x₁ x₂ lam)
    (hc : 16 ≤ Nat.card ↥(wreathGrp x₁ x₂ lam ⊓ centralizer ({w} : Set G))) : w ^ 4 = 1 := by
  obtain ⟨φ, hφinj, hφrange, -, -, -⟩ := h.exists_embedding
  rw [← hφrange] at hw
  obtain ⟨g, hg⟩ := hw
  rw [← hg] at hc ⊢
  have hmap : (centralizer ({g} : Set WMod)).map φ =
      wreathGrp x₁ x₂ lam ⊓ centralizer ({φ g} : Set G) := by
    rw [← hφrange]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨y, rfl⟩, ?_⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hy]
    · rintro ⟨⟨y, rfl⟩, hx⟩
      refine ⟨y, ?_, rfl⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr (hφinj ?_)
      rw [map_mul, map_mul, Subgroup.mem_centralizer_singleton_iff.mp hx]
  have hcard : Nat.card ↥(centralizer ({g} : Set WMod)) =
      Nat.card ↥(wreathGrp x₁ x₂ lam ⊓ centralizer ({φ g} : Set G)) := by
    rw [← hmap]
    exact (Subgroup.card_map_of_injective hφinj).symm
  rw [← hcard] at hc
  rw [← map_pow, z18_wmod_check g hc, map_one]

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
