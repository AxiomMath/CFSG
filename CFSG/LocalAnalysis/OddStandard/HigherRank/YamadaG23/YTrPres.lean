module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrMap

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

private lemma lift_comp_apply {α G H : Type*} [Group G] [Group H]
    (f : G →* H) (g : α → G) (r : FreeGroup α) :
    FreeGroup.lift (f ∘ g) r = f (FreeGroup.lift g r) := by
  have h := FreeGroup.lift_unique (f := f ∘ g) (g := f.comp (FreeGroup.lift g))
    (x := r) (fun x => by simp)
  exact h.symm

private lemma map_gens11' {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂]
    (f : Γ₁ →* Γ₂) (gf : GFrame Γ₁) :
    (gf.map f).gens11 = f ∘ gf.gens11 := by
  funext i
  fin_cases i <;> rfl

private lemma map_Sσ' {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂]
    (f : Γ₁ →* Γ₂) (gf : GFrame Γ₁) :
    (gf.map f).Sσ = gf.Sσ.map f := by
  change closure ({f gf.a₁, f gf.b₁, f gf.a₂, f gf.b₂, f gf.h₀, f gf.σ} : Set Γ₂) =
    (closure ({gf.a₁, gf.b₁, gf.a₂, gf.b₂, gf.h₀, gf.σ} : Set Γ₁)).map f
  rw [MonoidHom.map_closure]
  congr 1
  simp [Set.image_insert_eq, Set.image_singleton]

private lemma toGroup_map_eq {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂]
    (f : Γ₁ →* Γ₂) (gf : GFrame Γ₁)
    (h : ∀ r ∈ Frame.rels11, FreeGroup.lift gf.gens11 r = 1)
    (h' : ∀ r ∈ Frame.rels11, FreeGroup.lift (gf.map f).gens11 r = 1) :
    PresentedGroup.toGroup h' = f.comp (PresentedGroup.toGroup h) := by
  refine PresentedGroup.ext (fun i => ?_)
  simp [PresentedGroup.toGroup.of, map_gens11' f gf]

variable {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂] [Finite Γ₁] [Finite Γ₂] {f : Γ₁ →* Γ₂}

theorem p11_map_iff (hf : Function.Injective f) (gf : GFrame Γ₁) :
    (gf.map f).P11 ↔ gf.P11 := by
  constructor
  · rintro ⟨h', hinj', hrange'⟩
    have h : ∀ r ∈ Frame.rels11, FreeGroup.lift gf.gens11 r = 1 := by
      intro r hr
      have h1 : FreeGroup.lift (gf.map f).gens11 r = 1 := h' r hr
      rw [map_gens11' f gf] at h1
      rw [lift_comp_apply f gf.gens11 r] at h1
      exact (map_eq_one_iff f hf).mp h1
    have htg := toGroup_map_eq f gf h h'
    refine ⟨h, ?_, ?_⟩
    · rw [htg] at hinj'
      exact (hf.of_comp_iff (PresentedGroup.toGroup h)).mp hinj'
    · rw [htg, MonoidHom.range_comp, map_Sσ' f gf] at hrange'
      exact Subgroup.map_injective hf hrange'
  · rintro ⟨h, hinj, hrange⟩
    have h' : ∀ r ∈ Frame.rels11, FreeGroup.lift (gf.map f).gens11 r = 1 := by
      intro r hr
      rw [map_gens11' f gf, lift_comp_apply f gf.gens11 r, h r hr, map_one]
    have htg := toGroup_map_eq f gf h h'
    refine ⟨h', ?_, ?_⟩
    · rw [htg]
      exact hf.comp hinj
    · rw [htg, MonoidHom.range_comp, hrange, map_Sσ' f gf]

end CFSG.OddStandard.HigherRank.YamadaG23
