module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2ActModel
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2Data

public section

namespace CFSG.ComponentClassification.HSFLit.L2Act

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

theorem exists_l2Data_of_embedding (h : Config t L) (T : Sylow 2 ↥(centralizer ({t} : Set X)))
    {G : Type*} [Group G] (Φ : ↥(normalizer (L : Set X)) →* G)
    (hΦ : ∀ g, Φ g = 1 ↔ (g : X) ∈ coreActionKernel L)
    (ρ : G →* Multiplicative (ZMod 2 × ZMod 2)) (P : Subgroup G) (j : P →* Perm (ZMod 8))
    (hj : Function.Injective j) (hjH : ∀ p, j p ∈ H8) (hjρ : ∀ p : P, ρ p = typeP (j p))
    (hTP : ∀ g : ↥(normalizer (L : Set X)), (g : X) ∈ Config.sylowIn T → Φ g ∈ P)
    (hjR : ∀ (g : ↥(normalizer (L : Set X))) (hg : (g : X) ∈ Config.sylowIn T ⊓ L),
      j ⟨Φ g, hTP g hg.1⟩ ∈ R8) :
    ∃ A : L2Data t L, A.syl = T := by
  have hTN : Config.sylowIn T ≤ normalizer (L : Set X) :=
    (Config.sylowIn_le T).trans h.le_normalizer
  set ι : Config.sylowIn T →* normalizer (L : Set X) := Subgroup.inclusion hTN with hι
  set Φ₀ : Config.sylowIn T →* P := (Φ.comp ι).codRestrict P (fun g => hTP (ι g) g.2) with hΦ₀
  set ψ : Config.sylowIn T →* Perm (ZMod 8) := j.comp Φ₀ with hψ
  have hψ1 : ∀ g, ψ g = 1 ↔ (g : X) ∈ coreActionKernel L := by
    intro g
    rw [hψ, MonoidHom.comp_apply, map_eq_one_iff j hj, ← Subtype.coe_inj, OneMemClass.coe_one]
    exact hΦ (ι g)
  have hψR : ∀ g : Config.sylowIn T, (g : X) ∈ L → ψ g ∈ R8 := fun g hg => hjR (ι g) ⟨g.2, hg⟩
  have hsurj : ∀ σ ∈ R8, ∃ g : Config.sylowIn T, (g : X) ∈ L ∧ ψ g = σ := by
    set R : Subgroup (Config.sylowIn T) := (Config.sylowIn T ⊓ L).subgroupOf (Config.sylowIn T)
      with hR
    set f := ψ.comp R.subtype with hf
    have hfinj : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, hψ1] at hx
      have h1 : ((x : Config.sylowIn T) : X) ∈
          (Config.sylowIn T ⊓ coreActionKernel L ⊓ L : Subgroup X) :=
        ⟨⟨(x : Config.sylowIn T).2, hx⟩, x.2.2⟩
      rw [h.inf_kernel_inf_L T, mem_bot] at h1
      rw [mem_bot]
      exact Subtype.ext (Subtype.ext h1)
    have hrange : f.range ≤ R8 := by
      rintro _ ⟨x, rfl⟩
      exact hψR _ x.2.2
    have hcard : Nat.card f.range = 8 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv, hR,
        Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : Config.sylowIn T ⊓ L ≤
          Config.sylowIn T)).toEquiv]
      exact h.card_inf_L T
    have heq : f.range = R8 := Subgroup.eq_of_le_of_card_ge hrange (by rw [card_R8, hcard])
    intro σ hσ
    rw [← heq] at hσ
    obtain ⟨x, rfl⟩ := hσ
    exact ⟨x, x.2.2, rfl⟩
  refine ⟨{
    config := h
    syl := T
    ψ := ψ
    ψ_eq_one_iff := hψ1
    ψ_mem_R8 := hψR
    ψ_mem_H8 := fun g => hjH (Φ₀ g)
    exists_ψ_eq := hsurj
    τ := ρ.comp (Φ.comp (Subgroup.inclusion h.le_normalizer))
    τ_eq := fun g => ?_ }, rfl⟩
  rw [type8_eq_typeP]
  exact hjρ (Φ₀ g)

end CFSG.ComponentClassification.HSFLit.L2Act
