module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FusionCore

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

theorem a6FourSubgroupFusion :
    ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
      (N : Notation25 hs), N.H ≤ Subgroup.normalizer (N.K : Set G) → Concl2521 N →
        ∀ E₁ E₂ : Subgroup G, E₁ ≤ N.SK → IsFourSubgroup E₁ → E₂ ≤ N.SK → IsFourSubgroup E₂ →
          ∃ s ∈ N.S, E₂ = CFSG.conjugate E₁ s := by
  intro G _ _ T M hs N hKH h2521 E₁ E₂ hE₁ h₁4 hE₂ h₂4
  obtain ⟨⟨e⟩, φ, ψ, hcompat⟩ := h2521
  have hK : Nat.card N.K = 360 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  let c : ↥N.H →* MulAut ↥N.K := (conjAct N.K).comp (Subgroup.inclusion hKH)
  have hc : ∀ x : ↥N.H, c x ∈ autOn N.H N.K := fun x =>
    ⟨⟨(x : G), hKH x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  let ρ₀ : ↥N.H →* ↥(autOn N.H N.K) := c.codRestrict _ hc
  let ρ : ↥N.H →* Equiv.Perm (Fin 10) := (A6Models.autA6).subtype.comp (ψ.toMonoidHom.comp ρ₀)
  let ι : ↥N.K →* Equiv.Perm (Fin 10) := (A6Models.psl29).subtype.comp φ.toMonoidHom
  have hρ : ρ.range = A6Models.autA6 := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      exact (ψ (ρ₀ x)).2
    · intro ha
      obtain ⟨y, hy, hyc⟩ := (ψ.symm ⟨a, ha⟩).2
      refine ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
      have h1 : ρ₀ ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩ = ψ.symm ⟨a, ha⟩ :=
        Subtype.ext hyc
      show ((ψ (ρ₀ ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩) : ↥A6Models.autA6) :
        Equiv.Perm (Fin 10)) = a
      rw [h1]
      simp
  have hι : Function.Injective ι := (A6Models.psl29).subtype_injective.comp φ.injective
  have hιr : ι.range = A6Models.psl29 := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact (φ k).2
    · intro hx
      exact ⟨φ.symm ⟨x, hx⟩, by simp [ι]⟩
  have hιρ : ∀ k : ↥N.K, ρ ⟨(k : G), N.K_le_H k.2⟩ = ι k := by
    intro k
    have hk : conjAct N.K ⟨(k : G), Subgroup.le_normalizer k.2⟩ ∈ autOn N.H N.K :=
      ⟨⟨(k : G), Subgroup.le_normalizer k.2⟩, Subgroup.mem_subgroupOf.mpr (N.K_le_H k.2), rfl⟩
    exact hcompat k hk
  exact A6Fusion.fusion_of_hom N.K_le_H hKH N.tuple.sylow ρ hρ ι hι hιr hιρ hK hE₁ h₁4 hE₂ h₂4

end CFSG.QuasithinUnique
