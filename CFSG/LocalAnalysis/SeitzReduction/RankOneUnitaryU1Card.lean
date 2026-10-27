module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryU1Cent

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem card_eq_of_regular {Ω : Type*} {E : Subgroup (Equiv.Perm Ω)}
    (hreg : ∀ a b : Ω, ∃! x : E, (x : Equiv.Perm Ω) a = b) (ω₀ : Ω) :
    Nat.card E = Nat.card Ω := by
  have hbij : Function.Bijective (fun x : E => (x : Equiv.Perm Ω) ω₀) := by
    refine ⟨fun x y hxy => ?_, fun b => ?_⟩
    · obtain ⟨z, -, hz⟩ := hreg ω₀ ((x : Equiv.Perm Ω) ω₀)
      rw [hz x rfl, hz y hxy.symm]
    · obtain ⟨x, hx, -⟩ := hreg ω₀ b
      exact ⟨x, hx⟩
  exact Nat.card_eq_of_bijective _ hbij

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

section Certificates


theorem card_u3U_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2)
    {E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))} (hE : E ≤ (u3OmegaAction L T R₂ t).range)
    (hEreg : ∀ a b : u3Omega L T R₂ t, ∃! x : E, (x : Equiv.Perm (u3Omega L T R₂ t)) a = b) :
    Nat.card (u3U L T R₂ t E) = 2 * (2 ^ f) ^ 6 := by
  have hUY := u3U_le_normalizer L T R₂ t E
  set φ : u3U L T R₂ t E →* Equiv.Perm (u3Omega L T R₂ t) :=
    (u3OmegaAction L T R₂ t).comp (Subgroup.inclusion hUY) with hφ
  have hφapp : ∀ u : u3U L T R₂ t E, φ u = u3OmegaAction L T R₂ t ⟨u, hUY u.2⟩ := fun u => rfl
  have hrange : φ.range = E := by
    ext e
    constructor
    · rintro ⟨u, rfl⟩
      obtain ⟨hx, hxE⟩ := mem_u3U.mp u.2
      rw [hφapp]
      exact hxE
    · intro he
      obtain ⟨⟨y, hy⟩, rfl⟩ := hE he
      exact ⟨⟨y, mem_u3U.mpr ⟨hy, he⟩⟩, rfl⟩
  have hR₁U := h.szR_le_u3U_of_card_sylow hS2 hR E
  have hker : φ.ker = (szR (szT₁ L T) R₂ t).subgroupOf (u3U L T R₂ t E) := by
    ext u
    rw [MonoidHom.mem_ker, mem_subgroupOf, hφapp]
    constructor
    · intro h1
      refine h.mem_szR_of_forall_map_conj_eq_of_card_sylow hS2 hR hc hΩ (hUY u.2) fun X hX => ?_
      have h3 := congrArg (fun σ : Equiv.Perm (u3Omega L T R₂ t) =>
        ((σ ⟨X, hX⟩ : u3Omega L T R₂ t) : Subgroup G)) h1
      simpa [u3OmegaAction_apply] using h3
    · intro hu
      refine Equiv.ext fun X => Subtype.ext ?_
      rw [u3OmegaAction_apply, Equiv.Perm.one_apply]
      exact h.map_conj_eq_of_mem_szR_of_card_sylow hS2 hR hu X.2
  have hcard := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hrange, card_eq_of_regular hEreg
    ⟨R₂ ⊔ zpowers t, sup_zpowers_mem_u3Omega L T R₂ t⟩, Nat.card_coe_set_eq, hΩ, hker,
    Nat.card_congr (subgroupOfEquivOfLe hR₁U).toEquiv] at hcard
  obtain ⟨hR₁eq, -⟩ := h.s₁_facts_of_card_sylow hS2 hR
  rw [hR₁eq, h.card_u3R₁_of_card_sylow hS2] at hcard
  rw [← hcard]
  ring

theorem card_u3U₁_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2)
    {E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))} (hE : E ≤ (u3OmegaAction L T R₂ t).range)
    (hEn : (E.subgroupOf (u3OmegaAction L T R₂ t).range).Normal)
    (hEreg : ∀ a b : u3Omega L T R₂ t, ∃! x : E, (x : Equiv.Perm (u3Omega L T R₂ t)) a = b) :
    Nat.card (u3U L T R₂ t E ⊓ centralizer (R₂ : Set G) : Subgroup G) = (2 ^ f) ^ 6 := by
  obtain ⟨hYU₁, -, htU₁, hUeq, -, -⟩ := h.u3U₁_facts_of_card_sylow hS2 hR hc hΩ hE hEn hEreg
  have htN : zpowers t ≤
      normalizer ((u3U L T R₂ t E ⊓ centralizer (R₂ : Set G) : Subgroup G) : Set G) :=
    zpowers_le.mpr (hYU₁ (Subgroup.le_normalizer (mem_szR_right _ _ _)))
  have h1 := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer htN
  have hinf : zpowers t ⊓ (u3U L T R₂ t E ⊓ centralizer (R₂ : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxt, hxU₁⟩ := mem_inf.mp hx
    rcases mem_zpowers_involution_eq_one_or_eq hR.t_sq hxt with hx1 | hx1
    · rw [hx1]
      exact one_mem _
    · rw [hx1] at hxU₁
      exact absurd hxU₁ htU₁
  rw [hinf, card_bot, mul_one, sup_comm, ← hUeq, h.card_u3U_of_card_sylow hS2 hR hc hΩ hE hEreg,
    Nat.card_zpowers, h.inv] at h1
  omega

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
