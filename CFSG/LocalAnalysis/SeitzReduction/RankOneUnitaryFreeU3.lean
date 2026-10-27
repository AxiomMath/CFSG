module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryFree
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryU1Cent

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

section Certificates


theorem isPGroup_u3U_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2) {E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))}
    (hEreg : ∀ a b : u3Omega L T R₂ t, ∃! x : E, (x : Equiv.Perm (u3Omega L T R₂ t)) a = b) :
    IsPGroup 2 (u3U L T R₂ t E) := by
  set ω₀ : u3Omega L T R₂ t := ⟨R₂ ⊔ zpowers t, sup_zpowers_mem_u3Omega L T R₂ t⟩ with hω₀
  have hEcard : Nat.card E = 2 ^ (2 * f) := by
    have hbij : Function.Bijective
        (fun x : E => (x : Equiv.Perm (u3Omega L T R₂ t)) ω₀) := by
      refine ⟨fun x y hxy => ?_, fun b => ?_⟩
      · obtain ⟨z, -, hz⟩ := hEreg ω₀ ((x : Equiv.Perm (u3Omega L T R₂ t)) ω₀)
        rw [hz x rfl, hz y hxy.symm]
      · obtain ⟨x, hx, -⟩ := hEreg ω₀ b
        exact ⟨x, hx⟩
    rw [Nat.card_eq_of_bijective _ hbij, Nat.card_coe_set_eq, hΩ, ← pow_mul, mul_comm]
  obtain ⟨hR₁eq, -⟩ := h.s₁_facts_of_card_sylow hS2 hR
  have hR₁2 : IsPGroup 2 (szR (szT₁ L T) R₂ t) := by
    rw [hR₁eq]
    exact h.isPGroup_u3R₁_of_card_sylow hS2
  intro u
  obtain ⟨huY, huE⟩ := mem_u3U.mp u.2
  have h1 : (u3OmegaAction L T R₂ t ⟨u, huY⟩) ^ (Nat.card E) = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (G := E) (x := ⟨_, huE⟩))
  have hY' := pow_mem huY (Nat.card E)
  have h2 : (u : G) ^ (Nat.card E) ∈ szR (szT₁ L T) R₂ t := by
    refine h.mem_szR_of_forall_map_conj_eq_of_card_sylow hS2 hR hc hΩ hY' fun X hX => ?_
    have h3 : u3OmegaAction L T R₂ t ⟨(u : G) ^ Nat.card E, hY'⟩ = 1 := by
      have e : (⟨(u : G) ^ Nat.card E, hY'⟩ :
          normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G)) =
          (⟨u, huY⟩ : normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G)) ^
            Nat.card E := Subtype.ext (by simp)
      rw [e, map_pow, h1]
    have h4 := congrArg (fun σ : Equiv.Perm (u3Omega L T R₂ t) =>
      ((σ ⟨X, hX⟩ : u3Omega L T R₂ t) : Subgroup G)) h3
    simpa [u3OmegaAction_apply] using h4
  obtain ⟨k, hk⟩ := hR₁2 ⟨_, h2⟩
  refine ⟨2 * f + k, Subtype.ext ?_⟩
  have hk' : ((u : G) ^ Nat.card E) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  rw [hEcard] at hk'
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  rw [pow_add, pow_mul, hk']

theorem mem_sup_of_mem_u3U₁_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2)
    {E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))} (hE : E ≤ (u3OmegaAction L T R₂ t).range)
    (hEn : (E.subgroupOf (u3OmegaAction L T R₂ t).range).Normal)
    (hEreg : ∀ a b : u3Omega L T R₂ t, ∃! x : E, (x : Equiv.Perm (u3Omega L T R₂ t)) a = b)
    {x : G} (hx : x ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G))
    (hxt : t * x * t⁻¹ * x⁻¹ ∈ R₂) : x ∈ szT₁ L T ⊔ R₂ := by
  obtain ⟨-, -, -, -, hU₁R₁, -⟩ := h.u3U₁_facts_of_card_sylow hS2 hR hc hΩ hE hEn hEreg
  obtain ⟨-, -, -, hNR₁⟩ := h.char_of_card_sylow hS2 hR
  have hxU := (mem_inf.mp hx).1
  have hxY := u3U_le_normalizer L T R₂ t E hxU
  have hxR₂ : x ∈ normalizer (R₂ : Set G) := (mem_inf.mp (hNR₁ hxY)).2
  have hxR₁ : x ∈ szR (szT₁ L T) R₂ t := by
    refine h.mem_szR_of_mem_u3U_of_card_sylow hS2 hR hc hΩ hEreg hxU ?_
    rw [map_conj_sup_zpowers hxR₂]
    have e : x * t * x⁻¹ = t * (t⁻¹ * (t * x * t⁻¹ * x⁻¹)⁻¹ * t) := by group
    have hs : t⁻¹ * (t * x * t⁻¹ * x⁻¹)⁻¹ * t ∈ R₂ := by
      have := hR.tN _ (inv_mem hxt)
      rw [hR.t_inv] at this ⊢
      exact this
    rw [e, sup_zpowers_mul_eq hs]
  rw [← hU₁R₁]
  exact mem_inf.mpr ⟨hx, hxR₁⟩

theorem conj_t_of_mem_u3U₁_sup_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2)
    {E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))} (hE : E ≤ (u3OmegaAction L T R₂ t).range)
    (hEn : (E.subgroupOf (u3OmegaAction L T R₂ t).range).Normal)
    (hEreg : ∀ a b : u3Omega L T R₂ t, ∃! x : E, (x : Equiv.Perm (u3Omega L T R₂ t)) a = b)
    (hR₂2 : ∀ r ∈ R₂, r ^ 2 = 1)
    (hU₁c : ∀ x ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G),
      ∀ y ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G), x * y * x⁻¹ * y⁻¹ ∈ R₂)
    (hU₁2 : ∀ x ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G), x ^ 2 ∈ R₂)
    (hnot : ∀ g : G, g * t * g⁻¹ ∉ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G)) (g : G)
    (hg : g * t * g⁻¹ ∈ (u3U L T R₂ t E ⊓ centralizer (R₂ : Set G)) ⊔ zpowers t) :
    ∃ u ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G), g * t * g⁻¹ = u * t * u⁻¹ := by
  obtain ⟨hYU₁, hHU₁, -, -, -, hcov⟩ := h.u3U₁_facts_of_card_sylow hS2 hR hc hΩ hE hEn hEreg
  have htU₁ : t ∈ normalizer ((u3U L T R₂ t E ⊓ centralizer (R₂ : Set G) : Subgroup G) :
      Set G) := hYU₁ (Subgroup.le_normalizer (mem_szR_right _ _ _))
  exact hR.conj_t_of_mem_sup_zpowers htU₁ (le_sup_right.trans hHU₁) hR₂2 hU₁c hU₁2
    (fun x hx hxt => h.mem_sup_of_mem_u3U₁_of_card_sylow hS2 hR hc hΩ hE hEn hEreg hx hxt)
    hcov hnot g hg

theorem conj_t_not_mem_u3U₁_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2) {E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))}
    (hEreg : ∀ a b : u3Omega L T R₂ t, ∃! x : E, (x : Equiv.Perm (u3Omega L T R₂ t)) a = b)
    (hR₂2 : ∀ r ∈ R₂, r ^ 2 = 1)
    (hbound : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({t} : Set G) →
      Nat.card P < Nat.card (u3U L T R₂ t E ⊓ centralizer (R₂ : Set G) : Subgroup G))
    (hel : ∀ B : Subgroup G, B ≤ centralizer ({t} : Set G) → (∀ x ∈ B, x ^ 2 = 1) →
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → Nat.card B < 2 * (2 ^ f) ^ 2) (g : G) :
    g * t * g⁻¹ ∉ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G) :=
  conj_t_not_mem_of_card (q := 2 ^ f) hR.card hR₂2 hR.comm hR.t_sq inf_le_right
    ((h.isPGroup_u3U_of_card_sylow hS2 hR hc hΩ hEreg).to_le inf_le_left) hbound hel g

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
