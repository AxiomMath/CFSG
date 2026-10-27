module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryU1Sq
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryU1Statement

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped commutatorElement

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

section Certificates


theorem exists_comm_not_mem_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2)
    {E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))} (hE : E ≤ (u3OmegaAction L T R₂ t).range)
    (hEn : (E.subgroupOf (u3OmegaAction L T R₂ t).range).Normal)
    (hEreg : ∀ a b : u3Omega L T R₂ t, ∃! x : E, (x : Equiv.Perm (u3Omega L T R₂ t)) a = b) :
    ∃ x ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G),
      ∃ y ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G), x * y * x⁻¹ * y⁻¹ ∉ szA₁ (szT₁ L T) := by
  obtain ⟨-, hHU₁, -, -, -, hcov⟩ := h.u3U₁_facts_of_card_sylow hS2 hR hc hΩ hE hEn hEreg
  set U₁ := u3U L T R₂ t E ⊓ centralizer (R₂ : Set G) with hU₁
  by_contra hall
  push Not at hall
  have hT₁ab : ∀ w ∈ szT₁ L T, ∀ w' ∈ szT₁ L T, w * w' = w' * w := by
    intro w hw w' hw'
    obtain ⟨z, hz, r, hr, hzt⟩ := hcov w hw
    have hw'U₁ : w' ∈ U₁ := hHU₁ (mem_sup_left hw')
    obtain ⟨c, hcdef⟩ : ∃ c : G, c = z * w' * z⁻¹ * w'⁻¹ := ⟨_, rfl⟩
    have hcA : c ∈ szA₁ (szT₁ L T) := hcdef ▸ hall z hz w' hw'U₁
    have htw' : t * w' * t⁻¹ = w' := by rw [← hR.t_comm w' hw', mul_inv_cancel_right]
    have htc : t * c * t⁻¹ = c := by rw [← hR.szA₁_comm_t hcA, mul_inv_cancel_right]
    have htz : t * z * t⁻¹ = w⁻¹ * r⁻¹ * z := by
      have h1 : t * z⁻¹ * t⁻¹ = z⁻¹ * (r * w) := by
        calc t * z⁻¹ * t⁻¹ = z⁻¹ * (z * t * z⁻¹) * t⁻¹ := by group
          _ = z⁻¹ * (r * w * t) * t⁻¹ := by rw [hzt]
          _ = z⁻¹ * (r * w) := by group
      calc t * z * t⁻¹ = (t * z⁻¹ * t⁻¹)⁻¹ := by group
        _ = w⁻¹ * r⁻¹ * z := by rw [h1]; group
    have h2 : (w⁻¹ * r⁻¹ * z) * w' * (w⁻¹ * r⁻¹ * z)⁻¹ * w'⁻¹ = c := by
      rw [← htz, ← htc]
      calc t * z * t⁻¹ * w' * (t * z * t⁻¹)⁻¹ * w'⁻¹ =
          t * z * t⁻¹ * (t * w' * t⁻¹) * (t * z * t⁻¹)⁻¹ * (t * w' * t⁻¹)⁻¹ := by rw [htw']
        _ = t * c * t⁻¹ := by rw [hcdef]; group
    obtain ⟨a, ha⟩ : ∃ a : G, a = w⁻¹ * r⁻¹ := ⟨_, rfl⟩
    have hca : a * c = c * a := by
      have h3 : w⁻¹ * c = c * w⁻¹ :=
        mem_centralizer_iff.mp (mem_szA₁.mp hcA).2 _ (inv_mem hw)
      have h4 : r⁻¹ * c = c * r⁻¹ := hR.comm _ (inv_mem hr) _ (hR.le hcA)
      rw [ha, mul_assoc, h4, ← mul_assoc, h3, mul_assoc]
    have h5 : a * w' * a⁻¹ * w'⁻¹ = 1 := by
      have e : (a * z) * w' * (a * z)⁻¹ * w'⁻¹ = a * c * a⁻¹ * (a * w' * a⁻¹ * w'⁻¹) := by
        rw [hcdef]; group
      have h6 : a * c * a⁻¹ = c := by rw [hca, mul_inv_cancel_right]
      rw [← ha, e, h6] at h2
      have := congrArg (fun x => c⁻¹ * x) h2
      simpa using this
    have hrw' : r⁻¹ * w' = w' * r⁻¹ := (hR.commT₁ w' hw' _ (inv_mem hr)).symm
    have h7 : w⁻¹ * w' = w' * w⁻¹ := by
      have h8 : a * w' = w' * a := by
        calc a * w' = a * w' * a⁻¹ * w'⁻¹ * (w' * a) := by group
          _ = w' * a := by rw [h5, one_mul]
      rw [ha] at h8
      calc w⁻¹ * w' = w⁻¹ * (w' * r⁻¹) * r := by group
        _ = w⁻¹ * (r⁻¹ * w') * r := by rw [← hrw']
        _ = w⁻¹ * r⁻¹ * w' * r := by group
        _ = w' * (w⁻¹ * r⁻¹) * r := by rw [h8]
        _ = w' * w⁻¹ := by group
    calc w * w' = w * (w' * w⁻¹) * w := by group
      _ = w * (w⁻¹ * w') * w := by rw [h7]
      _ = w' * w := by group
  obtain ⟨-, hA₁card, hA₁eq, -⟩ := h.facts_of_card_sylow hS2
  have hbot : szA₁ (szT₁ L T) = ⊥ := by
    rw [hA₁eq, eq_bot_iff, commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [mem_bot, commutatorElement_def, hT₁ab g₁ hg₁ g₂ hg₂]
    group
  rw [hbot, card_bot] at hA₁card
  have : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := h.two_le; omega)
  omega

theorem sq_eq_one_of_mem_R₂_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2)
    {E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))} (hE : E ≤ (u3OmegaAction L T R₂ t).range)
    (hEn : (E.subgroupOf (u3OmegaAction L T R₂ t).range).Normal)
    (hEreg : ∀ a b : u3Omega L T R₂ t, ∃! x : E, (x : Equiv.Perm (u3Omega L T R₂ t)) a = b) :
    ∀ r ∈ R₂, r ^ 2 = 1 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h.exists_comm_not_mem_of_card_sylow hS2 hR hc hΩ hE hEn hEreg
  have hcR := h.comm_mem_of_mem_u3U₁_of_card_sylow hS2 hR hc hΩ hE hEn hEreg hx hy
  have hx2 := h.sq_mem_of_mem_u3U₁_of_card_sylow hS2 hR hc hΩ hE hEn hEreg hx
  have hcen : ∀ z ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G), ∀ r ∈ R₂, r * z = z * r :=
    fun z hz r hr => mem_centralizer_iff.mp (mem_inf.mp hz).2 r hr
  obtain ⟨c, hcdef⟩ : ∃ c : G, c = x * y * x⁻¹ * y⁻¹ := ⟨_, rfl⟩
  rw [← hcdef] at hcR hxy
  have hxc : x * c * x⁻¹ = c := by rw [← hcen x hx c hcR, mul_inv_cancel_right]
  have h1 : x * y * x⁻¹ = c * y := by rw [hcdef]; group
  have h2 : x ^ 2 * y * (x ^ 2)⁻¹ = c ^ 2 * y := by
    calc x ^ 2 * y * (x ^ 2)⁻¹ = x * (x * y * x⁻¹) * x⁻¹ := by rw [sq]; group
      _ = x * (c * y) * x⁻¹ := by rw [h1]
      _ = (x * c * x⁻¹) * (x * y * x⁻¹) := by group
      _ = c * (c * y) := by rw [hxc, h1]
      _ = c ^ 2 * y := by rw [sq, mul_assoc]
  have h3 : x ^ 2 * y * (x ^ 2)⁻¹ = y := by
    rw [hcen y hy _ hx2, mul_inv_cancel_right]
  have hc2 : c ^ 2 = 1 := by
    rw [h2] at h3
    exact mul_right_cancel (h3.trans (one_mul y).symm)
  rcases hR.sq_eq_one_or with h4 | h4
  · exact h4
  · exact absurd (h4 c hcR hc2) hxy

theorem commutator_u3U₁_eq_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2)
    {E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))} (hE : E ≤ (u3OmegaAction L T R₂ t).range)
    (hEn : (E.subgroupOf (u3OmegaAction L T R₂ t).range).Normal)
    (hEreg : ∀ a b : u3Omega L T R₂ t, ∃! x : E, (x : Equiv.Perm (u3Omega L T R₂ t)) a = b) :
    ⁅u3U L T R₂ t E ⊓ centralizer (R₂ : Set G), u3U L T R₂ t E ⊓ centralizer (R₂ : Set G)⁆ =
      R₂ := by
  obtain ⟨hYU₁, hHU₁, -, -, -, -⟩ := h.u3U₁_facts_of_card_sylow hS2 hR hc hΩ hE hEn hEreg
  obtain ⟨-, -, hA₁eq, -⟩ := h.facts_of_card_sylow hS2
  set U₁ := u3U L T R₂ t E ⊓ centralizer (R₂ : Set G) with hU₁
  set C := ⁅U₁, U₁⁆ with hC
  apply le_antisymm
  · rw [commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [commutatorElement_def]
    exact h.comm_mem_of_mem_u3U₁_of_card_sylow hS2 hR hc hΩ hE hEn hEreg hg₁ hg₂
  · have hA₁C : szA₁ (szT₁ L T) ≤ C := by
      rw [hA₁eq]
      exact commutator_mono (le_sup_left.trans hHU₁) (le_sup_left.trans hHU₁)
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      h.exists_comm_not_mem_of_card_sylow hS2 hR hc hΩ hE hEn hEreg
    obtain ⟨c₀, hc₀⟩ : ∃ c₀ : G, c₀ = x * y * x⁻¹ * y⁻¹ := ⟨_, rfl⟩
    have hc₀R : c₀ ∈ R₂ :=
      hc₀ ▸ h.comm_mem_of_mem_u3U₁_of_card_sylow hS2 hR hc hΩ hE hEn hEreg hx hy
    rw [← hc₀] at hxy
    have hc₀C : c₀ ∈ C := by
      rw [hc₀, ← commutatorElement_def]
      exact commutator_mem_commutator hx hy
    obtain ⟨d, hdt, hdR, hdT, htr⟩ := hR.torus
    have hdY : d ∈ normalizer (szR (szT₁ L T) R₂ t : Set G) := by
      have htN : t ∈ normalizer (zpowers t : Set G) := Subgroup.le_normalizer (mem_zpowers t)
      refine mem_normalizer_of_forall_inv_mul_mul_mem fun z hz => ?_
      have hle : szR (szT₁ L T) R₂ t ≤
          (szR (szT₁ L T) R₂ t).comap (MulAut.conj d⁻¹).toMonoidHom := by
        refine sup_le (sup_le (fun w hw => ?_) (fun r hr => ?_)) (zpowers_le.mpr ?_)
        · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
          have := (mem_normalizer_iff''.mp hdT w).mp hw
          exact le_szR_left _ _ _ this
        · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
          have := (mem_normalizer_iff''.mp hdR r).mp hr
          exact le_szR_mid _ _ _ this
        · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
          rw [show d⁻¹ * t * d = t by rw [mul_assoc, ← hdt, inv_mul_cancel_left]]
          exact mem_szR_right _ _ _
      have := hle hz
      rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at this
    have hdU₁ : d ∈ normalizer (U₁ : Set G) := hYU₁ hdY
    have hdC : ∀ n : ℕ, ∀ z ∈ C, (d ^ n)⁻¹ * z * d ^ n ∈ C := by
      have hdC1 : d ∈ normalizer (C : Set G) := by
        refine mem_normalizer_of_forall_inv_mul_mul_mem fun z hz => ?_
        have hle : C ≤ C.comap (MulAut.conj d⁻¹).toMonoidHom := by
          rw [hC, commutator_le]
          intro g₁ hg₁ g₂ hg₂
          rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
          have e : d⁻¹ * ⁅g₁, g₂⁆ * d = ⁅d⁻¹ * g₁ * d, d⁻¹ * g₂ * d⁆ := by
            simp only [commutatorElement_def]; group
          rw [e]
          exact commutator_mem_commutator ((mem_normalizer_iff''.mp hdU₁ _).mp hg₁)
            ((mem_normalizer_iff''.mp hdU₁ _).mp hg₂)
        have := hle hz
        rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at this
      intro n z hz
      exact (mem_normalizer_iff''.mp (pow_mem hdC1 n) z).mp hz
    intro r hr
    by_cases hrA : r ∈ szA₁ (szT₁ L T)
    · exact hA₁C hrA
    obtain ⟨n, -, hρ⟩ := hR.sq_eq_conj_of_not_mem hdt hdR htr hc₀R hxy hr hrA
    obtain ⟨v, hv⟩ : ∃ v : G, v = (d ^ n)⁻¹ * c₀ * d ^ n := ⟨_, rfl⟩
    have hvR : v ∈ R₂ := by
      rw [hv]
      have := (mem_normalizer_iff.mp (inv_mem (pow_mem hdR n)) c₀).mp hc₀R
      rwa [inv_inv] at this
    have hDt : d ^ n * t = t * d ^ n := (Commute.pow_left hdt n).eq
    have hρv : v * t * v⁻¹ * t = (d ^ n)⁻¹ * (c₀ * t * c₀⁻¹ * t) * d ^ n := by
      rw [hv]; exact U3R2.rho_conj hDt
    have h1 : r * t * r⁻¹ = v * t * v⁻¹ := by
      rw [hR.conj_t_eq r, hR.conj_t_eq v, hρ, hρv]
    have hrv : r⁻¹ * v ∈ szA₁ (szT₁ L T) := by
      refine hR.rho_ker _ (mul_mem (inv_mem hr) hvR) ?_
      calc r⁻¹ * v * t = r⁻¹ * (v * t * v⁻¹) * v := by group
        _ = r⁻¹ * (r * t * r⁻¹) * v := by rw [← h1]
        _ = t * (r⁻¹ * v) := by group
    have hvC : v ∈ C := hv ▸ hdC n c₀ hc₀C
    have e : r = v * (r⁻¹ * v)⁻¹ := by group
    rw [e]
    exact mul_mem hvC (inv_mem (hA₁C hrv))

theorem _root_.CFSG.SeitzReduction.RankOne.u3U1ElemStatement : U3U1ElemStatement := by
  intro G _ _ L f t T R₂ E h hS2 hR hc hΩ hE hEn hEreg
  exact ⟨h.sq_eq_one_of_mem_R₂_of_card_sylow hS2 hR hc hΩ hE hEn hEreg,
    fun x hx y hy => h.comm_mem_of_mem_u3U₁_of_card_sylow hS2 hR hc hΩ hE hEn hEreg hx hy,
    fun x hx => h.sq_mem_of_mem_u3U₁_of_card_sylow hS2 hR hc hΩ hE hEn hEreg hx,
    h.commutator_u3U₁_eq_of_card_sylow hS2 hR hc hΩ hE hEn hEreg⟩

theorem exists_u3U₁_export_of_regular_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2)
    (hreg : HasRegularNormalSubgroup (u3OmegaAction L T R₂ t).range) :
    ∃ U₁ : Subgroup G,
      normalizer (szR (szT₁ L T) R₂ t : Set G) ≤ normalizer (U₁ : Set G) ∧
      szT₁ L T ⊔ R₂ ≤ U₁ ∧ U₁ ≤ centralizer (R₂ : Set G) ∧ t ∉ U₁ ∧
      Nat.card U₁ = (2 ^ f) ^ 6 ∧ U₁ ⊓ szR (szT₁ L T) R₂ t = szT₁ L T ⊔ R₂ ∧
      (∀ w ∈ szT₁ L T, ∃ u ∈ U₁, ∃ r ∈ R₂, u * t * u⁻¹ = r * w * t) ∧
      (∀ u ∈ U₁ ⊔ zpowers t, (R₂ ⊔ zpowers t).map (MulAut.conj u).toMonoidHom = R₂ ⊔ zpowers t →
        u ∈ szR (szT₁ L T) R₂ t) ∧
      (∀ r ∈ R₂, r ^ 2 = 1) ∧ (∀ x ∈ U₁, ∀ y ∈ U₁, x * y * x⁻¹ * y⁻¹ ∈ R₂) ∧
      (∀ x ∈ U₁, x ^ 2 ∈ R₂) ∧ ⁅U₁, U₁⁆ = R₂ ∧
      (∀ g : G, g * t * g⁻¹ ∉ U₁) ∧
      ∀ g : G, g * t * g⁻¹ ∈ U₁ ⊔ zpowers t → ∃ u ∈ U₁, g * t * g⁻¹ = u * t * u⁻¹ :=
  h.exists_u3U₁_export_of_card_sylow hS2 hR hc hΩ hreg u3U1ElemStatement

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
