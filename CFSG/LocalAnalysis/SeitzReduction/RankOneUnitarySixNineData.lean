module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryU1Elem

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools
open scoped commutatorElement

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure U3U1Data (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G)
    (T R₂ U₁ : Subgroup G) : Prop where
  normalizer_le : normalizer (szR (szT₁ L T) R₂ t : Set G) ≤ normalizer (U₁ : Set G)
  le_normalizer_szR : U₁ ≤ normalizer (szR (szT₁ L T) R₂ t : Set G)
  le : szT₁ L T ⊔ R₂ ≤ U₁
  le_centralizer : U₁ ≤ centralizer (R₂ : Set G)
  t_not_mem : t ∉ U₁
  card : Nat.card U₁ = (2 ^ f) ^ 6
  inf_szR : U₁ ⊓ szR (szT₁ L T) R₂ t = szT₁ L T ⊔ R₂
  transitive : ∀ w ∈ szT₁ L T, ∃ u ∈ U₁, ∃ r ∈ R₂, u * t * u⁻¹ = r * w * t
  mem_szR : ∀ u ∈ U₁ ⊔ zpowers t,
    (R₂ ⊔ zpowers t).map (MulAut.conj u).toMonoidHom = R₂ ⊔ zpowers t →
      u ∈ szR (szT₁ L T) R₂ t
  sq_R₂ : ∀ r ∈ R₂, r ^ 2 = 1
  comm_mem : ∀ x ∈ U₁, ∀ y ∈ U₁, x * y * x⁻¹ * y⁻¹ ∈ R₂
  sq_mem : ∀ x ∈ U₁, x ^ 2 ∈ R₂
  commutator_eq : ⁅U₁, U₁⁆ = R₂
  conj_not_mem : ∀ g : G, g * t * g⁻¹ ∉ U₁
  conj_of_mem : ∀ g : G, g * t * g⁻¹ ∈ U₁ ⊔ zpowers t → ∃ u ∈ U₁, g * t * g⁻¹ = u * t * u⁻¹

theorem exists_mul_eq_of_mem_sup_of_le_normalizer {G : Type*} [Group G] {U T : Subgroup G}
    (hTU : T ≤ normalizer (U : Set G)) {x : G} (hx : x ∈ U ⊔ T) :
    ∃ u ∈ U, ∃ s ∈ T, u * s = x := by
  have hx' : x ∈ ((U ⊔ T : Subgroup G) : Set G) := hx
  rw [coe_mul_of_right_le_normalizer_left U T hTU] at hx'
  obtain ⟨u, hu, s, hs, rfl⟩ := Set.mem_mul.mp hx'
  exact ⟨u, hu, s, hs, rfl⟩

namespace U3U1Data

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ U₁ : Subgroup G}

theorem isPGroup (hU : U3U1Data G L f t T R₂ U₁) : IsPGroup 2 U₁ :=
  IsPGroup.of_card (n := 6 * f) (by rw [hU.card, ← pow_mul, mul_comm])

theorem mem_szT₁_of_commute (hU : U3U1Data G L f t T R₂ U₁) (hR : U3R2 G L (szT₁ L T) R₂ t f)
    {x : G} (hx : x ∈ U₁) (hxt : x * t = t * x) : x ∈ szT₁ L T := by
  have hxR : x ∈ normalizer (R₂ : Set G) := centralizer_le_normalizer _ (hU.le_centralizer hx)
  have hxR₁ := hU.mem_szR x (mem_sup_left hx) (by
    rw [map_conj_sup_zpowers hxR, hxt, mul_inv_cancel_right])
  have hxH : x ∈ szT₁ L T ⊔ R₂ := by rw [← hU.inf_szR]; exact mem_inf.mpr ⟨hx, hxR₁⟩
  obtain ⟨w, hw, r, hr, rfl⟩ := hR.mem_sup_iff.mp hxH
  have hwt : w * t = t * w := hR.t_comm w hw
  have hrt : r * t = t * r := by
    calc r * t = w⁻¹ * (w * r * t) := by group
      _ = w⁻¹ * (t * (w * r)) := by rw [hxt]
      _ = w⁻¹ * (t * w) * r := by group
      _ = w⁻¹ * (w * t) * r := by rw [hwt]
      _ = t * r := by group
  exact mul_mem hw (szA₁_le _ (hR.rho_ker r hr hrt))

theorem inf_eq (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) : U₁ ⊓ T = szT₁ L T := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxU, hxT⟩ := mem_inf.mp hx
    exact hU.mem_szT₁_of_commute hR hxU (mem_centralizer_singleton_iff.mp (h.le hxT))
  · exact le_inf (le_sup_left.trans hU.le) (szT₁_le_left L T)

theorem conj_not_mem_centralizer (hU : U3U1Data G L f t T R₂ U₁)
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (g : G) : g * t * g⁻¹ ∉ centralizer (R₂ : Set G) :=
  conj_t_not_mem_centralizer_of_card (q := 2 ^ f) hR.card hU.sq_R₂ hR.comm h.sq_eq_one
    hU.le_centralizer hU.isPGroup
    (fun P hP hPt => by
      rw [hU.card]
      exact h.card_lt_of_isPGroup_of_card_sylow (h.card_lt_of_card_sylow hS2) hP hPt)
    (fun B hBt hB2 _ => h.card_lt_of_sq_eq_one_of_card_sylow hS2 hBt hB2) g

end U3U1Data

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

section Certificates

theorem u3U1Data_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2)
    {E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))} (hE : E ≤ (u3OmegaAction L T R₂ t).range)
    (hEn : (E.subgroupOf (u3OmegaAction L T R₂ t).range).Normal)
    (hEreg : ∀ a b : u3Omega L T R₂ t, ∃! x : E, (x : Equiv.Perm (u3Omega L T R₂ t)) a = b) :
    U3U1Data G L f t T R₂ (u3U L T R₂ t E ⊓ centralizer (R₂ : Set G)) := by
  obtain ⟨hYU₁, hHU₁, htU₁, hUeq, hU₁R₁, hcov⟩ :=
    h.u3U₁_facts_of_card_sylow hS2 hR hc hΩ hE hEn hEreg
  obtain ⟨hR₂2, hU₁c, hU₁2, hU₁'⟩ :=
    u3U1ElemStatement G L f t T R₂ E h hS2 hR hc hΩ hE hEn hEreg
  refine ⟨hYU₁, inf_le_left.trans (u3U_le_normalizer L T R₂ t E), hHU₁, inf_le_right, htU₁,
    h.card_u3U₁_of_card_sylow hS2 hR hc hΩ hE hEn hEreg, hU₁R₁, hcov, fun u hu hut => ?_, hR₂2,
    hU₁c, hU₁2, hU₁', h.conj_t_not_mem_u3U₁_of_elem_of_card_sylow hS2 hR hc hΩ hE hEn hEreg hR₂2,
    fun g hg => h.conj_t_of_mem_u3U₁_sup_of_elem_of_card_sylow hS2 hR hc hΩ hE hEn hEreg hR₂2
      hU₁c hU₁2 g hg⟩
  rw [← hUeq] at hu
  exact h.mem_szR_of_mem_u3U_of_card_sylow hS2 hR hc hΩ hEreg hu hut

end Certificates

end U3Start

namespace U3U1Data

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ U₁ : Subgroup G}

section Certificates

theorem le_normalizer (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) : T ≤ normalizer (U₁ : Set G) := by
  obtain ⟨-, -, -, hNA, -, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  have hTA : T ≤ normalizer (szA L T t : Set G) :=
    Subgroup.le_normalizer.trans (h.normalizer_le_normalizer_szA_of_card_sylow hS2)
  exact fun s hs => hU.normalizer_le (hNA (hTA hs))

theorem isPGroup_sup (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) : IsPGroup 2 (U₁ ⊔ T : Subgroup G) :=
  IsPGroup.to_sup_of_normal_left' hU.isPGroup h.isPGroup (hU.le_normalizer h hS2 hR)

theorem commutator_le (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) : ⁅U₁ ⊔ T, U₁ ⊔ T⁆ ≤ U₁ := by
  have hTU := hU.le_normalizer h hS2 hR
  have hTT := h.commutator_le_szT₁_of_card_sylow hS2
  have hSN : U₁ ⊔ T ≤ normalizer (U₁ : Set G) := sup_le Subgroup.le_normalizer hTU
  have hdec : ∀ x ∈ U₁ ⊔ T, ∃ u ∈ T, ∃ w ∈ U₁, u * w = x := by
    intro x hx
    obtain ⟨w₀, hw₀, u, hu, rfl⟩ := exists_mul_eq_of_mem_sup_of_le_normalizer hTU hx
    exact ⟨u, hu, u⁻¹ * w₀ * u, (mem_normalizer_iff''.mp (hTU hu) w₀).mp hw₀, by group⟩
  have hconj : ∀ c ∈ U₁ ⊔ T, ∀ w ∈ U₁, c * w * c⁻¹ ∈ U₁ :=
    fun c hc w hw => (mem_normalizer_iff.mp (hSN hc) w).mp hw
  have hconj' : ∀ c ∈ U₁ ⊔ T, ∀ w ∈ U₁, c⁻¹ * w * c ∈ U₁ :=
    fun c hc w hw => (mem_normalizer_iff''.mp (hSN hc) w).mp hw
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨u, hu, w, hw, rfl⟩ := hdec x hx
  obtain ⟨u', hu', w', hw', rfl⟩ := hdec y hy
  have huS : u ∈ U₁ ⊔ T := mem_sup_right hu
  have hu'S : u' ∈ U₁ ⊔ T := mem_sup_right hu'
  have hA := hconj' u' hu'S w hw
  have hB : u'⁻¹ * w * u' * w' * w⁻¹ ∈ U₁ := mul_mem (mul_mem hA hw') (inv_mem hw)
  have hC := hconj u huS _ hB
  have hD := hconj u' hu'S _ (mul_mem hC (inv_mem hw'))
  have huu' : ⁅u, u'⁆ ∈ U₁ :=
    hU.le (mem_sup_left (hTT (commutator_mem_commutator hu hu')))
  have e : ⁅u * w, u' * w'⁆ =
      ⁅u, u'⁆ * (u' * (u * (u'⁻¹ * w * u' * w' * w⁻¹) * u⁻¹ * w'⁻¹) * u'⁻¹) := by
    rw [commutatorElement_def, commutatorElement_def]
    group
  rw [e]
  exact mul_mem huu' hD

end Certificates

end U3U1Data

end CFSG.SeitzReduction.RankOne
