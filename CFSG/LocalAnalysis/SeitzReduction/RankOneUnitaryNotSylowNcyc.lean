module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryNotSylow
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryLangCor
public import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarCat
public import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarGroups

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools CFSG.LocalAnalysis
open scoped commutatorElement

@[expose] def U3ClosureInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ : Subgroup G),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f → (∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ R₂) →
    (∀ h ∈ normalizer (szA₁ (szT₁ L T) : Set G),
      (∀ r ∈ szR (szT₁ L T) R₂ t, h⁻¹ * r * h ∈ T ⊔ R₂) →
        ∀ r ∈ szR (szT₁ L T) R₂ t, h⁻¹ * r * h ∈ szR (szT₁ L T) R₂ t) ∧
    ∀ g ∈ normalizer (szA₁ (szT₁ L T) : Set G), g⁻¹ * t * g ∈ T ⊔ R₂ →
      g⁻¹ * t * g ∈ szR (szT₁ L T) R₂ t

@[expose] def U3SplitInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T : Subgroup G),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    (¬ ∃ b ∈ T, ∀ s ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T) →
    ∃ v ∈ T, v ^ 2 = 1 ∧ v ∉ szT₁ L T ⊔ zpowers t

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem mul_inv_mem_of_sq_mem_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {s v : G} (hs : s ∈ T)
    (hv : v ∈ T) (hs2 : s ^ 2 ∈ szT₁ L T ⊔ zpowers t) (hv2 : v ^ 2 ∈ szT₁ L T ⊔ zpowers t)
    (hsS : s ∉ szT₁ L T ⊔ zpowers t) (hvS : v ∉ szT₁ L T ⊔ zpowers t) :
    s * v⁻¹ ∈ szT₁ L T ⊔ zpowers t := by
  have : Finite (MulAut L) := finite_mulAut L
  obtain ⟨φ, hker, hcyc⟩ := h.exists_outHom_of_card_sylow hS2
  have hord : ∀ {y : G} (hy : y ∈ T), y ^ 2 ∈ szT₁ L T ⊔ zpowers t →
      y ∉ szT₁ L T ⊔ zpowers t → orderOf (φ ⟨y, hy⟩) = 2 := by
    intro y hy hy2 hyS
    refine orderOf_eq_prime ?_ fun h1 => hyS ((hker ⟨y, hy⟩).mp h1)
    rw [← map_pow]
    exact (hker _).mpr (by simpa using hy2)
  have heq := CFSG.LocalAnalysis.eq_of_orderOf_eq_two_of_isCyclic_subgroup hcyc
    (⟨⟨s, hs⟩, rfl⟩ : φ ⟨s, hs⟩ ∈ φ.range) (⟨⟨v, hv⟩, rfl⟩ : φ ⟨v, hv⟩ ∈ φ.range)
    (hord hs hs2 hsS) (hord hv hv2 hvS)
  have h1 : φ (⟨s, hs⟩ * (⟨v, hv⟩)⁻¹) = 1 := by rw [map_mul, map_inv, heq, mul_inv_cancel]
  exact (hker _).mp h1

theorem exists_normalizer_szA₁_conj_of_outer_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    {g : G} (hxT : g⁻¹ * t * g ∈ T) (hxS : g⁻¹ * t * g ∉ szT₁ L T ⊔ zpowers t) :
    ∃ g' ∈ normalizer (szA₁ (szT₁ L T) : Set G), g'⁻¹ * t * g' = g⁻¹ * t * g := by
  set x := g⁻¹ * t * g with hx
  have ht2 : t * t = 1 := by rw [← sq, h.sq_eq_one]
  have hx2 : x ^ 2 = 1 := by
    calc x ^ 2 = g⁻¹ * (t * t) * g := by rw [hx, sq]; group
      _ = 1 := by rw [ht2]; group
  have hx1 : x ≠ 1 := fun h1 => hxS (h1 ▸ one_mem _)
  have hxo : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  obtain ⟨hxout, hxA₁, -, -⟩ := h.outer_facts_of_card_sylow hS2 hxT hx2 hxS
  obtain ⟨-, hLs, hLnab, -, -⟩ := u3Star_fixed h.two_le h.model hxo (h.le_normalizer hxT) hxout
  set Lx := L ⊓ centralizer ({x} : Set G) with hLx
  have hA₁Lx : szA₁ (szT₁ L T) ≤ Lx := fun b hb => mem_inf.mpr
    ⟨szT₁_le_right L T (szA₁_le _ hb), mem_centralizer_singleton_iff.mpr (hxA₁ b hb).symm⟩
  have hgx : g * x * g⁻¹ = t := by rw [hx]; group
  set M := Lx.map (MulAut.conj g).toMonoidHom with hM
  have hMt : M ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have hyx : y * x = x * y := mem_centralizer_singleton_iff.mp (mem_inf.mp hy).2
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mem_centralizer_singleton_iff]
    calc g * y * g⁻¹ * t = g * (y * x) * g⁻¹ := by rw [← hgx]; group
      _ = g * (x * y) * g⁻¹ := by rw [hyx]
      _ = t * (g * y * g⁻¹) := by rw [← hgx]; group
  have hMp : ⁅M, M⁆ = M := by
    rw [hM, ← map_commutator, commutator_eq_self_of_simple hLs hLnab]
  have hML : M ≤ L := h.le_of_perfect_of_card_sylow hS2 hMt hMp
  refine h.exists_normalizer_szA₁_conj_of_card_sylow hS2 (fun a ha => (hxA₁ a ha).symm)
    fun a ha => mem_sup_left (hML ⟨a, hA₁Lx ha, rfl⟩)

section Certificates



theorem inf_szR_le_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) : T ⊓ szR (szT₁ L T) R₂ t ≤ szT₁ L T ⊔ zpowers t := by
  obtain ⟨-, -, -, -, -, hTH⟩ := h.s₁_facts_of_card_sylow hS2 hR
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  intro x hx
  obtain ⟨hxT, hxR⟩ := mem_inf.mp hx
  obtain ⟨w, hw, z, hz, rfl⟩ := exists_mul_of_mem_szR hR hxR
  have hzT : z ∈ T := zpowers_le.mpr htT hz
  have hwT : w ∈ T := by
    have := mul_mem hxT (inv_mem hzT)
    rwa [mul_inv_cancel_right] at this
  exact mul_mem (mem_sup_left (hTH ⟨hwT, hw⟩)) (mem_sup_right hz)

theorem exists_sq_mem_szT₁_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {x : G} (hx : x ∈ T ⊔ R₂)
    (hx2 : x ^ 2 ∈ szT₁ L T ⊔ R₂) :
    ∃ s ∈ T, ∃ r ∈ szR (szT₁ L T) R₂ t, s * r = x ∧ s ^ 2 ∈ szT₁ L T := by
  obtain ⟨-, -, -, -, hS₁H, hTH⟩ := h.s₁_facts_of_card_sylow hS2 hR
  obtain ⟨s, hs, r, hr, rfl⟩ := h.exists_mul_of_mem_s₁_of_card_sylow hS2 hR hx
  refine ⟨s, hs, r, hr, rfl, ?_⟩
  obtain ⟨w, hw, z, hz, rfl⟩ := exists_mul_of_mem_szR hR hr
  have hsz : s * z = z * s := commute_of_mem_zpowers hz (mem_centralizer_singleton_iff.mp (h.le hs))
  have hzz : z * z = 1 := by
    rcases mem_zpowers_involution_eq_one_or_eq hR.t_sq hz with hz1 | hz1
    · rw [hz1, mul_one]
    · rw [hz1, ← sq, hR.t_sq]
  have hw1 : s⁻¹ * w * s ∈ szT₁ L T ⊔ R₂ :=
    (mem_normalizer_iff''.mp (hS₁H (mem_sup_left hs)) w).mp hw
  have hw2 : z * w * z⁻¹ ∈ szT₁ L T ⊔ R₂ :=
    (mem_normalizer_iff.mp (zpowers_le.mpr hR.t_mem_normalizer_sup hz) w).mp hw
  have e : (s * (w * z)) ^ 2 = s ^ 2 * ((s⁻¹ * w * s) * (z * w * z⁻¹)) := by
    calc (s * (w * z)) ^ 2 = s * w * (z * s) * w * z := by rw [sq]; group
      _ = s * w * (s * z) * w * z := by rw [hsz]
      _ = s ^ 2 * ((s⁻¹ * w * s) * (z * w * z⁻¹)) * (z * z) := by rw [sq]; group
      _ = s ^ 2 * ((s⁻¹ * w * s) * (z * w * z⁻¹)) := by rw [hzz, mul_one]
  refine hTH ⟨pow_mem hs 2, ?_⟩
  have := mul_mem hx2 (inv_mem (mul_mem hw1 hw2))
  rwa [e, mul_inv_cancel_right] at this

theorem conj_mem_of_mem_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f)
    (hcl : ∀ g ∈ normalizer (szA₁ (szT₁ L T) : Set G), g⁻¹ * t * g ∈ T ⊔ R₂ →
      g⁻¹ * t * g ∈ szR (szT₁ L T) R₂ t)
    {g : G} (hxT : g⁻¹ * t * g ∈ T) : g⁻¹ * t * g ∈ szT₁ L T ⊔ zpowers t := by
  by_contra hxS
  obtain ⟨g', hg'N, hg't⟩ := h.exists_normalizer_szA₁_conj_of_outer_of_card_sylow hS2 hxT hxS
  have h1 := hcl g' hg'N (by rw [hg't]; exact mem_sup_left hxT)
  rw [hg't] at h1
  exact hxS (h.inf_szR_le_of_card_sylow hS2 hR (mem_inf.mpr ⟨hxT, h1⟩))

theorem conj_ne_mul_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f)
    (hcl : ∀ g ∈ normalizer (szA₁ (szT₁ L T) : Set G), g⁻¹ * t * g ∈ T ⊔ R₂ →
      g⁻¹ * t * g ∈ szR (szT₁ L T) R₂ t)
    {v : G} (hvT : v ∈ T) (hv2 : v ^ 2 = 1) (hvS : v ∉ szT₁ L T ⊔ zpowers t)
    {w : G} (hw2 : w ^ 2 = 1) (hwt : w ∈ centralizer ({t} : Set G))
    (hwout : ¬ ∃ l ∈ L, ∀ x ∈ L, w * x * w⁻¹ = l * x * l⁻¹) :
    ∀ c ∈ centralizer ({w} : Set G), c * t * c⁻¹ ≠ t * w := by
  intro c hc hct
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  have hvout := (h.outer_facts_of_card_sylow hS2 hvT hv2 hvS).1
  obtain ⟨c₀, hc₀, hc₀w⟩ := h.outer_involution_conj_of_card_sylow hS2 hvT hv2 hvout hw2 hwt hwout
  have hc₀t : c₀ * t = t * c₀ := mem_centralizer_singleton_iff.mp hc₀
  have key : (c₀ * c)⁻¹⁻¹ * t * (c₀ * c)⁻¹ = t * (c₀ * w * c₀⁻¹) := by
    calc (c₀ * c)⁻¹⁻¹ * t * (c₀ * c)⁻¹ = c₀ * (c * t * c⁻¹) * c₀⁻¹ := by group
      _ = c₀ * (t * w) * c₀⁻¹ := by rw [hct]
      _ = (c₀ * t) * w * c₀⁻¹ := by group
      _ = t * (c₀ * w * c₀⁻¹) := by rw [hc₀t]; group
  have htv : t * v ∉ szT₁ L T ⊔ zpowers t := fun h1 => hvS (by
    have := mul_mem (mem_sup_right (inv_mem (mem_zpowers t))) h1
    rwa [inv_mul_cancel_left] at this)
  rcases hc₀w with h1 | h1
  · rw [h1] at key
    exact htv (key ▸ h.conj_mem_of_mem_of_card_sylow hS2 hR hcl (key ▸ mul_mem htT hvT))
  · rw [h1, ← mul_assoc, ← sq, h.sq_eq_one, one_mul] at key
    exact hvS (key ▸ h.conj_mem_of_mem_of_card_sylow hS2 hR hcl (key ▸ hvT))


theorem mem_sup_zpowers_conj_of_star_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hstar : StarPrimeStatement f)
    (hS : ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ R₂)
    (hcl : ∀ g ∈ normalizer (szA₁ (szT₁ L T) : Set G), g⁻¹ * t * g ∈ T ⊔ R₂ →
      g⁻¹ * t * g ∈ szR (szT₁ L T) R₂ t)
    {v : G} (hvT : v ∈ T) (hv2 : v ^ 2 = 1) (hvS : v ∉ szT₁ L T ⊔ zpowers t)
    {g : G} (hA : ∀ a ∈ szA₁ (szT₁ L T), a * (g⁻¹ * t * g) = g⁻¹ * t * g * a) :
    ∀ a ∈ szA₁ (szT₁ L T), g * a * g⁻¹ ∈ L ⊔ zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro a ha
  obtain ⟨-, -, -, -, -, hA₁sq, -⟩ := h.facts_of_card_sylow hS2
  have hst := h.setting.standardSetting
  have hHN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hst.standard
      h.mem h.inv).1
  have hCH : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t :=
    inf_centralizer_eq_zpowers_of_card_sylow_eq_two hst.standard hS2 h.mem h.inv
      (hst.core t h.inv)
  set a' := g * a * g⁻¹ with ha'
  have hct : a' * t = t * a' := by
    have e := hA a ha
    calc a' * t = g * (a * (g⁻¹ * t * g)) * g⁻¹ := by rw [ha']; group
      _ = g * ((g⁻¹ * t * g) * a) * g⁻¹ := by rw [e]
      _ = t * a' := by rw [ha']; group
  have hsq : a' ^ 2 = 1 := by
    calc a' ^ 2 = g * a ^ 2 * g⁻¹ := by rw [ha', sq, sq]; group
      _ = 1 := by rw [hA₁sq a ha]; group
  by_cases hinn : ∃ l ∈ L, ∀ y ∈ L, a' * y * a'⁻¹ = l * y * l⁻¹
  · obtain ⟨l, hl, hly⟩ := hinn
    have hlt : l * t = t * l := mem_centralizer_iff.mp h.mem l hl
    have hk : l⁻¹ * a' ∈ zpowers t := by
      rw [← hCH]
      refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun y hy => ?_, ?_⟩
      · calc y * (l⁻¹ * a') = l⁻¹ * (l * y * l⁻¹) * a' := by group
          _ = l⁻¹ * (a' * y * a'⁻¹) * a' := by rw [hly y hy]
          _ = l⁻¹ * a' * y := by group
      · rw [mem_centralizer_singleton_iff]
        have hlt' : l⁻¹ * t = t * l⁻¹ := by
          calc l⁻¹ * t = l⁻¹ * (t * l) * l⁻¹ := by group
            _ = l⁻¹ * (l * t) * l⁻¹ := by rw [hlt]
            _ = t * l⁻¹ := by group
        calc l⁻¹ * a' * t = l⁻¹ * (a' * t) := by rw [mul_assoc]
          _ = l⁻¹ * (t * a') := by rw [hct]
          _ = (l⁻¹ * t) * a' := by rw [mul_assoc]
          _ = (t * l⁻¹) * a' := by rw [hlt']
          _ = t * (l⁻¹ * a') := by rw [mul_assoc]
    have := mul_mem (mem_sup_left hl : l ∈ L ⊔ zpowers t) (mem_sup_right hk)
    rwa [mul_inv_cancel_left] at this
  · exfalso
    obtain ⟨hR₁, hS₁N, -, hR₁S₁, -, -⟩ := h.s₁_facts_of_card_sylow hS2 hR
    obtain ⟨S, hSeq⟩ := hS
    have ha1 : a' ≠ 1 := fun h1 => hinn ⟨1, one_mem _, fun y _ => by simp [h1]⟩
    have hao : orderOf a' = 2 := orderOf_eq_prime hsq ha1
    have hwt : a' ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr hct
    have hbound := hstar G L h.setting h.model hS2 t h.inv h.mem a' hao hct (hHN hwt) hinn
      (h.conj_ne_mul_of_card_sylow hS2 hR hcl hvT hv2 hvS hsq hwt hinn)
    set P := szR (szT₁ L T) R₂ t ⊔ zpowers v with hP
    have hvA₁ := (h.outer_facts_of_card_sylow hS2 hvT hv2 hvS).2.1
    have hPS : P ≤ T ⊔ R₂ := sup_le hR₁S₁ (zpowers_le.mpr (mem_sup_left hvT))
    have hPp : IsPGroup 2 P := (hSeq ▸ S.isPGroup').to_le hPS
    have hPa : P ≤ centralizer ({a} : Set G) := by
      refine sup_le (fun r hr => ?_) (zpowers_le.mpr ?_)
      · rw [hR₁] at hr
        exact mem_centralizer_singleton_iff.mpr
          ((mem_centralizer_iff.mp hr.2.1 a ha).symm)
      · exact mem_centralizer_singleton_iff.mpr (hvA₁ a ha)
    have hvN : zpowers v ≤ normalizer (szR (szT₁ L T) R₂ t : Set G) :=
      zpowers_le.mpr (hS₁N (mem_sup_left hvT))
    have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hvN
    have hinf : zpowers v ⊓ szR (szT₁ L T) R₂ t = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨hyv, hyR⟩ := mem_inf.mp hy
      rcases mem_zpowers_involution_eq_one_or_eq hv2 hyv with rfl | rfl
      · exact one_mem _
      · exact absurd (h.inf_szR_le_of_card_sylow hS2 hR (mem_inf.mpr ⟨hvT, hyR⟩)) hvS
    have hv1 : v ≠ 1 := fun h1 => hvS (h1 ▸ one_mem _)
    rw [hinf, card_bot, mul_one, Nat.card_zpowers, orderOf_eq_prime hv2 hv1, sup_comm, hR₁,
      h.card_u3R₁_of_card_sylow hS2] at hprod
    have hcardP : 4 * (2 ^ f) ^ 4 ≤ Nat.card P := by
      have e : Nat.card P = 2 * (2 * (2 ^ f) ^ 4) := by rw [hP, hR₁]; exact hprod
      rw [e]
      exact le_of_eq (by ring)
    exact conj_ne_of_card_le hPp hPa hcardP hbound g rfl

theorem false_of_conj_mem_sup_of_weakClosed_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hS : ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ R₂)
    (hwc : ∀ k ∈ normalizer (szA₁ (szT₁ L T) : Set G),
      (∀ r ∈ szR (szT₁ L T) R₂ t, k⁻¹ * r * k ∈ T ⊔ R₂) →
        ∀ r ∈ szR (szT₁ L T) R₂ t, k⁻¹ * r * k ∈ szR (szT₁ L T) R₂ t)
    {g' : G} (hg'N : g' ∈ normalizer (szA₁ (szT₁ L T) : Set G))
    (hx : g'⁻¹ * t * g' ∈ szT₁ L T ⊔ R₂) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hR₁, -, hS₁A₁, hR₁S₁, -, hTH⟩ := h.s₁_facts_of_card_sylow hS2 hR
  obtain ⟨htT, -, -, -, hdisj, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨S, hSeq⟩ := hS
  have hSsyl : IsSylowOf 2 (T ⊔ R₂) ⊤ := by
    refine isSylowOf_iff.mpr ⟨le_top, hSeq ▸ S.isPGroup', ?_⟩
    rw [relIndex_top_right, ← hSeq]
    exact S.not_dvd_index
  have hcomm : ∀ r ∈ szR (szT₁ L T) R₂ t, ∀ r' ∈ szR (szT₁ L T) R₂ t,
      r * r' * r⁻¹ * r'⁻¹ ∈ szA₁ (szT₁ L T) := by
    rw [hR₁]
    intro r hr r' hr'
    exact h.comm_mem_szA₁_of_mem_u3R₁_of_card_sylow hS2 hr hr'
  obtain ⟨n, hnN, hnx⟩ := exists_mem_normalizer_inv_mul_mem_of_weakClosed hSsyl hS₁A₁ hR₁S₁
    hcomm hwc (mem_szR_right _ _ _) hg'N (sup_le_szR _ _ _ hx)
  have hnt : n⁻¹ * t * n ∈ szT₁ L T ⊔ R₂ := by
    have e : n⁻¹ * t * n = (g'⁻¹ * t * g') * ((g'⁻¹ * t * g')⁻¹ * (n⁻¹ * t * n)) := by group
    rw [e]
    exact mul_mem hx (mem_sup_left (szA₁_le _ hnx))
  have hnH := (mem_inf.mp ((h.char_of_card_sylow hS2 hR).2.2.2 hnN)).1
  have htH : t ∈ szT₁ L T ⊔ R₂ := (mem_normalizer_iff''.mp hnH t).mpr hnt
  have h1 : t ∈ szT₁ L T ⊓ zpowers t := mem_inf.mpr ⟨hTH (mem_inf.mpr ⟨htT, htH⟩), mem_zpowers t⟩
  rw [hdisj, mem_bot] at h1
  have h2 := h.inv
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by norm_num)


theorem commutator_le_sup_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) : ⁅T ⊔ R₂, T ⊔ R₂⁆ ≤ szT₁ L T ⊔ R₂ := by
  obtain ⟨-, -, -, -, hS₁H, -⟩ := h.s₁_facts_of_card_sylow hS2 hR
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  have hTT := h.commutator_le_szT₁_of_card_sylow hS2
  have hdec : ∀ x ∈ T ⊔ R₂, ∃ u ∈ T, ∃ w ∈ szT₁ L T ⊔ R₂, u * w = x := by
    intro x hx
    obtain ⟨s, hs, r, hr, rfl⟩ := h.exists_mul_of_mem_s₁_of_card_sylow hS2 hR hx
    obtain ⟨w, hw, z, hz, rfl⟩ := exists_mul_of_mem_szR hR hr
    have hzT : z ∈ T := zpowers_le.mpr htT hz
    exact ⟨s * z, mul_mem hs hzT, z⁻¹ * w * z,
      (mem_normalizer_iff''.mp (zpowers_le.mpr hR.t_mem_normalizer_sup hz) w).mp hw, by group⟩
  have hconj : ∀ c ∈ T ⊔ R₂, ∀ w ∈ szT₁ L T ⊔ R₂, c * w * c⁻¹ ∈ szT₁ L T ⊔ R₂ :=
    fun c hc w hw => (mem_normalizer_iff.mp (hS₁H hc) w).mp hw
  have hconj' : ∀ c ∈ T ⊔ R₂, ∀ w ∈ szT₁ L T ⊔ R₂, c⁻¹ * w * c ∈ szT₁ L T ⊔ R₂ :=
    fun c hc w hw => (mem_normalizer_iff''.mp (hS₁H hc) w).mp hw
  rw [commutator_le]
  intro x hx y hy
  obtain ⟨u, hu, w, hw, rfl⟩ := hdec x hx
  obtain ⟨u', hu', w', hw', rfl⟩ := hdec y hy
  have huS : u ∈ T ⊔ R₂ := mem_sup_left hu
  have hu'S : u' ∈ T ⊔ R₂ := mem_sup_left hu'
  have hA := hconj' u' hu'S w hw
  have hB : u'⁻¹ * w * u' * w' * w⁻¹ ∈ szT₁ L T ⊔ R₂ := mul_mem (mul_mem hA hw') (inv_mem hw)
  have hC := hconj u huS _ hB
  have hD := hconj u' hu'S _ (mul_mem hC (inv_mem hw'))
  have huu' : ⁅u, u'⁆ ∈ szT₁ L T ⊔ R₂ :=
    mem_sup_left (hTT (commutator_mem_commutator hu hu'))
  have e : ⁅u * w, u' * w'⁆ =
      ⁅u, u'⁆ * (u' * (u * (u'⁻¹ * w * u' * w' * w⁻¹) * u⁻¹ * w'⁻¹) * u'⁻¹) := by
    rw [commutatorElement_def, commutatorElement_def]
    group
  rw [e]
  exact mul_mem huu' hD

theorem conj_mem_mul_of_star_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hstar : StarPrimeStatement f)
    (hclos : U3ClosureInput) (hS : ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ R₂)
    {v : G} (hvT : v ∈ T) (hv2 : v ^ 2 = 1) (hvS : v ∉ szT₁ L T ⊔ zpowers t)
    {g : G} (hx : g⁻¹ * t * g ∈ T ⊔ R₂) : t⁻¹ * (g⁻¹ * t * g) ∈ szT₁ L T ⊔ R₂ := by
  obtain ⟨hwc, hcl⟩ := hclos G L f t T R₂ h hS2 hR hS
  obtain ⟨hR₁, -, -, -, -, -⟩ := h.s₁_facts_of_card_sylow hS2 hR
  have hvA₁ := (h.outer_facts_of_card_sylow hS2 hvT hv2 hvS).2.1
  have hx2 : (g⁻¹ * t * g) ^ 2 = 1 := by
    rw [show (g⁻¹ * t * g) ^ 2 = g⁻¹ * t ^ 2 * g by rw [sq, sq]; group, h.sq_eq_one, mul_one,
      inv_mul_cancel]
  have hR₁A : ∀ r ∈ szR (szT₁ L T) R₂ t, ∀ a ∈ szA₁ (szT₁ L T), a * r = r * a := by
    intro r hr a ha
    rw [hR₁] at hr
    exact mem_centralizer_iff.mp hr.2.1 a ha
  have hcA : ∀ a ∈ szA₁ (szT₁ L T), a * (g⁻¹ * t * g) = g⁻¹ * t * g * a := by
    by_cases hxR : g⁻¹ * t * g ∈ szR (szT₁ L T) R₂ t
    · exact fun a ha => hR₁A _ hxR a ha
    obtain ⟨s, hs, r, hr, hsr, hs2⟩ :=
      h.exists_sq_mem_szT₁_of_card_sylow hS2 hR hx (by rw [hx2]; exact one_mem _)
    have hsS : s ∉ szT₁ L T ⊔ zpowers t := fun hsS => hxR (hsr ▸ mul_mem
      (sup_le (le_szR_left _ _ _) (zpowers_le.mpr (mem_szR_right _ _ _)) hsS) hr)
    have hsv := h.mul_inv_mem_of_sq_mem_of_card_sylow hS2 hs hvT (mem_sup_left hs2)
      (by rw [hv2]; exact one_mem _) hsS hvS
    have hAc := szA₁_le_centralizer_sup_zpowers h.mem_centralizer_szT₁
    intro a ha
    have h1 : a * (s * v⁻¹) = s * v⁻¹ * a := (mem_centralizer_iff.mp (hAc ha) _ hsv).symm
    have h2 : a * v = v * a := (hvA₁ a ha).symm
    have h3 := hR₁A r hr a ha
    rw [← hsr, show s = s * v⁻¹ * v by group]
    calc a * (s * v⁻¹ * v * r) = (a * (s * v⁻¹)) * v * r := by group
      _ = s * v⁻¹ * (a * v) * r := by rw [h1]; group
      _ = s * v⁻¹ * v * (a * r) := by rw [h2]; group
      _ = s * v⁻¹ * v * r * a := by rw [h3]; group
  obtain ⟨g', hg'N, hg't⟩ := h.exists_normalizer_szA₁_conj_of_card_sylow hS2 hcA
    (h.mem_sup_zpowers_conj_of_star_of_card_sylow hS2 hR hstar hS hcl hvT hv2 hvS hcA)
  have hxR : g⁻¹ * t * g ∈ szR (szT₁ L T) R₂ t := by
    rw [← hg't]
    exact hcl g' hg'N (by rw [hg't]; exact hx)
  obtain ⟨w, hw, z, hz, hwz⟩ := exists_mul_of_mem_szR hR hxR
  rcases mem_zpowers_involution_eq_one_or_eq hR.t_sq hz with hz1 | hz1
  · exfalso
    rw [hz1, mul_one] at hwz
    exact h.false_of_conj_mem_sup_of_weakClosed_of_card_sylow hS2 hR hS hwc hg'N
      (by rw [hg't, ← hwz]; exact hw)
  · rw [← hwz, hz1]
    have := (mem_normalizer_iff''.mp (zpowers_le.mpr hR.t_mem_normalizer_sup (mem_zpowers t)) w).mp
      hw
    rwa [show t⁻¹ * w * t = t⁻¹ * (w * t) by group] at this

theorem not_isSylow_S₁_of_outer_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hstar : StarPrimeStatement f) (hclos : U3ClosureInput)
    {v : G} (hvT : v ∈ T) (hv2 : v ^ 2 = 1) (hvS : v ∉ szT₁ L T ⊔ zpowers t) :
    ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ R₂ := by
  intro hS
  obtain ⟨S, hSeq⟩ := hS
  obtain ⟨-, -, -, -, hS₁H, hTH⟩ := h.s₁_facts_of_card_sylow hS2 hR
  obtain ⟨htT, -, -, -, hdisj, -, -⟩ := h.start_of_card_sylow hS2
  have hG : IsSimpleGroup G := h.setting.1
  obtain ⟨a₀, b₀, hab⟩ : ∃ a b : G, a * b ≠ b * a := h.setting.2.1
  have htH : t ∉ szT₁ L T ⊔ R₂ := by
    intro htH
    have h1 : t ∈ szT₁ L T ⊓ zpowers t :=
      mem_inf.mpr ⟨hTH (mem_inf.mpr ⟨htT, htH⟩), mem_zpowers t⟩
    rw [hdisj, mem_bot] at h1
    have h2 := h.inv
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hle : szT₁ L T ⊔ R₂ ≤ T ⊔ R₂ := sup_le_sup_right (szT₁_le_left L T) R₂
  have hindex : Nat.Coprime 2 (T ⊔ R₂).index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (hSeq ▸ S.not_dvd_index)
  have hnot := CFSG.Quasithin.generalized_thompson_transfer_two (H := T ⊔ R₂)
    (K := szT₁ L T ⊔ R₂) hindex
    ⟨hle, (normal_subgroupOf_iff_le_normalizer hle).mpr hS₁H⟩
    (h.commutator_le_sup_of_card_sylow hS2 hR) (mem_sup_left htT) htH h.inv
    (fun a ha => h.conj_mem_mul_of_star_of_card_sylow hS2 hR hstar hclos ⟨S, hSeq⟩ hvT hv2 hvS ha)
  apply hnot
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H := commutator G) with h1 | h1
  · exfalso
    apply hab
    have h2 := commutator_mem_commutator (mem_top a₀) (mem_top b₀)
    rw [← commutator_def, h1, mem_bot] at h2
    exact commutatorElement_eq_one_iff_mul_comm.mp h2
  · rw [h1]
    exact mem_top t

theorem not_isSylow_S₁_of_star_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hstar : StarPrimeStatement f) (hclos : U3ClosureInput)
    (hsplit : U3SplitInput) : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ R₂ := by
  by_cases hcyc : ∃ b ∈ T, ∀ s ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T
  · exact h.not_isSylow_S₁_of_isCyclic_of_card_sylow hS2 hR hcyc
  · obtain ⟨v, hvT, hv2, hvS⟩ := hsplit G L f t T h hS2 hcyc
    exact h.not_isSylow_S₁_of_outer_of_card_sylow hS2 hR hstar hclos hvT hv2 hvS

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
