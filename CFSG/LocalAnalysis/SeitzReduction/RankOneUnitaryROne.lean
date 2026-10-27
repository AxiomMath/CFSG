module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRScalar
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRegular
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearPointKernelCentralizer

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis
open scoped commutatorElement

@[expose] def u3R₁ {G : Type*} [Group G] (L T : Subgroup G) (t : G) : Subgroup G where
  carrier := {x | x ∈ normalizer (szA L T t : Set G) ∧ x ∈ centralizer (szA₁ (szT₁ L T) : Set G) ∧
    x ∈ normalizer (szT₁ L T : Set G) ∧ ∀ y ∈ szT₁ L T, y⁻¹ * (x * y * x⁻¹) ∈ szA₁ (szT₁ L T)}
  mul_mem' := by
    rintro x x' ⟨hxA, hxC, hxT, hx⟩ ⟨hx'A, hx'C, hx'T, hx'⟩
    refine ⟨mul_mem hxA hx'A, mul_mem hxC hx'C, mul_mem hxT hx'T, fun y hy => ?_⟩
    have e : y⁻¹ * (x * x' * y * (x * x')⁻¹) =
        (y⁻¹ * (x * y * x⁻¹)) * (x * (y⁻¹ * (x' * y * x'⁻¹)) * x⁻¹) := by group
    have h1 := hx' y hy
    have h2 : x * (y⁻¹ * (x' * y * x'⁻¹)) * x⁻¹ = y⁻¹ * (x' * y * x'⁻¹) := by
      rw [(mem_centralizer_iff.mp hxC _ h1).symm, mul_inv_cancel_right]
    rw [e, h2]
    exact mul_mem (hx y hy) h1
  one_mem' := ⟨one_mem _, one_mem _, one_mem _, fun y _ => by
    rw [one_mul, inv_one, mul_one, inv_mul_cancel]
    exact one_mem _⟩
  inv_mem' := by
    rintro x ⟨hxA, hxC, hxT, hx⟩
    refine ⟨inv_mem hxA, inv_mem hxC, inv_mem hxT, fun y hy => ?_⟩
    have hy' : x⁻¹ * y * x ∈ szT₁ L T := by
      have := (mem_normalizer_iff.mp (inv_mem hxT) y).mp hy
      rwa [inv_inv] at this
    have e : y⁻¹ * (x⁻¹ * y * x⁻¹⁻¹) = ((x⁻¹ * y * x)⁻¹ * (x * (x⁻¹ * y * x) * x⁻¹))⁻¹ := by
      group
    rw [e]
    exact inv_mem (hx _ hy')

theorem u3R₁_le_normalizer {G : Type*} [Group G] (L T : Subgroup G) (t : G) :
    u3R₁ L T t ≤ normalizer (szA L T t : Set G) := fun _ hx => hx.1

theorem u3R₁_le_centralizer {G : Type*} [Group G] (L T : Subgroup G) (t : G) :
    u3R₁ L T t ≤ centralizer (szA₁ (szT₁ L T) : Set G) := fun _ hx => hx.2.1

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem conj_mem_u3R₁_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {n r : G}
    (hn : n ∈ normalizer (szA L T t : Set G)) (hr : r ∈ u3R₁ L T t) :
    n * r * n⁻¹ ∈ u3R₁ L T t := by
  obtain ⟨hNA₁, -, -⟩ := h.partition_of_card_sylow hS2
  have hnA₁ := hNA₁ hn
  have hnT := h.normalizer_szA_le_of_card_sylow hS2 hn
  obtain ⟨hrA, hrC, hrT, hr⟩ := hr
  refine ⟨mul_mem (mul_mem hn hrA) (inv_mem hn), mem_centralizer_iff.mpr fun a ha => ?_,
    mul_mem (mul_mem hnT hrT) (inv_mem hnT), fun y hy => ?_⟩
  · have ha' : n⁻¹ * a * n ∈ szA₁ (szT₁ L T) := by
      have := (mem_normalizer_iff.mp (inv_mem hnA₁) a).mp ha
      rwa [inv_inv] at this
    have hra := (mem_centralizer_iff.mp hrC _ ha').symm
    calc a * (n * r * n⁻¹) = n * ((n⁻¹ * a * n) * r) * n⁻¹ := by group
      _ = n * (r * (n⁻¹ * a * n)) * n⁻¹ := by rw [hra]
      _ = n * r * n⁻¹ * a := by group
  · have hy' : n⁻¹ * y * n ∈ szT₁ L T := by
      have := (mem_normalizer_iff.mp (inv_mem hnT) y).mp hy
      rwa [inv_inv] at this
    have h1 := (mem_normalizer_iff.mp hnA₁ _).mp (hr _ hy')
    have e : y⁻¹ * (n * r * n⁻¹ * y * (n * r * n⁻¹)⁻¹) =
        n * ((n⁻¹ * y * n)⁻¹ * (r * (n⁻¹ * y * n) * r⁻¹)) * n⁻¹ := by group
    rw [e]
    exact h1

theorem sup_le_u3R₁_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    szT₁ L T ⊔ zpowers t ≤ u3R₁ L T t := by
  obtain ⟨-, -, hAC, -⟩ := h.szA_facts_of_card_sylow hS2
  obtain ⟨-, -, hcomm, -⟩ := h.facts_of_card_sylow hS2
  have hT₁C : szT₁ L T ⊔ zpowers t ≤ normalizer (szA L T t : Set G) := by
    intro x hx
    refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun a ha => ?_)
    exact (mem_centralizer_iff.mp (hAC ha) x hx).symm
  have htT : t ∈ centralizer (szT₁ L T : Set G) := h.mem_centralizer_szT₁
  refine sup_le (fun y hy => ⟨hT₁C (mem_sup_left hy), ?_, Subgroup.le_normalizer hy, ?_⟩)
    (zpowers_le.mpr ⟨hT₁C (mem_sup_right (mem_zpowers t)), ?_,
      centralizer_le_normalizer _ htT, fun y hy => ?_⟩)
  · exact mem_centralizer_iff.mpr fun a ha =>
      (mem_centralizer_iff.mp (hAC (szA₁_le_szA L T t ha)) y (mem_sup_left hy)).symm
  · intro z hz
    rw [hcomm]
    have e : z⁻¹ * (y * z * y⁻¹) = ⁅z⁻¹, y⁆ := by rw [commutatorElement_def]; group
    rw [e]
    exact commutator_mem_commutator (inv_mem hz) hy
  · exact mem_centralizer_iff.mpr fun a ha =>
      (mem_centralizer_iff.mp (hAC (szA₁_le_szA L T t ha)) t (mem_sup_right (mem_zpowers t))).symm
  · rw [(mem_centralizer_iff.mp htT y hy).symm, mul_inv_cancel_right, inv_mul_cancel]
    exact one_mem _

theorem u3R₁_inf_centralizer_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    u3R₁ L T t ⊓ centralizer ({t} : Set G) = szT₁ L T ⊔ zpowers t := by
  apply le_antisymm
  · rintro r ⟨⟨-, hrC, -, hr⟩, hrt⟩
    have hrA : r ∈ centralizer (szA L T t : Set G) := by
      have hle : szA L T t ≤ centralizer ({r} : Set G) :=
        sup_le (fun a ha => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hrC a ha))
          (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
            (mem_centralizer_singleton_iff.mp hrt).symm))
      exact mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp (hle hx)
    exact h.mem_sup_of_forall_mem_szA₁_of_card_sylow hS2 hrA hr
  · refine le_inf (h.sup_le_u3R₁_of_card_sylow hS2) (sup_le ?_ ?_)
    · intro y hy
      exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp h.mem_centralizer_szT₁ y hy)
    · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)

omit [Finite G] in
theorem mem_u3R₁_pow_of_untwisted {E : Type*} [Field E] {σ : E →+* E} {u v : G → E}
    (hc : U3RootCoords (szT₁ L T) σ u v) (hA₁u : ∀ y ∈ szT₁ L T, (y ∈ szA₁ (szT₁ L T) ↔ u y = 0))
    (hσ : ∀ x, σ x = x ^ (2 ^ f)) (hf : 1 ≤ f) {x b : G}
    (hxA : x ∈ normalizer (szA L T t : Set G)) (hxC : x ∈ centralizer (szA₁ (szT₁ L T) : Set G))
    (hxT : x ∈ normalizer (szT₁ L T : Set G)) (hb : b ∈ szA₁ (szT₁ L T))
    (hxt : x * t * x⁻¹ = b * t) (hb2 : b ^ 2 = 1) {l : E} (hl : l * σ l = 1)
    (hlx : ∀ y ∈ szT₁ L T, u (x * y * x⁻¹) = l * u y) :
    x ^ (2 ^ f + 1) ∈ u3R₁ L T t ∧ x ^ (2 ^ f + 1) * t * (x ^ (2 ^ f + 1))⁻¹ = b * t := by
  have hl1 : l ^ (2 ^ f + 1) = 1 := by rw [pow_succ, mul_comm, ← hσ, hl]
  refine ⟨⟨pow_mem hxA _, pow_mem hxC _, pow_mem hxT _, fun y hy => ?_⟩, ?_⟩
  · have hz : x ^ (2 ^ f + 1) * y * (x ^ (2 ^ f + 1))⁻¹ ∈ szT₁ L T :=
      (mem_normalizer_iff.mp (pow_mem hxT _) y).mp hy
    refine (hA₁u _ (mul_mem (inv_mem hy) hz)).mpr ?_
    rw [hc.u_mul_inv hy hz, U3RootCoords.u_conj_pow hxT hlx _ y hy, hl1, one_mul, sub_self]
  ·
    have hx2 : x ^ 2 * t = t * x ^ 2 := by
      have hxb : x * b = b * x := (mem_centralizer_iff.mp hxC b hb).symm
      have h1 : x ^ 2 * t * (x ^ 2)⁻¹ = t := by
        calc x ^ 2 * t * (x ^ 2)⁻¹ = x * (x * t * x⁻¹) * x⁻¹ := by rw [sq]; group
          _ = x * (b * t) * x⁻¹ := by rw [hxt]
          _ = (x * b * x⁻¹) * (x * t * x⁻¹) := by group
          _ = b * (b * t) := by rw [hxb, mul_inv_cancel_right, hxt]
          _ = t := by rw [← mul_assoc, ← sq, hb2, one_mul]
      calc x ^ 2 * t = x ^ 2 * t * (x ^ 2)⁻¹ * x ^ 2 := by group
        _ = t * x ^ 2 := by rw [h1]
    have hpow : ∀ k : ℕ, (x ^ 2) ^ k * t = t * (x ^ 2) ^ k := fun k =>
      (Commute.pow_left hx2 k).eq
    obtain ⟨m, hm⟩ : ∃ m, 2 ^ f = 2 * m := ⟨2 ^ (f - 1), by
      rw [← pow_succ']
      congr 1
      omega⟩
    have e : x ^ (2 ^ f + 1) = x * (x ^ 2) ^ m := by
      rw [hm, ← pow_mul, ← pow_succ']
    rw [e]
    calc x * (x ^ 2) ^ m * t * (x * (x ^ 2) ^ m)⁻¹ =
        x * ((x ^ 2) ^ m * t) * ((x ^ 2) ^ m)⁻¹ * x⁻¹ := by group
      _ = x * t * x⁻¹ := by rw [hpow m]; group
      _ = b * t := hxt

section Certificates

theorem exists_u3R₁_conj_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∀ b ∈ szA₁ (szT₁ L T), ∃ r ∈ u3R₁ L T t, r * t * r⁻¹ = b * t := by
  classical
  obtain ⟨E, _, _, _, σ, hEcard, hσ, -, u, v, hc, hA₁u, hdich, -⟩ :=
    h.exists_rootCoords_scalar_of_card_sylow hS2
  have : Fintype E := Fintype.ofFinite E
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    rw [hσ, hσ, ← pow_mul, ← sq]
    have h1 : x ^ Fintype.card E = x := FiniteField.pow_card x
    rwa [← Nat.card_eq_fintype_card, hEcard] at h1
  have htr := h.forall_exists_conj_translation_of_card_sylow hS2
  have hNT₁ := h.normalizer_szA_le_of_card_sylow hS2
  have hD := h.partitionData_of_card_sylow hS2
  obtain ⟨-, hA₁card, -, -, -, hA₁sq, -⟩ := h.facts_of_card_sylow hS2
  have hf1 : 1 ≤ f := by have := h.two_le; omega
  set A₁ := szA₁ (szT₁ L T) with hA₁
  set S : Set G := {b | b ∈ A₁ ∧ ∃ r ∈ u3R₁ L T t, r * t * r⁻¹ = b * t} with hS
  have hunt : ∀ x ∈ normalizer (szA L T t : Set G) ⊓ centralizer (A₁ : Set G), ∀ b ∈ A₁,
      x * t * x⁻¹ = b * t → ∀ l : E, l * σ l = 1 →
        (∀ y ∈ szT₁ L T, u (x * y * x⁻¹) = l * u y) → b ∈ S := by
    intro x hx b hb hxt l hl hlx
    obtain ⟨hxA, hxC⟩ := mem_inf.mp hx
    obtain ⟨hr, hrt⟩ := mem_u3R₁_pow_of_untwisted hc hA₁u hσ hf1 hxA hxC (hNT₁ hxA) hb hxt
      (hA₁sq b hb) hl hlx
    exact ⟨hb, _, hr, hrt⟩
  have hSmul : ∀ b ∈ S, ∀ b' ∈ S, b' * b ∈ S := by
    rintro b ⟨hb, r, hr, hrt⟩ b' ⟨hb', r', hr', hr't⟩
    refine ⟨mul_mem hb' hb, r * r', mul_mem hr hr', ?_⟩
    have hrb' : r * b' = b' * r := (mem_centralizer_iff.mp (u3R₁_le_centralizer L T t hr) b' hb').symm
    calc r * r' * t * (r * r')⁻¹ = r * (r' * t * r'⁻¹) * r⁻¹ := by group
      _ = r * b' * r⁻¹ * (r * t * r⁻¹) := by rw [hr't]; group
      _ = b' * b * t := by rw [hrb', mul_inv_cancel_right, hrt, mul_assoc]
  have htw : ∀ x ∈ normalizer (szA L T t : Set G) ⊓ centralizer (A₁ : Set G),
      ∀ x' ∈ normalizer (szA L T t : Set G) ⊓ centralizer (A₁ : Set G), ∀ b ∈ A₁, ∀ b' ∈ A₁,
      x * t * x⁻¹ = b * t → x' * t * x'⁻¹ = b' * t → ∀ l l' : E, l * σ l = 1 → l' * σ l' = 1 →
      (∀ y ∈ szT₁ L T, u (x * y * x⁻¹) = l * σ (u y)) →
      (∀ y ∈ szT₁ L T, u (x' * y * x'⁻¹) = l' * σ (u y)) → b' * b ∈ S := by
    intro x hx x' hx' b hb b' hb' hxt hx't l l' hl hl' hlx hl'x
    have hxx' : x * x' ∈ normalizer (szA L T t : Set G) ⊓ centralizer (A₁ : Set G) :=
      mul_mem hx hx'
    have hxb' : x * b' = b' * x := (mem_centralizer_iff.mp (mem_inf.mp hx).2 b' hb').symm
    refine hunt _ hxx' _ (mul_mem hb' hb) ?_ (l * σ l') ?_ fun y hy => ?_
    · calc x * x' * t * (x * x')⁻¹ = x * (x' * t * x'⁻¹) * x⁻¹ := by group
        _ = x * b' * x⁻¹ * (x * t * x⁻¹) := by rw [hx't]; group
        _ = b' * b * t := by rw [hxb', mul_inv_cancel_right, hxt, mul_assoc]
    · rw [map_mul, hσσ]
      calc l * σ l' * (σ l * l') = (l * σ l) * (l' * σ l') := by ring
        _ = 1 := by rw [hl, hl', one_mul]
    · have hz : x' * y * x'⁻¹ ∈ szT₁ L T :=
        (mem_normalizer_iff.mp (hNT₁ (mem_inf.mp hx').1) y).mp hy
      have e : x * x' * y * (x * x')⁻¹ = x * (x' * y * x'⁻¹) * x⁻¹ := by group
      rw [e, hlx _ hz, hl'x y hy, map_mul, hσσ]
      ring
  have hScart : ∀ s ∈ S, s ≠ 1 → ∀ b ∈ A₁, b ∈ S := by
    rintro s ⟨hs, r, hr, hrt⟩ hs1 b hb
    by_cases hb1 : b = 1
    · exact ⟨hb, 1, one_mem _, by rw [hb1]; group⟩
    obtain ⟨x, hxN, hxt, hxs⟩ := hD.torus s hs b hb hs1 hb1
    have hxA : x ∈ normalizer (szA L T t : Set G) :=
      SzPartition.mem_normalizer_sup_zpowers hD.mem_centralizer hxN hxt
    refine ⟨hb, x * r * x⁻¹, h.conj_mem_u3R₁_of_card_sylow hS2 hxA hr, ?_⟩
    have hxt' : x * t * x⁻¹ = t := by rw [hxt, mul_inv_cancel_right]
    have hxt'' : x⁻¹ * t * x = t := by
      rw [mul_assoc, ← hxt, ← mul_assoc, inv_mul_cancel, one_mul]
    calc x * r * x⁻¹ * t * (x * r * x⁻¹)⁻¹ = x * (r * (x⁻¹ * t * x) * r⁻¹) * x⁻¹ := by group
      _ = x * (r * t * r⁻¹) * x⁻¹ := by rw [hxt'']
      _ = x * (s * t) * x⁻¹ := by rw [hrt]
      _ = x * s * x⁻¹ * (x * t * x⁻¹) := by group
      _ = b * t := by rw [hxs, hxt']
  by_contra hno
  push Not at hno
  have hnotS : ∀ b ∈ A₁, b ≠ 1 → b ∉ S := by
    intro b hb hb1 hbS
    obtain ⟨b₀, hb₀, hb₀r⟩ := hno
    exact hb₀r _ (hScart b hbS hb1 b₀ hb₀).2.choose_spec.1 (hScart b hbS hb1 b₀ hb₀).2.choose_spec.2
  have htwisted : ∀ b ∈ A₁, b ≠ 1 → ∃ x ∈ normalizer (szA L T t : Set G) ⊓
      centralizer (A₁ : Set G), x * t * x⁻¹ = b * t ∧ ∃ l : E, l * σ l = 1 ∧
        ∀ y ∈ szT₁ L T, u (x * y * x⁻¹) = l * σ (u y) := by
    intro b hb hb1
    obtain ⟨x, hx, hxt⟩ := htr b hb
    obtain ⟨l, hl, hlx | hlx⟩ := hdich x hx
    · exact absurd (hunt x hx b hb hxt l hl hlx) (hnotS b hb hb1)
    · exact ⟨x, hx, hxt, l, hl, hlx⟩
  obtain ⟨b₁, hb₁, hb₁1⟩ : ∃ b ∈ A₁, b ≠ 1 := by
    by_contra hall
    push Not at hall
    have : A₁ = ⊥ := eq_bot_iff.mpr fun x hx => (mem_bot).mpr (hall x hx)
    rw [this, card_bot] at hA₁card
    have : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
    omega
  obtain ⟨b₂, hb₂, hb₂1, hb₂b₁⟩ : ∃ b ∈ A₁, b ≠ 1 ∧ b ≠ b₁ := by
    by_contra hall
    push Not at hall
    have hsub : (A₁ : Set G) ⊆ {1, b₁} := fun x hx => by
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (hall x hx hx1)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, show Nat.card (A₁ : Set G) = Nat.card A₁ from rfl, hA₁card] at h1
    have h2 := Set.ncard_insert_le (1 : G) ({b₁} : Set G)
    rw [Set.ncard_singleton] at h2
    have h3 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
    omega
  obtain ⟨x₁, hx₁, hx₁t, l₁, hl₁, hl₁x⟩ := htwisted b₁ hb₁ hb₁1
  obtain ⟨x₂, hx₂, hx₂t, l₂, hl₂, hl₂x⟩ := htwisted b₂ hb₂ hb₂1
  have hprod := htw x₁ hx₁ x₂ hx₂ b₁ hb₁ b₂ hb₂ hx₁t hx₂t l₁ l₂ hl₁ hl₂ hl₁x hl₂x
  have h1 : b₂ * b₁ ≠ 1 := by
    intro h1
    apply hb₂b₁
    have : b₂ = b₁⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this, inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hA₁sq b₁ hb₁)]
  exact hnotS _ (mul_mem hb₂ hb₁) h1 hprod

theorem card_u3R₁_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    Nat.card (u3R₁ L T t) = 2 * (2 ^ f) ^ 4 := by
  have hD := h.partitionData_of_card_sylow hS2
  obtain ⟨-, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨-, -, -, hAcomm⟩ := h.szA_facts_of_card_sylow hS2
  have hcov := h.exists_u3R₁_conj_of_card_sylow hS2
  set A₁ := szA₁ (szT₁ L T) with hA₁
  set R₁ := u3R₁ L T t with hR₁
  have hmem : ∀ r : R₁, (r : G) * t * (r : G)⁻¹ * t⁻¹ ∈ A₁ := by
    intro r
    obtain ⟨c, hc, hct⟩ := hD.exists_conj_t_eq (u3R₁_le_normalizer L T t r.2)
    rw [hct, mul_inv_cancel_right]
    exact hc
  let θ : R₁ →* A₁ := MonoidHom.mk' (fun r => ⟨(r : G) * t * (r : G)⁻¹ * t⁻¹, hmem r⟩)
    (fun r r' => by
      apply Subtype.ext
      have hrc : (r : G) * ((r' : G) * t * (r' : G)⁻¹ * t⁻¹) =
          ((r' : G) * t * (r' : G)⁻¹ * t⁻¹) * r :=
        (mem_centralizer_iff.mp (u3R₁_le_centralizer L T t r.2) _ (hmem r')).symm
      have hab := hAcomm _ (szA₁_le_szA L T t (hmem r)) _ (szA₁_le_szA L T t (hmem r'))
      change ((r : G) * r') * t * ((r : G) * r')⁻¹ * t⁻¹ =
        ((r : G) * t * (r : G)⁻¹ * t⁻¹) * ((r' : G) * t * (r' : G)⁻¹ * t⁻¹)
      rw [hab]
      calc ((r : G) * r') * t * ((r : G) * r')⁻¹ * t⁻¹ =
          (r : G) * ((r' : G) * t * (r' : G)⁻¹ * t⁻¹) * t * (r : G)⁻¹ * t⁻¹ := by group
        _ = ((r' : G) * t * (r' : G)⁻¹ * t⁻¹) * ((r : G) * t * (r : G)⁻¹ * t⁻¹) := by
          rw [hrc]; group)
  have hsurj : Function.Surjective θ := by
    rintro ⟨b, hb⟩
    obtain ⟨r, hr, hrt⟩ := hcov b hb
    refine ⟨⟨r, hr⟩, Subtype.ext ?_⟩
    change r * t * r⁻¹ * t⁻¹ = b
    rw [hrt, mul_inv_cancel_right]
  have hker : Nat.card θ.ker = Nat.card (szT₁ L T ⊔ zpowers t : Subgroup G) := by
    rw [← h.u3R₁_inf_centralizer_of_card_sylow hS2]
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨x.1.1, x.1.2, ?_⟩) ⟨?_, ?_⟩)
    · have h1 : (x.1 : G) * t * (x.1 : G)⁻¹ * t⁻¹ = 1 := congrArg Subtype.val x.2
      show (x.1 : G) ∈ centralizer ({t} : Set G)
      rw [mem_centralizer_singleton_iff]
      calc (x.1 : G) * t = (x.1 : G) * t * (x.1 : G)⁻¹ * t⁻¹ * (t * x.1) := by group
        _ = t * x.1 := by rw [h1, one_mul]
    · intro x y hxy
      exact Subtype.ext (Subtype.ext (Subtype.mk.inj hxy))
    · rintro ⟨y, hyR, hyt⟩
      refine ⟨⟨⟨y, hyR⟩, ?_⟩, rfl⟩
      apply Subtype.ext
      change y * t * y⁻¹ * t⁻¹ = 1
      rw [mem_centralizer_singleton_iff.mp hyt, mul_inv_cancel_right, mul_inv_cancel]
  have h1 := Subgroup.card_ker_mul_card_range θ
  rw [MonoidHom.range_eq_top.mpr hsurj, card_top, hker, h.card_szT₁_sup_of_card_sylow hS2,
    hA₁card] at h1
  rw [← h1]
  ring

theorem isPGroup_u3R₁_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    IsPGroup 2 (u3R₁ L T t) :=
  IsPGroup.of_card (n := 4 * f + 1) (by
    rw [h.card_u3R₁_of_card_sylow hS2, ← pow_mul, pow_succ]
    ring)

theorem isSylowOf_sup_u3R₁_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    CFSG.ABGLocalTools.IsSylowOf 2 (T ⊔ u3R₁ L T t) (normalizer (szA L T t : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (szA L T t : Set G) with hN
  set R₁ := u3R₁ L T t with hR₁
  have hTN : T ≤ N := fun x hx =>
    h.normalizer_le_normalizer_szA_of_card_sylow hS2 (Subgroup.le_normalizer hx)
  have hR₁N : R₁ ≤ N := u3R₁_le_normalizer L T t
  have hTnR : T ≤ normalizer (R₁ : Set G) := fun x hx => mem_normalizer_iff.mpr fun r =>
    ⟨fun hr => h.conj_mem_u3R₁_of_card_sylow hS2 (hTN hx) hr, fun hr => by
      have := h.conj_mem_u3R₁_of_card_sylow hS2 (inv_mem (hTN hx)) hr
      simpa [mul_assoc] using this⟩
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  have hinf : R₁ ⊓ T = szT₁ L T ⊔ zpowers t := by
    apply le_antisymm
    · rw [← h.u3R₁_inf_centralizer_of_card_sylow hS2]
      exact inf_le_inf_left _ h.le
    · exact le_inf (h.sup_le_u3R₁_of_card_sylow hS2)
        (sup_le (szT₁_le_left L T) (zpowers_le.mpr htT))
  have hcard := CFSG.ShultStronglyClosedTI.LinearChain.card_sup_mul_card_inf_of_le_normalizer hTnR
  rw [hinf, h.card_szT₁_sup_of_card_sylow hS2, h.card_u3R₁_of_card_sylow hS2] at hcard
  have hsup : Nat.card (T ⊔ R₁ : Subgroup G) = 2 ^ f * Nat.card T := by
    have hpos : 0 < 2 * (2 ^ f) ^ 3 := by positivity
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [sup_comm, hcard]
    ring
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer ({t} : Set G)) := by
    obtain ⟨P, hP⟩ := h.sylow
    exact ⟨P, by rw [hP, subgroupOf_map_subtype, inf_of_le_left h.le]⟩
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer ({t} : Set G) ⊓ N) :=
    hTsyl.of_le (le_inf h.le hTN) inf_le_left
  have hodd := (CFSG.ABGLocalTools.isSylowOf_iff.mp hS).2.2
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨sup_le hTN hR₁N, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp h.isPGroup
    exact IsPGroup.of_card (n := f + k) (by rw [hsup, hk, pow_add])
  · have e1 := Subgroup.relIndex_mul_card (H := T ⊔ R₁) (K := N)
    rw [inf_of_le_left (sup_le hTN hR₁N)] at e1
    have e2 := Subgroup.relIndex_mul_card (H := centralizer ({t} : Set G)) (K := N)
    rw [h.relIndex_centralizer_of_card_sylow hS2] at e2
    have e3 := Subgroup.relIndex_mul_card (H := T) (K := centralizer ({t} : Set G) ⊓ N)
    rw [inf_of_le_left (le_inf h.le hTN)] at e3
    have hrel : (T ⊔ R₁).relIndex N = T.relIndex (centralizer ({t} : Set G) ⊓ N) := by
      have hpos : 0 < 2 ^ f * Nat.card T := by
        have : 0 < Nat.card T := Nat.card_pos
        positivity
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc (T ⊔ R₁).relIndex N * (2 ^ f * Nat.card T) = Nat.card N := by rw [← hsup, e1]
        _ = 2 ^ f * Nat.card (centralizer ({t} : Set G) ⊓ N : Subgroup G) := e2.symm
        _ = T.relIndex (centralizer ({t} : Set G) ⊓ N) * (2 ^ f * Nat.card T) := by
          rw [← e3]
          ring
    rw [hrel]
    exact hodd

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
