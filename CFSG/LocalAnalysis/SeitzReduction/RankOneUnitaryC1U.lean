module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1Basic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1Untwist

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped commutatorElement

@[expose] def u3C1U {G : Type*} [Group G] (L T R₂ : Subgroup G) (t : G) : Subgroup G where
  carrier := {x | x ∈ normalizer (szR (szT₁ L T) R₂ t : Set G) ∧
    x ∈ centralizer (szA₁ (szT₁ L T) : Set G) ∧ x ∈ normalizer (szT₁ L T : Set G) ∧
    ∀ y ∈ szT₁ L T, y⁻¹ * (x * y * x⁻¹) ∈ szA₁ (szT₁ L T)}
  mul_mem' := by
    rintro x x' ⟨hxR, hxC, hxT, hx⟩ ⟨hx'R, hx'C, hx'T, hx'⟩
    refine ⟨mul_mem hxR hx'R, mul_mem hxC hx'C, mul_mem hxT hx'T, fun y hy => ?_⟩
    have e : y⁻¹ * (x * x' * y * (x * x')⁻¹) =
        (y⁻¹ * (x * y * x⁻¹)) * (x * (y⁻¹ * (x' * y * x'⁻¹)) * x⁻¹) := by group
    have h1 := hx' y hy
    have h2 : x * (y⁻¹ * (x' * y * x'⁻¹)) * x⁻¹ = y⁻¹ * (x' * y * x'⁻¹) := by
      rw [(mem_centralizer_iff.mp hxC _ h1).symm, mul_inv_cancel_right]
    rw [e, h2]
    exact mul_mem (hx y hy) h1
  one_mem' := ⟨one_mem _, one_mem _, one_mem _, fun y _ => by simp⟩
  inv_mem' := by
    rintro x ⟨hxR, hxC, hxT, hx⟩
    refine ⟨inv_mem hxR, inv_mem hxC, inv_mem hxT, fun y hy => ?_⟩
    have hy' : x⁻¹ * y * x ∈ szT₁ L T := (mem_normalizer_iff''.mp hxT y).mp hy
    have h1 := hx _ hy'
    rw [show x * (x⁻¹ * y * x) * x⁻¹ = y by group] at h1
    rw [show y⁻¹ * (x⁻¹ * y * x⁻¹⁻¹) = ((x⁻¹ * y * x)⁻¹ * y)⁻¹ by group]
    exact inv_mem h1

section General

variable {G : Type*} [Group G] {L T R₂ : Subgroup G} {t : G}

theorem u3C1U_le_normalizer : u3C1U L T R₂ t ≤ normalizer (szR (szT₁ L T) R₂ t : Set G) :=
  fun _ hx => hx.1

theorem conj_mem_u3C1U {y x : G} (hyR : y ∈ normalizer (szR (szT₁ L T) R₂ t : Set G))
    (hyT : y ∈ normalizer (szT₁ L T : Set G)) (hyA : y ∈ normalizer (szA₁ (szT₁ L T) : Set G))
    (hx : x ∈ u3C1U L T R₂ t) : y * x * y⁻¹ ∈ u3C1U L T R₂ t := by
  obtain ⟨hxR, hxC, hxT, hx⟩ := hx
  refine ⟨mul_mem (mul_mem hyR hxR) (inv_mem hyR), mem_centralizer_iff.mpr fun a ha => ?_,
    mul_mem (mul_mem hyT hxT) (inv_mem hyT), fun z hz => ?_⟩
  · have ha' : y⁻¹ * a * y ∈ szA₁ (szT₁ L T) := (mem_normalizer_iff''.mp hyA a).mp ha
    have h1 := mem_centralizer_iff.mp hxC _ ha'
    calc a * (y * x * y⁻¹) = y * ((y⁻¹ * a * y) * x) * y⁻¹ := by group
      _ = y * (x * (y⁻¹ * a * y)) * y⁻¹ := by rw [h1]
      _ = y * x * y⁻¹ * a := by group
  · have hz' : y⁻¹ * z * y ∈ szT₁ L T := (mem_normalizer_iff''.mp hyT z).mp hz
    have h1 := hx _ hz'
    have h2 : y * ((y⁻¹ * z * y)⁻¹ * (x * (y⁻¹ * z * y) * x⁻¹)) * y⁻¹ ∈ szA₁ (szT₁ L T) :=
      (mem_normalizer_iff.mp hyA _).mp h1
    rwa [show y * ((y⁻¹ * z * y)⁻¹ * (x * (y⁻¹ * z * y) * x⁻¹)) * y⁻¹ =
      z⁻¹ * (y * x * y⁻¹ * z * (y * x * y⁻¹)⁻¹) by group] at h2

theorem le_normalizer_u3C1U
    (hYT : normalizer (szR (szT₁ L T) R₂ t : Set G) ≤ normalizer (szT₁ L T : Set G))
    (hYA : normalizer (szR (szT₁ L T) R₂ t : Set G) ≤ normalizer (szA₁ (szT₁ L T) : Set G)) :
    normalizer (szR (szT₁ L T) R₂ t : Set G) ≤ normalizer (u3C1U L T R₂ t : Set G) := by
  intro y hy
  refine mem_normalizer_iff.mpr fun x => ⟨conj_mem_u3C1U hy (hYT hy) (hYA hy), fun hx => ?_⟩
  have := conj_mem_u3C1U (inv_mem hy) (hYT (inv_mem hy)) (hYA (inv_mem hy)) hx
  rwa [show y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x by group] at this

theorem u3C1U_inf_normalizer_le :
    u3C1U L T R₂ t ⊓ normalizer (szA L T t : Set G) ≤ u3R₁ L T t := by
  rintro x ⟨⟨-, hxC, hxT, hx⟩, hxA⟩
  exact ⟨hxA, hxC, hxT, hx⟩

end General

namespace U3R2

variable {G : Type} [Group G] [Finite G] {L T₁ R₂ : Subgroup G} {t : G} {f : ℕ}

theorem conj_mem_of_inv (hR : U3R2 G L T₁ R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) {x : G}
    (hxR : x ∈ normalizer (R₂ : Set G)) (hxA : ∀ b ∈ szA₁ T₁, x * b * x⁻¹ = b) {r : G}
    (hr : r ∈ R₂) : r⁻¹ * (x * r * x⁻¹) ∈ szA₁ T₁ := by
  have hxr : x * r * x⁻¹ ∈ R₂ := (mem_normalizer_iff.mp hxR r).mp hr
  refine hR.mem_szA₁_of_sq_eq_one_of_inv hinv (mul_mem (inv_mem hr) hxr) ?_
  have hc : Commute r⁻¹ (x * r * x⁻¹) := hR.comm _ (inv_mem hr) _ hxr
  rw [hc.mul_pow, show (x * r * x⁻¹) ^ 2 = x * r ^ 2 * x⁻¹ by rw [sq, sq]; group,
    hxA _ (hR.sq_mem r hr), inv_pow, inv_mul_cancel]

end U3R2

theorem exists_two_ne_one {G : Type*} [Group G] {A : Subgroup G} [Finite A]
    (h : 2 < Nat.card A) : ∃ b ∈ A, ∃ b' ∈ A, b ≠ 1 ∧ b' ≠ 1 ∧ b ≠ b' := by
  classical
  by_contra hcon
  push Not at hcon
  have hnt : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨b₀, hb₀⟩, hb₀1⟩ := exists_ne (1 : A)
  have hb₀1' : b₀ ≠ 1 := fun h1 => hb₀1 (Subtype.ext h1)
  have hinj : Function.Injective (fun x : A => decide ((x : G) = 1)) := by
    intro x y hxy
    simp only [decide_eq_decide] at hxy
    apply Subtype.ext
    by_cases hx : (x : G) = 1
    · rw [hx, hxy.mp hx]
    · have hy : (y : G) ≠ 1 := fun hy => hx (hxy.mpr hy)
      rw [hcon _ x.2 _ hb₀ hx hb₀1', hcon _ y.2 _ hb₀ hy hb₀1']
  have := Nat.card_le_card_of_injective _ hinj
  rw [show Nat.card Bool = 2 by simp] at this
  omega

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem szR_le_u3C1U (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) : szR (szT₁ L T) R₂ t ≤ u3C1U L T R₂ t := by
  obtain ⟨-, -, hA₁, -⟩ := h.facts_of_card_sylow hS2
  have hcen : ∀ x, (∀ y ∈ szT₁ L T, x * y = y * x) → x ∈ szR (szT₁ L T) R₂ t →
      x ∈ u3C1U L T R₂ t := by
    intro x hx hxR
    refine ⟨Subgroup.le_normalizer hxR, mem_centralizer_iff.mpr fun a ha =>
      (hx a (szA₁_le _ ha)).symm, ?_, fun y hy => ?_⟩
    · exact centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun y hy => (hx y hy).symm)
    · rw [show x * y * x⁻¹ = y by rw [hx y hy, mul_inv_cancel_right], inv_mul_cancel]
      exact one_mem _
  refine sup_le (sup_le (fun y hy => ⟨Subgroup.le_normalizer (le_szR_left _ _ _ hy),
    mem_centralizer_iff.mpr fun a ha => (mem_centralizer_iff.mp (mem_szA₁.mp ha).2 y hy).symm,
    Subgroup.le_normalizer hy, fun z hz => ?_⟩) fun r hr => hcen r
      (fun y hy => (hR.commT₁ y hy r hr).symm) (le_szR_mid _ _ _ hr)) (zpowers_le.mpr
        (hcen t (fun y hy => (hR.t_comm y hy).symm) (mem_szR_right _ _ _)))
  rw [hA₁, show z⁻¹ * (y * z * y⁻¹) = ⁅z⁻¹, y⁆ by rw [commutatorElement_def, inv_inv]; group]
  exact commutator_mem_commutator (inv_mem hz) hy

theorem u3C1U_inf_centralizer (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) :
    u3C1U L T R₂ t ⊓ centralizer ({t} : Set G) = szT₁ L T ⊔ zpowers t := by
  apply le_antisymm
  · rintro x ⟨hxU, hxt⟩
    have hxA : x ∈ normalizer (szA L T t : Set G) := by
      refine mem_normalizer_szA_of_conj_t_mem (b := 1)
        (centralizer_le_normalizer _ hxU.2.1) (one_mem _) ?_
      rw [mem_centralizer_singleton_iff.mp hxt, mul_inv_cancel_right, one_mul]
    rw [← h.u3R₁_inf_centralizer_of_card_sylow hS2]
    exact ⟨u3C1U_inf_normalizer_le ⟨hxU, hxA⟩, hxt⟩
  · refine le_inf ((sup_le (le_szR_left _ _ _) (zpowers_le.mpr (mem_szR_right _ _ _))).trans
      (h.szR_le_u3C1U hS2 hR)) (sup_le (fun y hy => ?_) (zpowers_le.mpr ?_))
    · exact mem_centralizer_singleton_iff.mpr (hR.t_comm y hy)
    · exact mem_centralizer_singleton_iff.mpr rfl

theorem card_le_mul_card_inf_normalizer_szA (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) {H : Subgroup G}
    (hH : H ≤ normalizer (szR (szT₁ L T) R₂ t : Set G))
    (hHA : H ≤ normalizer (szA₁ (szT₁ L T) : Set G)) :
    Nat.card H ≤ 2 ^ f * Nat.card (H ⊓ normalizer (szA L T t : Set G) : Subgroup G) ∧
      ((∀ r ∈ R₂, ∃ x ∈ H, x * t * x⁻¹ * (r * t)⁻¹ ∈ szA₁ (szT₁ L T)) →
        Nat.card H = 2 ^ f * Nat.card (H ⊓ normalizer (szA L T t : Set G) : Subgroup G)) := by
  classical
  obtain ⟨-, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  set N := H ⊓ normalizer (szA L T t : Set G) with hNdef
  set N' := N.subgroupOf H with hN'
  set A' := (szA₁ (szT₁ L T)).subgroupOf R₂ with hA'
  have hσ : ∀ x : H, (x : G) * t * (x : G)⁻¹ * t⁻¹ ∈ R₂ := by
    intro x
    obtain ⟨r, hr, hxt⟩ := h.exists_conj_t_eq_of_inv hS2 hR hinv (hH x.2)
    rw [hxt, mul_inv_cancel_right]
    exact hr
  let φ : H → R₂ ⧸ A' := fun x => ((⟨_, hσ x⟩ : R₂) : R₂ ⧸ A')
  have htA : ∀ a ∈ szA₁ (szT₁ L T), a * t = t * a := fun a ha => hR.t_comm a (szA₁_le _ ha)
  have key : ∀ x y : H, φ x = φ y ↔ x⁻¹ * y ∈ N' := by
    intro x y
    rw [QuotientGroup.eq, mem_subgroupOf, mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · intro ha
      set a := ((x : G) * t * (x : G)⁻¹ * t⁻¹)⁻¹ * ((y : G) * t * (y : G)⁻¹ * t⁻¹) with hadef
      refine mem_inf.mpr ⟨mul_mem (inv_mem x.2) y.2, ?_⟩
      have hb : (x : G)⁻¹ * a * x ∈ szA₁ (szT₁ L T) :=
        (mem_normalizer_iff''.mp (hHA x.2) a).mp ha
      refine mem_normalizer_szA_of_conj_t_mem (hHA (mul_mem (inv_mem x.2) y.2)) hb ?_
      have e1 : (y : G) * t * (y : G)⁻¹ = x * t * (x : G)⁻¹ * t⁻¹ * a * t := by
        rw [hadef]; group
      have e2 : t⁻¹ * a * t = a := by rw [mul_assoc, htA a ha, inv_mul_cancel_left]
      calc (x : G)⁻¹ * y * t * ((x : G)⁻¹ * y)⁻¹ = (x : G)⁻¹ * ((y : G) * t * (y : G)⁻¹) * x := by
            group
        _ = t * ((x : G)⁻¹ * (t⁻¹ * a * t) * x) := by rw [e1]; group
        _ = t * ((x : G)⁻¹ * a * x) := by rw [e2]
        _ = (x : G)⁻¹ * a * x * t := (htA _ hb).symm
    · rintro ⟨-, hnA⟩
      set n := (x : G)⁻¹ * y with hn
      obtain ⟨r, hr, hnt⟩ := h.exists_conj_t_eq_of_inv hS2 hR hinv
        (hH (mul_mem (inv_mem x.2) y.2))
      have hrt : r * t ∈ szA L T t := by
        rw [← hnt]; exact (mem_normalizer_iff.mp hnA t).mp (mem_sup_right (mem_zpowers t))
      obtain ⟨a, ha, z, hz, haz⟩ := exists_mul_eq_of_mem_sup_zpowers
        (centralizer_le (szA₁_le _) h.mem_centralizer_szT₁) hrt
      have hrA : r ∈ szA₁ (szT₁ L T) := by
        rcases mem_zpowers_involution_eq_one_or_eq hR.t_sq hz with hz1 | hz1
        · exfalso
          rw [hz1, mul_one] at haz
          apply h.t_not_mem_sup_of_card_sylow hS2 hR
          have : t = r⁻¹ * a := by rw [haz]; group
          rw [this]
          exact mul_mem (mem_sup_right (inv_mem hr)) (mem_sup_left (szA₁_le _ ha))
        · rw [hz1] at haz
          rw [mul_right_cancel haz] at ha
          exact ha
      have hxr : (x : G) * r * (x : G)⁻¹ ∈ szA₁ (szT₁ L T) :=
        (mem_normalizer_iff.mp (hHA x.2) r).mp hrA
      have hσx := hσ x
      have e : (y : G) * t * (y : G)⁻¹ * t⁻¹ =
          ((x : G) * r * (x : G)⁻¹) * ((x : G) * t * (x : G)⁻¹ * t⁻¹) := by
        have hy : (y : G) = x * n := by rw [hn]; group
        rw [hy, show (x : G) * n * t * ((x : G) * n)⁻¹ * t⁻¹ =
          x * (n * t * n⁻¹) * (x : G)⁻¹ * t⁻¹ by group, hnt]
        group
      rw [e]
      have hfin : ((x : G) * t * (x : G)⁻¹ * t⁻¹)⁻¹ *
          ((x : G) * r * (x : G)⁻¹ * ((x : G) * t * (x : G)⁻¹ * t⁻¹)) ∈ szA₁ (szT₁ L T) := by
        rw [hR.comm _ (hR.le hxr) _ hσx, inv_mul_cancel_left]; exact hxr
      simpa only [mul_assoc] using hfin
  let ψ : H ⧸ N' → R₂ ⧸ A' := Quotient.lift φ fun a b hab =>
    (key a b).mpr (QuotientGroup.leftRel_apply.mp hab)
  have hψ : Function.Injective ψ := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    exact QuotientGroup.eq.mpr ((key a b).mp hab)
  have h1 : N'.index ≤ Nat.card (R₂ ⧸ A') := Nat.card_le_card_of_injective ψ hψ
  have h2 : Nat.card (R₂ ⧸ A') = 2 ^ f := by
    have h3 := A'.card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hR.le).toEquiv, hA₁card, hR.card] at h3
    have h4 : 2 ^ f * A'.index = 2 ^ f * 2 ^ f := by rw [h3]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h4
  have h3 := N'.card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : N ≤ H)).toEquiv] at h3
  refine ⟨by rw [← h3, mul_comm]; exact Nat.mul_le_mul_right _ (h2 ▸ h1), fun htr => ?_⟩
  have hsurj : Function.Surjective ψ := by
    intro c
    induction c using QuotientGroup.induction_on with | H r => ?_
    obtain ⟨x, hx, hxt⟩ := htr r r.2
    refine ⟨(⟨x, hx⟩ : H), QuotientGroup.eq.mpr ?_⟩
    rw [mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hcomm : (x * t * x⁻¹ * (r * t)⁻¹) * (r : G) = (r : G) * (x * t * x⁻¹ * (r * t)⁻¹) :=
      hR.comm _ (hR.le hxt) _ r.2
    have e : (x * t * x⁻¹ * t⁻¹)⁻¹ * (r : G) = (x * t * x⁻¹ * (r * t)⁻¹)⁻¹ := by
      calc (x * t * x⁻¹ * t⁻¹)⁻¹ * (r : G) =
          ((x * t * x⁻¹ * (r * t)⁻¹) * (r : G))⁻¹ * (r : G) := by group
        _ = ((r : G) * (x * t * x⁻¹ * (r * t)⁻¹))⁻¹ * (r : G) := by rw [hcomm]
        _ = (x * t * x⁻¹ * (r * t)⁻¹)⁻¹ := by group
    change (x * t * x⁻¹ * t⁻¹)⁻¹ * (r : G) ∈ szA₁ (szT₁ L T)
    rw [e]
    exact inv_mem hxt
  have h4 : N'.index = 2 ^ f := by
    rw [← h2]
    exact Nat.card_eq_of_bijective ψ ⟨hψ, hsurj⟩
  rw [← h3, h4, mul_comm]

theorem exists_u3C1U_conj_of_transitive (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hne : ∃ r ∈ R₂, r ^ 2 ≠ 1) {E : Subgroup G}
    (hEY : E ≤ normalizer (szR (szT₁ L T) R₂ t : Set G))
    (hEn : normalizer (szR (szT₁ L T) R₂ t : Set G) ≤ normalizer (E : Set G))
    (hEA : E ≤ centralizer (szA₁ (szT₁ L T) : Set G))
    (htr : ∀ r ∈ R₂, ∃ x ∈ E, x * t * x⁻¹ * (r * t)⁻¹ ∈ szA₁ (szT₁ L T)) :
    ∀ r ∈ R₂, ∃ x ∈ u3C1U L T R₂ t, x * t * x⁻¹ * (r * t)⁻¹ ∈ szA₁ (szT₁ L T) := by
  classical
  obtain ⟨E', _, _, _, σ, hEcard, hσ, hfix, u, v, hc, hA₁u, -, -⟩ :=
    h.exists_rootCoords_scalar_of_card_sylow hS2
  have : Fintype E' := Fintype.ofFinite E'
  obtain ⟨-, hA₁card, -, -, -, -, -⟩ := h.facts_of_card_sylow hS2
  have hf1 : 1 ≤ f := by have := h.two_le; omega
  obtain ⟨μ₀, hμ₀⟩ : ∃ μ : E', σ μ ≠ μ := by
    by_contra hall
    push Not at hall
    have h1 : Nat.card {x : E' // σ x = x} = Nat.card E' :=
      Nat.card_congr (Equiv.subtypeUnivEquiv hall)
    rw [hfix, hEcard] at h1
    have h2 : 2 ^ f < (2 ^ f) ^ 2 := by
      have : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
      nlinarith
    omega
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    rw [hσ, hσ, ← pow_mul, ← sq]
    have h1 : x ^ Fintype.card E' = x := FiniteField.pow_card x
    rwa [← Nat.card_eq_fintype_card, hEcard] at h1
  obtain ⟨hYT, hYA⟩ := h.normalizer_szR_le_normalizer_szT₁_of_inv hS2 hR hinv hne
  obtain ⟨-, -, -, hNR₁⟩ := h.char_of_card_sylow hS2 hR
  have hYR : ∀ y ∈ normalizer (szR (szT₁ L T) R₂ t : Set G), y ∈ normalizer (R₂ : Set G) :=
    fun y hy => (mem_inf.mp (hNR₁ hy)).2
  have hXA : ∀ x ∈ E, ∀ a ∈ szA₁ (szT₁ L T), x * a * x⁻¹ = a := fun x hx a ha => by
    rw [← mem_centralizer_iff.mp (hEA hx) a ha, mul_inv_cancel_right]
  obtain ⟨d, hdt, hdR, hdT, hdtr⟩ := hR.torus
  have hdY : d ∈ normalizer (szR (szT₁ L T) R₂ t : Set G) := by
    refine mem_normalizer_of_forall_inv_mul_mul_mem fun x hx => ?_
    have hle : szR (szT₁ L T) R₂ t ≤
        (szR (szT₁ L T) R₂ t).comap (MulAut.conj d⁻¹).toMonoidHom := by
      show szT₁ L T ⊔ R₂ ⊔ zpowers t ≤ _
      refine sup_le (sup_le (fun y hy => ?_) (fun r hr => ?_)) (zpowers_le.mpr ?_)
      · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        exact le_szR_left _ _ _ ((mem_normalizer_iff''.mp hdT y).mp hy)
      · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        exact le_szR_mid _ _ _ ((mem_normalizer_iff''.mp hdR r).mp hr)
      · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
          show d⁻¹ * t * d = t by rw [mul_assoc, ← hdt, inv_mul_cancel_left]]
        exact mem_szR_right _ _ _
    have := hle hx
    rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at this
  have hsqne : ∀ r ∈ R₂, r ∉ szA₁ (szT₁ L T) → r ^ 2 ≠ 1 := fun r hr hrA h1 =>
    hrA (hR.mem_szA₁_of_sq_eq_one_of_inv hinv hr h1)
  have hdtr' : ∀ r ∈ R₂, r ∉ szA₁ (szT₁ L T) → ∀ r' ∈ R₂, r' ∉ szA₁ (szT₁ L T) →
      ∃ n : ℕ, (d ^ n * r * (d ^ n)⁻¹)⁻¹ * r' ∈ szA₁ (szT₁ L T) := by
    intro r hr hrA r' hr' hr'A
    obtain ⟨n, hn⟩ := hdtr _ (hR.sq_mem r' hr') _ (hR.sq_mem r hr) (hsqne r' hr' hr'A)
      (hsqne r hr hrA)
    have hrn : d ^ n * r * (d ^ n)⁻¹ ∈ R₂ := (mem_normalizer_iff.mp (pow_mem hdR n) r).mp hr
    refine ⟨n, hR.mem_szA₁_of_sq_eq_one_of_inv hinv (mul_mem (inv_mem hrn) hr') ?_⟩
    have hcomm : Commute (d ^ n * r * (d ^ n)⁻¹)⁻¹ r' := hR.comm _ (inv_mem hrn) _ hr'
    have h1 : r' ^ 2 = (d ^ n * r * (d ^ n)⁻¹) ^ 2 := by
      rw [show (d ^ n * r * (d ^ n)⁻¹) ^ 2 = d ^ n * r ^ 2 * (d ^ n)⁻¹ by rw [sq, sq]; group,
        ← hn]
      group
    rw [hcomm.mul_pow, h1, inv_pow, inv_mul_cancel]
  have hfour : ∃ r ∈ R₂, ∃ r' ∈ R₂, r ∉ szA₁ (szT₁ L T) ∧ r' ∉ szA₁ (szT₁ L T) ∧
      r⁻¹ * r' ∉ szA₁ (szT₁ L T) := by
    have h3 : 2 < Nat.card (szA₁ (szT₁ L T)) := by
      rw [hA₁card]
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
    obtain ⟨b, hb, b', hb', hb1, hb'1, hbb'⟩ := exists_two_ne_one h3
    obtain ⟨r, hr, rfl⟩ := hR.exists_sq_eq_of_inv hinv hb
    obtain ⟨r', hr', rfl⟩ := hR.exists_sq_eq_of_inv hinv hb'
    refine ⟨r, hr, r', hr', fun h1 => hb1 (hR.sq_A₁ r h1), fun h1 => hb'1 (hR.sq_A₁ r' h1),
      fun h1 => hbb' ?_⟩
    have h2 := hR.sq_A₁ _ h1
    have hcomm : Commute r⁻¹ r' := hR.comm _ (inv_mem hr) _ hr'
    rw [hcomm.mul_pow, inv_pow, inv_mul_eq_one] at h2
    exact h2
  intro r hr
  obtain ⟨x, hx, htriv, hxt⟩ := U3C1.exists_trivial_of_transitive hc hA₁u hμ₀ hσσ hσ
    (Nat.even_pow.mpr ⟨even_two, by omega⟩) (hEY.trans hYT) hXA hR.le hR.comm hR.sq_mem
    (fun x hx r hr => hR.conj_mem_of_inv hinv (hYR x (hEY hx)) (hXA x hx) hr) htr (hEn hdY)
    hdR (hYA hdY) hdt hdT hdtr' hfour r hr
  exact ⟨x, ⟨hEY hx, hEA hx, hYT (hEY hx), htriv⟩, hxt⟩

section Certificates

theorem u3C1U_inf_normalizer_szA (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) :
    u3C1U L T R₂ t ⊓ normalizer (szA L T t : Set G) = szR (szT₁ L T) R₂ t := by
  obtain ⟨hR₁, -, -, -, -, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  apply le_antisymm
  · rw [show szR (szT₁ L T) R₂ t = szT₁ L T ⊔ R₂ ⊔ zpowers t from rfl, hR₁]
    exact u3C1U_inf_normalizer_le
  · refine le_inf (h.szR_le_u3C1U hS2 hR) ?_
    rw [show szR (szT₁ L T) R₂ t = szT₁ L T ⊔ R₂ ⊔ zpowers t from rfl, hR₁]
    exact u3R₁_le_normalizer L T t

theorem card_u3C1U_of_transitive (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (htr : ∀ r ∈ R₂, ∃ x ∈ u3C1U L T R₂ t, x * t * x⁻¹ * (r * t)⁻¹ ∈ szA₁ (szT₁ L T)) :
    Nat.card (u3C1U L T R₂ t) = 2 * (2 ^ f) ^ 5 := by
  obtain ⟨hR₁, -, -, -, -, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  have h1 := (h.card_le_mul_card_inf_normalizer_szA hS2 hR hinv (H := u3C1U L T R₂ t)
    u3C1U_le_normalizer fun x hx => centralizer_le_normalizer _ hx.2.1).2 htr
  rw [h1, h.u3C1U_inf_normalizer_szA hS2 hR,
    show szR (szT₁ L T) R₂ t = szT₁ L T ⊔ R₂ ⊔ zpowers t from rfl, hR₁,
    h.card_u3R₁_of_card_sylow hS2]
  ring

theorem isSylowOf_u3C1U_of_transitive (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hne : ∃ r ∈ R₂, r ^ 2 ≠ 1) (hT : T ≤ szT₁ L T ⊔ zpowers t)
    (htr : ∀ r ∈ R₂, ∃ x ∈ u3C1U L T R₂ t, x * t * x⁻¹ * (r * t)⁻¹ ∈ szA₁ (szT₁ L T)) :
    CFSG.ABGLocalTools.IsSylowOf 2 (u3C1U L T R₂ t) (normalizer (szR (szT₁ L T) R₂ t : Set G)) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hR₁, -, -, -, -, hsyl⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  obtain ⟨-, hYA⟩ := h.normalizer_szR_le_normalizer_szT₁_of_inv hS2 hR hinv hne
  have hcard := h.card_u3C1U_of_transitive hS2 hR hinv htr
  have hU2 : IsPGroup 2 (u3C1U L T R₂ t) :=
    IsPGroup.of_card (n := 1 + f * 5) (by rw [hcard, pow_add, pow_mul, pow_one])
  obtain ⟨P, hP, hUP⟩ := exists_isSylowOf_le_of_isPGroup u3C1U_le_normalizer hU2
  have hS₁le : T ⊔ R₂ ≤ szR (szT₁ L T) R₂ t :=
    sup_le (hT.trans (sup_le (le_szR_left _ _ _) (zpowers_le.mpr (mem_szR_right _ _ _))))
      (le_szR_mid _ _ _)
  have hS₁card : Nat.card (T ⊔ R₂ : Subgroup G) ≤ 2 * (2 ^ f) ^ 4 := by
    have := Subgroup.card_le_of_le hS₁le
    rwa [show szR (szT₁ L T) R₂ t = szT₁ L T ⊔ R₂ ⊔ zpowers t from rfl, hR₁,
      h.card_u3R₁_of_card_sylow hS2] at this
  have hPA2 : IsPGroup 2 (P ⊓ normalizer (szA L T t : Set G) : Subgroup G) :=
    hP.isPGroup.to_le inf_le_left
  obtain ⟨a, -, ha⟩ := exists_conj_mem_of_isSylowOf hsyl inf_le_right hPA2
  have hPAcard : Nat.card (P ⊓ normalizer (szA L T t : Set G) : Subgroup G) ≤ 2 * (2 ^ f) ^ 4 := by
    have hle : (P ⊓ normalizer (szA L T t : Set G)).map (MulAut.conj a⁻¹).toMonoidHom ≤
        T ⊔ R₂ := by
      rintro _ ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply] using ha x hx
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective (MulAut.conj a⁻¹).injective] at h1
    exact h1.trans hS₁card
  have hPcard := (h.card_le_mul_card_inf_normalizer_szA hS2 hR hinv (H := P) hP.le
    (hP.le.trans hYA)).1
  have hle : Nat.card P ≤ Nat.card (u3C1U L T R₂ t) := by
    rw [hcard]
    calc Nat.card P ≤ 2 ^ f * (2 * (2 ^ f) ^ 4) := hPcard.trans (Nat.mul_le_mul_left _ hPAcard)
      _ = 2 * (2 ^ f) ^ 5 := by ring
  have heq : u3C1U L T R₂ t = P := Subgroup.eq_of_le_of_card_ge hUP hle
  rw [heq]
  exact hP

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
