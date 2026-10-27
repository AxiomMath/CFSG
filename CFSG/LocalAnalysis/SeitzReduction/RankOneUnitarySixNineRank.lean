module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineFourThree
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineRankBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def U3SixNineTorusInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ U₁ : Subgroup G),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f → U3U1Data G L f t T R₂ U₁ →
    ∃ ε ∈ normalizer (U₁ : Set G), ε * t = t * ε ∧ (orderOf ε).Prime ∧
      (∀ a ∈ U₁, ε * a * ε⁻¹ * a⁻¹ ∈ R₂ → a ∈ R₂) ∧
      ∀ x ∈ normalizer (U₁ : Set G) ⊓ centralizer (R₂ : Set G), x * t = t * x →
        Odd (orderOf x) → (¬ ∀ a ∈ U₁, x * a * x⁻¹ * a⁻¹ ∈ R₂) →
        (∀ a ∈ U₁, (x * ε * x⁻¹ * ε⁻¹) * a * (x * ε * x⁻¹ * ε⁻¹)⁻¹ * a⁻¹ ∈ R₂) →
        (∀ Y : Subgroup G, R₂ ≤ Y → Y ≤ szT₁ L T ⊔ R₂ → ε ∈ normalizer (Y : Set G) →
          x ∈ normalizer (Y : Set G) → Y = R₂ ∨ Y = szT₁ L T ⊔ R₂) ∧
        (∀ Y : Subgroup G, szT₁ L T ⊔ R₂ ≤ Y → Y ≤ U₁ → ε ∈ normalizer (Y : Set G) →
          x ∈ normalizer (Y : Set G) → Y = szT₁ L T ⊔ R₂ ∨ Y = U₁)

namespace SixNineRank

variable {G : Type*} [Group G]

theorem comm_mem_mul {U R : Subgroup G} {g h : G} (hgR : g ∈ normalizer (R : Set G))
    (hg : ∀ a ∈ U, g * a * g⁻¹ * a⁻¹ ∈ R) (hh : ∀ a ∈ U, h * a * h⁻¹ * a⁻¹ ∈ R) :
    ∀ a ∈ U, (g * h) * a * (g * h)⁻¹ * a⁻¹ ∈ R := by
  intro a ha
  have e : (g * h) * a * (g * h)⁻¹ * a⁻¹ =
      (g * (h * a * h⁻¹ * a⁻¹) * g⁻¹) * (g * a * g⁻¹ * a⁻¹) := by group
  rw [e]
  exact mul_mem ((mem_normalizer_iff.mp hgR _).mp (hh a ha)) (hg a ha)

theorem comm_mem_pow {U R : Subgroup G} {g : G} (hgR : g ∈ normalizer (R : Set G))
    (hg : ∀ a ∈ U, g * a * g⁻¹ * a⁻¹ ∈ R) (n : ℕ) :
    ∀ a ∈ U, g ^ n * a * (g ^ n)⁻¹ * a⁻¹ ∈ R := by
  induction n with
  | zero => intro a ha; simp
  | succ n ih =>
    rw [pow_succ']
    exact comm_mem_mul hgR hg ih

theorem comm_mem_of_sq {U R : Subgroup G} {g : G} (hgR : g ∈ normalizer (R : Set G))
    (hodd : Odd (orderOf g)) (hg : ∀ a ∈ U, g ^ 2 * a * (g ^ 2)⁻¹ * a⁻¹ ∈ R) :
    ∀ a ∈ U, g * a * g⁻¹ * a⁻¹ ∈ R := by
  obtain ⟨m, hm⟩ := hodd
  have hgm : g = (g ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf g + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [hgm]
  exact comm_mem_pow (pow_mem hgR 2) hg (m + 1)

theorem mem_of_mul_mem_swap {U R : Subgroup G}
    (hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ R) {p q r s : G} (hq : q ∈ U) (hr : r ∈ U)
    (hs : s ∈ U) (h : p * q * r * s ∈ R) : p * s * r * q ∈ R := by
  have e : p * s * r * q = (p * q * r * s) * (s⁻¹ * r⁻¹ * s⁻¹⁻¹ * r⁻¹⁻¹) *
      ((s * r)⁻¹ * q⁻¹ * (s * r)⁻¹⁻¹ * q⁻¹⁻¹) := by group
  rw [e]
  exact mul_mem (mul_mem h (hcomm _ (inv_mem hs) _ (inv_mem hr)))
    (hcomm _ (inv_mem (mul_mem hs hr)) _ (inv_mem hq))

end SixNineRank

namespace U3U1Data

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ U₁ : Subgroup G}

theorem mem_normalizer_szT₁_of_comm (hU : U3U1Data G L f t T R₂ U₁)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {x : G} (hx : x ∈ normalizer (U₁ : Set G))
    (hxt : x * t = t * x) : x ∈ normalizer (szT₁ L T : Set G) := by
  have key : ∀ g ∈ normalizer (U₁ : Set G), g * t = t * g →
      ∀ y ∈ szT₁ L T, g * y * g⁻¹ ∈ szT₁ L T := by
    intro g hg hgt y hy
    have hyU : y ∈ U₁ := hU.le (mem_sup_left hy)
    refine hU.mem_szT₁_of_commute hR ((mem_normalizer_iff.mp hg y).mp hyU) ?_
    have hc : Commute g t := hgt
    have hyc : Commute y t := hR.t_comm y hy
    exact ((hc.mul_left hyc).mul_left hc.inv_left).eq
  refine mem_normalizer_iff.mpr fun y => ⟨fun hy => key x hx hxt y hy, fun hy => ?_⟩
  have h1 := key x⁻¹ (inv_mem hx) (Commute.inv_left (show Commute x t from hxt)).eq _ hy
  rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at h1

theorem mem_normalizer_sup_of_comm (hU : U3U1Data G L f t T R₂ U₁)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {x : G} (hx : x ∈ normalizer (U₁ : Set G))
    (hxt : x * t = t * x) : x ∈ normalizer ((szT₁ L T ⊔ R₂ : Subgroup G) : Set G) := by
  have hxT := hU.mem_normalizer_szT₁_of_comm hR hx hxt
  have hxR := hU.normalizer_le_normalizer_R₂ hx
  rw [mem_normalizer_iff_map_conj_eq] at hxR hxT ⊢
  rw [Subgroup.map_sup, hxT, hxR]

theorem normalizer_le_normalizer_K (hU : U3U1Data G L f t T R₂ U₁) :
    normalizer (U₁ : Set G) ≤
      normalizer ((normalizer (U₁ : Set G) ⊓ centralizer (R₂ : Set G) : Subgroup G) : Set G) := by
  intro g hg
  refine mem_normalizer_iff.mpr fun x => ?_
  have hgR := hU.normalizer_le_normalizer_R₂ hg
  simp only [mem_inf]
  constructor
  · rintro ⟨hx1, hx2⟩
    refine ⟨mul_mem (mul_mem hg hx1) (inv_mem hg), mem_centralizer_iff.mpr fun r hr => ?_⟩
    have hr' : g⁻¹ * r * g ∈ R₂ := (mem_normalizer_iff''.mp hgR r).mp hr
    have := mem_centralizer_iff.mp hx2 _ hr'
    calc r * (g * x * g⁻¹) = g * ((g⁻¹ * r * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * r * g)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * r := by group
  · rintro ⟨hx1, hx2⟩
    refine ⟨?_, mem_centralizer_iff.mpr fun r hr => ?_⟩
    · have := mul_mem (mul_mem (inv_mem hg) hx1) hg
      simpa [mul_assoc] using this
    · have hr' : g * r * g⁻¹ ∈ R₂ := (mem_normalizer_iff.mp hgR r).mp hr
      have := mem_centralizer_iff.mp hx2 _ hr'
      calc r * x = g⁻¹ * ((g * r * g⁻¹) * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * (g * r * g⁻¹)) * g := by rw [this]
        _ = x * r := by group

theorem comm_t_mem_sup (hU : U3U1Data G L f t T R₂ U₁) (hR : U3R2 G L (szT₁ L T) R₂ t f)
    (htU : t ∈ normalizer (U₁ : Set G)) {a : G} (ha : a ∈ U₁) :
    a * t * a⁻¹ * t⁻¹ ∈ szT₁ L T ⊔ R₂ := by
  have htt : t * t = 1 := by rw [← sq, hR.t_sq]
  have htinv : t⁻¹ = t := hR.t_inv
  have hb : a * t * a⁻¹ * t⁻¹ ∈ U₁ := by
    have h1 : t * a⁻¹ * t⁻¹ ∈ U₁ := (mem_normalizer_iff.mp htU _).mp (inv_mem ha)
    have := mul_mem ha h1
    simpa [mul_assoc] using this
  refine hU.mem_sup_of_comm_mem hR htt hb ?_
  have h1 : t * (a * t * a⁻¹ * t⁻¹)⁻¹ * t⁻¹ = a * t * a⁻¹ * t⁻¹ := by
    calc t * (a * t * a⁻¹ * t⁻¹)⁻¹ * t⁻¹ = (t * t) * (a * t⁻¹ * a⁻¹ * t⁻¹) := by group
      _ = a * t⁻¹ * a⁻¹ * t⁻¹ := by rw [htt, one_mul]
      _ = a * t * a⁻¹ * t⁻¹ := by rw [htinv]
  have e : ∀ b : G, t * b⁻¹ * t⁻¹ = b → b * t * b⁻¹ * t⁻¹ = b ^ 2 := fun b hb' => by
    calc b * t * b⁻¹ * t⁻¹ = b * (t * b⁻¹ * t⁻¹) := by group
      _ = b ^ 2 := by rw [hb', sq]
  rw [e _ h1]
  exact hU.sq_mem _ hb

theorem not_forall_comm_mem_of_free {w : G}
    (hfree : ∀ x ∈ U₁, w * x * w⁻¹ * x⁻¹ ∈ R₂ → ∃ y ∈ U₁, (y * w * y⁻¹ * w⁻¹)⁻¹ * x ∈ R₂)
    (hcard : Nat.card R₂ < Nat.card U₁) : ¬ ∀ a ∈ U₁, w * a * w⁻¹ * a⁻¹ ∈ R₂ := by
  intro hall
  have hle : U₁ ≤ R₂ := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hfree x hx (hall x hx)
    have hy' : y * w * y⁻¹ * w⁻¹ ∈ R₂ := by
      have := inv_mem (hall y hy)
      rwa [show (w * y * w⁻¹ * y⁻¹)⁻¹ = y * w * y⁻¹ * w⁻¹ by group] at this
    have := mul_mem hy' hyx
    rwa [mul_inv_cancel_left] at this
  exact absurd (card_le_of_le hle) (not_le.mpr hcard)

theorem forall_comm_mem_of_forall_comm_mem_szT₁ (hU : U3U1Data G L f t T R₂ U₁)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (htU : t ∈ normalizer (U₁ : Set G)) {x : G}
    (hxN : x ∈ normalizer (U₁ : Set G)) (hxR : x ∈ centralizer (R₂ : Set G))
    (hxt : x * t = t * x) (hodd : Odd (orderOf x))
    (hxT : ∀ y ∈ szT₁ L T, x * y * x⁻¹ * y⁻¹ ∈ R₂) :
    ∀ a ∈ U₁, x * a * x⁻¹ * a⁻¹ ∈ R₂ := by
  have htt : t * t = 1 := by rw [← sq, hR.t_sq]
  have hxRN : x ∈ normalizer (R₂ : Set G) := centralizer_le_normalizer _ hxR
  have hsup : ∀ b ∈ szT₁ L T ⊔ R₂, x * b * x⁻¹ * b⁻¹ ∈ R₂ := by
    intro b hb
    obtain ⟨w, hw, r, hr, rfl⟩ := hR.mem_sup_iff.mp hb
    have hxr : x * r * x⁻¹ * r⁻¹ = 1 := by
      rw [← (mem_centralizer_iff.mp hxR r hr), mul_assoc r x, mul_inv_cancel, mul_one,
        mul_inv_cancel]
    have e : x * (w * r) * x⁻¹ * (w * r)⁻¹ =
        (x * w * x⁻¹ * w⁻¹) * (w * (x * r * x⁻¹ * r⁻¹) * w⁻¹) := by group
    rw [e, hxr, mul_one, mul_inv_cancel, mul_one]
    exact hxT w hw
  have hxtx : x * t * x⁻¹ = t := by rw [hxt, mul_inv_cancel_right]
  have hlay : ∀ a ∈ U₁, x * a * x⁻¹ * a⁻¹ ∈ szT₁ L T ⊔ R₂ := by
    intro a ha
    have ha' : x * a * x⁻¹ ∈ U₁ := (mem_normalizer_iff.mp hxN a).mp ha
    have hA : t * a * t⁻¹ ∈ U₁ := (mem_normalizer_iff.mp htU a).mp ha
    have hA' : t * (x * a * x⁻¹)⁻¹ * t⁻¹ ∈ U₁ := (mem_normalizer_iff.mp htU _).mp (inv_mem ha')
    have hb := hU.comm_t_mem_sup hR htU ha
    have h1 := hsup _ hb
    have e1 : x * (a * t * a⁻¹ * t⁻¹) * x⁻¹ * (a * t * a⁻¹ * t⁻¹)⁻¹ =
        (x * a * x⁻¹) * (t * (x * a * x⁻¹)⁻¹ * t⁻¹) * (t * a * t⁻¹) * a⁻¹ := by
      calc x * (a * t * a⁻¹ * t⁻¹) * x⁻¹ * (a * t * a⁻¹ * t⁻¹)⁻¹ =
          (x * a * x⁻¹) * (x * t * x⁻¹) * (x * a * x⁻¹)⁻¹ * (x * t * x⁻¹)⁻¹ *
            (a * t * a⁻¹ * t⁻¹)⁻¹ := by group
        _ = (x * a * x⁻¹) * (t * (x * a * x⁻¹)⁻¹ * t⁻¹) * (t * a * t⁻¹) * a⁻¹ := by
          rw [hxtx]; group
    rw [e1] at h1
    have h2 := SixNineRank.mem_of_mul_mem_swap hU.comm_mem hA' hA (inv_mem ha) h1
    have hd : x * a * x⁻¹ * a⁻¹ ∈ U₁ := mul_mem ha' (inv_mem ha)
    refine hU.mem_sup_of_comm_mem hR htt hd ?_
    have e2 : (x * a * x⁻¹ * a⁻¹) * t * (x * a * x⁻¹ * a⁻¹)⁻¹ * t⁻¹ =
        (x * a * x⁻¹) * a⁻¹ * (t * a * t⁻¹) * (t * (x * a * x⁻¹)⁻¹ * t⁻¹) := by group
    rw [e2]
    exact h2
  refine SixNineRank.comm_mem_of_sq hxRN hodd fun a ha => ?_
  have hd : x * a * x⁻¹ * a⁻¹ ∈ U₁ := mul_mem ((mem_normalizer_iff.mp hxN a).mp ha) (inv_mem ha)
  have e : x ^ 2 * a * (x ^ 2)⁻¹ * a⁻¹ =
      (x * (x * a * x⁻¹ * a⁻¹) * x⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹) *
        ((x * a * x⁻¹ * a⁻¹) ^ 2) := by
    rw [sq, sq]; group
  rw [e]
  exact mul_mem (hsup _ (hlay a ha)) (hU.sq_mem _ hd)

theorem forall_comm_mem_szT₁_of_comm_conj
    (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {v : G} (hvT : v ∈ T) (hv2 : v ^ 2 = 1)
    (hvS : v ∉ szT₁ L T ⊔ zpowers t) {x : G} (hxN : x ∈ normalizer (U₁ : Set G))
    (hxR : x ∈ centralizer (R₂ : Set G)) (hxt : x * t = t * x) (hodd : Odd (orderOf x))
    (hxv : ∀ a ∈ U₁, (x * v * x⁻¹ * v⁻¹) * a * (x * v * x⁻¹ * v⁻¹)⁻¹ * a⁻¹ ∈ R₂) :
    ∀ y ∈ szT₁ L T, x * y * x⁻¹ * y⁻¹ ∈ R₂ := by
  classical
  obtain ⟨E, _, _, _, σ, hEcard, hσ, -, u, vc, hc, hA₁u, hkey, hoddsc⟩ :=
    h.exists_rootCoords_scalar_of_card_sylow hS2
  have : Fintype E := Fintype.ofFinite E
  have hσσ : ∀ z, σ (σ z) = z := fun z => by
    rw [hσ, hσ, ← pow_mul, ← sq]
    have h1 : z ^ Fintype.card E = z := FiniteField.pow_card z
    rwa [← Nat.card_eq_fintype_card, hEcard] at h1
  have hchar1 : ∀ e : E, e * e = 1 → e = 1 := fun e he => by
    have h0 : (e + 1) * (e + 1) = 0 := by
      calc (e + 1) * (e + 1) = e * e + (e + e) + 1 := by ring
        _ = 0 := by rw [he, CharTwo.add_self_eq_zero, add_zero, CharTwo.add_self_eq_zero]
    have h1 : e + 1 = 0 := mul_self_eq_zero.mp h0
    calc e = -1 := eq_neg_of_add_eq_zero_left h1
      _ = 1 := CharTwo.neg_eq 1
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, hvA, -, -⟩ := h.outer_facts_of_card_sylow hS2 hvT hv2 hvS
  have hTA : T ≤ normalizer (szA L T t : Set G) :=
    Subgroup.le_normalizer.trans (h.normalizer_le_normalizer_szA_of_card_sylow hS2)
  have hvv : v * v = 1 := by rw [← sq, hv2]
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have hvN : v ∈ normalizer (szT₁ L T : Set G) := hTN₁ hvT
  have hxT₁ : x ∈ normalizer (szT₁ L T : Set G) := hU.mem_normalizer_szT₁_of_comm hR hxN hxt
  have hconjv : ∀ y ∈ szT₁ L T, v * y * v⁻¹ ∈ szT₁ L T := fun y hy =>
    (mem_normalizer_iff.mp hvN y).mp hy
  have hconjx : ∀ y ∈ szT₁ L T, x * y * x⁻¹ ∈ szT₁ L T := fun y hy =>
    (mem_normalizer_iff.mp hxT₁ y).mp hy
  have hxA : x ∈ normalizer (szA L T t : Set G) ⊓ centralizer (szA₁ (szT₁ L T) : Set G) := by
    have hxC : x ∈ centralizer (szA₁ (szT₁ L T) : Set G) :=
      mem_centralizer_iff.mpr fun a ha => mem_centralizer_iff.mp hxR a (hR.le ha)
    refine mem_inf.mpr ⟨centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun z hz => ?_), hxC⟩
    have hle : szA L T t ≤ centralizer ({x} : Set G) := by
      refine sup_le (fun a ha => mem_centralizer_singleton_iff.mpr ?_) (zpowers_le.mpr
        (mem_centralizer_singleton_iff.mpr hxt.symm))
      exact mem_centralizer_iff.mp hxC a ha
    exact mem_centralizer_singleton_iff.mp (hle hz)
  obtain ⟨s, hs1, hs⟩ := hoddsc x hxA hodd
  have hvA' : v ∈ normalizer (szA L T t : Set G) ⊓ centralizer (szA₁ (szT₁ L T) : Set G) :=
    mem_inf.mpr ⟨hTA hvT, mem_centralizer_iff.mpr fun a ha => (hvA a ha).symm⟩
  obtain ⟨y₁, hy₁, hu₁⟩ := hc.u_surj 1
  obtain ⟨l, hl1, hlin | hsemi⟩ := hkey v hvA'
  ·
    exfalso
    have hl : l = 1 := by
      refine hchar1 l ?_
      have e : v * (v * y₁ * v⁻¹) * v⁻¹ = y₁ := by
        calc v * (v * y₁ * v⁻¹) * v⁻¹ = (v * v) * y₁ * (v * v)⁻¹ := by group
          _ = y₁ := by rw [hvv, one_mul, inv_one, mul_one]
      have h1 := hlin _ (hconjv y₁ hy₁)
      rw [e, hlin y₁ hy₁, hu₁] at h1
      rw [mul_one] at h1
      exact h1.symm
    obtain ⟨y, hy, hyA⟩ := h.exists_comm_not_mem_of_outer_of_card_sylow hS2 hvT hv2 hvS
    apply hyA
    have hy' : v * y⁻¹ * v⁻¹ ∈ szT₁ L T := hconjv _ (inv_mem hy)
    have e : y * v * y⁻¹ * v⁻¹ = y * (v * y⁻¹ * v⁻¹) := by group
    rw [e]
    refine (hA₁u _ (mul_mem hy hy')).mpr ?_
    rw [hc.mul_u y hy _ hy', hlin _ (inv_mem hy), hl, one_mul, hc.u_inv hy, add_neg_cancel]
  have hσs : σ s = s := by
    set z := v * x * v⁻¹ with hz
    have hzy : z * y₁ * z⁻¹ = v * (x * (v * y₁ * v⁻¹) * x⁻¹) * v⁻¹ := by
      rw [hz]
      calc v * x * v⁻¹ * y₁ * (v * x * v⁻¹)⁻¹ = v * (x * (v⁻¹ * y₁ * v⁻¹⁻¹) * x⁻¹) * v⁻¹ := by
            group
        _ = v * (x * (v * y₁ * v⁻¹) * x⁻¹) * v⁻¹ := by rw [inv_inv, hvinv]
    have hzyT : z * y₁ * z⁻¹ ∈ szT₁ L T := by
      rw [hzy]; exact hconjv _ (hconjx _ (hconjv _ hy₁))
    have hzU : z * y₁ * z⁻¹ ∈ U₁ := hU.le (mem_sup_left hzyT)
    have h1 := hxv _ hzU
    have e1 : (x * v * x⁻¹ * v⁻¹) * (z * y₁ * z⁻¹) * (x * v * x⁻¹ * v⁻¹)⁻¹ = x * y₁ * x⁻¹ := by
      rw [hz]; group
    rw [e1] at h1
    have h2 : x * y₁ * x⁻¹ * (z * y₁ * z⁻¹)⁻¹ ∈ szA₁ (szT₁ L T) := by
      rw [← hR.inf]
      exact mem_inf.mpr ⟨mul_mem (hconjx _ hy₁) (inv_mem hzyT), h1⟩
    have h3 := (hA₁u _ (mul_mem (hconjx _ hy₁) (inv_mem hzyT))).mp h2
    rw [hc.mul_u _ (hconjx _ hy₁) _ (inv_mem hzyT), hc.u_inv hzyT, hs y₁ hy₁, hu₁, hzy,
      hsemi _ (hconjx _ (hconjv _ hy₁)), hs _ (hconjv _ hy₁), hsemi _ hy₁, hu₁, map_mul, map_mul,
      hσσ] at h3
    simp only [mul_one] at h3
    have h4 : s = σ s * (l * σ l) := by
      linear_combination h3
    rw [hl1, mul_one] at h4
    exact h4.symm
  have hs1' : s = 1 := hchar1 s (by rw [hσs] at hs1; exact hs1)
  intro y hy
  have hxyT := hconjx y hy
  have hmem : x * y * x⁻¹ * y⁻¹ ∈ szA₁ (szT₁ L T) := by
    refine (hA₁u _ (mul_mem hxyT (inv_mem hy))).mpr ?_
    rw [hc.mul_u _ hxyT _ (inv_mem hy), hc.u_inv hy, hs y hy, hs1', one_mul, add_neg_cancel]
  exact hR.le hmem

theorem _root_.CFSG.SeitzReduction.RankOne.U3Start.exists_outer_involution_of_four
    (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hncyc : ¬ ∃ b ∈ T, ∀ s ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T)
    (hfour : ∀ c ∈ T, c ^ 2 ∈ szT₁ L T ⊔ zpowers t) :
    ∃ v ∈ T, v ^ 2 = 1 ∧ v ∉ szT₁ L T ⊔ zpowers t := by
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  have hdec : ∀ c ∈ szT₁ L T ⊔ zpowers t, c ∈ szT₁ L T ∨ t⁻¹ * c ∈ szT₁ L T := by
    intro c hc
    obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hc
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with hz1 | hz1
    · left; rwa [hz1, mul_one]
    · right
      have hyt : y * t = t * y := mem_centralizer_iff.mp h.mem_centralizer_szT₁ y hy
      rw [hz1, hyt, inv_mul_cancel_left]
      exact hy
  obtain ⟨s, hs, hsS⟩ : ∃ s ∈ T, s ∉ szT₁ L T ⊔ zpowers t := by
    by_contra hno
    push Not at hno
    refine hncyc ⟨t, htT, fun c hc => ?_⟩
    rcases hdec c (hno c hc) with h1 | h1
    · exact ⟨0, by rwa [zpow_zero, inv_one, one_mul]⟩
    · exact ⟨1, by rwa [zpow_one]⟩
  have hs2 : s ^ 2 ∈ szT₁ L T := by
    rcases hdec _ (hfour s hs) with h1 | h1
    · exact h1
    · exact absurd h1 (h.inv_mul_sq_not_mem_of_not_isCyclic hS2 hncyc hs)
  exact h.exists_outer_involution_of_card_sylow hS2 hs hs2 hsS

theorem card_lt (hU : U3U1Data G L f t T R₂ U₁) (hR : U3R2 G L (szT₁ L T) R₂ t f) (hf : 1 ≤ f) :
    Nat.card R₂ < Nat.card U₁ := by
  rw [hU.card, hR.card]
  exact Nat.pow_lt_pow_right (Nat.one_lt_two_pow (by omega)) (by norm_num)

section Certificates

theorem exists_mem_not_forall_comm_mem (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) :
    ∃ k ∈ normalizer (U₁ : Set G) ⊓ centralizer (R₂ : Set G),
      ¬ ∀ a ∈ U₁, k * a * k⁻¹ * a⁻¹ ∈ R₂ := by
  obtain ⟨k, -, -, hkU, hkT, hkR, -, hksurj⟩ := hU.exists_odd_mem_normalizer_centralizer h hS2 hR
  refine ⟨k, mem_inf.mpr ⟨hkU, hkR⟩, fun hall => ?_⟩
  obtain ⟨hT₁card, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  have hle : szT₁ L T ≤ szA₁ (szT₁ L T) := by
    intro y hy
    obtain ⟨y', hy', hyy'⟩ := hksurj y hy
    have hc : k * y' * k⁻¹ * y'⁻¹ ∈ szA₁ (szT₁ L T) := by
      rw [← hR.inf]
      exact mem_inf.mpr ⟨mul_mem ((mem_normalizer_iff.mp hkT y').mp hy') (inv_mem hy'),
        hall y' (hU.le (mem_sup_left hy'))⟩
    have := mul_mem hyy' (inv_mem hc)
    rwa [mul_inv_cancel_right, inv_mem_iff] at this
  have h1 := card_le_of_le hle
  rw [hT₁card, hA₁card] at h1
  have h2 : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := h.two_le; omega)
  have h3 : (2 ^ f) ^ 1 < (2 ^ f) ^ 3 := Nat.pow_lt_pow_right h2 (by norm_num)
  rw [pow_one] at h3
  omega

end Certificates

end U3U1Data

section Certificates

theorem u3SixNineRankInput_of_rankCount (hGI : SixNineRank.RankCountInput)
    (hT : U3SixNineTorusInput) : U3SixNineRankInput := by
  intro G _ _ L f t T R₂ U₁ h hS2 hR hU hncyc hS hC hfour hall
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨v, hvT, hv2, hvS⟩ := h.exists_outer_involution_of_four hS2 hncyc hfour
  obtain ⟨y, hy, hy1, hy2⟩ := hU.exists_three_cycle_of_four h hS2 hR hS hfour hvT hv2 hvS
    fun w hw hw2 hwS => by
      obtain ⟨g, hg, hgw⟩ := hall w hw hw2 hwS
      exact ⟨g, (mem_inf.mp hg).2, hgw⟩
  obtain ⟨ε, hεN, hεt, hεp, hεfix, hεirr⟩ := hT G L f t T R₂ U₁ h hS2 hR hU
  obtain ⟨htvT, htv2, htvS⟩ := h.mul_outer_of_card_sylow hS2 hvT hv2 hvS
  have htU : t ∈ normalizer (U₁ : Set G) := hU.le_normalizer h hS2 hR htT
  have hcard := hU.card_lt hR (by have := h.two_le; omega)
  exact hGI G (normalizer (U₁ : Set G)) U₁ R₂ (szT₁ L T ⊔ R₂)
    (normalizer (U₁ : Set G) ⊓ centralizer (R₂ : Set G)) t v y ε le_sup_right hU.le
    (le_inf Subgroup.le_normalizer hU.le_centralizer) inf_le_left le_rfl
    hU.normalizer_le_normalizer_R₂ hU.normalizer_le_normalizer_K hU.sq_mem
    hU.comm_mem (hU.isSylowOf_normalizer_inf_centralizer h hS2 hR hS hC) htU
    (hU.le_normalizer h hS2 hR hvT) h.sq_eq_one hv2
    (mem_centralizer_singleton_iff.mp (h.le hvT)).symm
    (U3U1Data.not_forall_comm_mem_of_free (fun x hx hxw => hU.exists_comm_mem_t hR hx hxw) hcard)
    (U3U1Data.not_forall_comm_mem_of_free
      (fun x hx hxw => hU.exists_comm_mem_of_outer_of_card_sylow h hS2 hR hvT hv2 hvS hx hxw) hcard)
    (U3U1Data.not_forall_comm_mem_of_free
      (fun x hx hxw => hU.exists_comm_mem_of_outer_of_card_sylow h hS2 hR htvT htv2 htvS hx hxw)
      hcard)
    (mem_inf.mp hy).1 hy1 hy2 hU.conj_of_mem (hU.exists_mem_not_forall_comm_mem h hS2 hR)
    (fun x hx hxt hodd hxv => hU.forall_comm_mem_of_forall_comm_mem_szT₁ hR htU
      (mem_inf.mp hx).1 (mem_inf.mp hx).2 hxt hodd
      (hU.forall_comm_mem_szT₁_of_comm_conj h hS2 hR hvT hv2 hvS (mem_inf.mp hx).1
        (mem_inf.mp hx).2 hxt hodd hxv))
    (fun x hx hxt => hU.mem_normalizer_sup_of_comm hR hx hxt) hεN hεt hεp hεfix hεirr

end Certificates

end CFSG.SeitzReduction.RankOne
