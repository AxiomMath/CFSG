module

public import CFSG.ClassicalInvolution.Asc77.AscE187P2
public import CFSG.ClassicalInvolution.Q3.Q3T8Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

namespace TwinThmEW

section Q8

variable {G : Type} [Group G]

@[expose] def IsQ8 (R : Subgroup G) : Prop := Nonempty (↥R ≃* QuaternionGroup 2)

theorem orb4_q8_cent_cases : ∀ a y : QuaternionGroup 2, a * a ≠ 1 → a * y = y * a →
    y = 1 ∨ y = a ∨ y = a * a ∨ y = a * a * a := by decide

theorem orb4_q8_noncentral : ∀ a : QuaternionGroup 2, a * a ≠ 1 → ∃ r, a * r ≠ r * a := by decide

theorem orb4_q8_orderOf_a_one : orderOf (QuaternionGroup.a 1 : QuaternionGroup 2) = 4 := by
  rw [QuaternionGroup.orderOf_a_one]

theorem orb4_sq_ne_one_of_orderOf_eq_four {u : G} (hu : orderOf u = 4) : u * u ≠ 1 := by
  intro h
  have : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  rw [hu] at this
  omega

theorem IsQ8.exists_order_four {R : Subgroup G} (h : IsQ8 R) : ∃ x ∈ R, orderOf x = 4 := by
  obtain ⟨e⟩ := h
  refine ⟨((e.symm (QuaternionGroup.a 1) : ↥R) : G), (e.symm _).2, ?_⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  exact orb4_q8_orderOf_a_one

theorem IsQ8.noncentral {R : Subgroup G} (h : IsQ8 R) {u : G} (hu : u ∈ R) (hu4 : orderOf u = 4) :
    ∃ r ∈ R, u * r ≠ r * u := by
  obtain ⟨e⟩ := h
  have h4 : orderOf (e ⟨u, hu⟩) = 4 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hu4
  obtain ⟨r, hr⟩ := orb4_q8_noncentral _ (orb4_sq_ne_one_of_orderOf_eq_four h4)
  refine ⟨((e.symm r : ↥R) : G), (e.symm r).2, fun hcomm => hr ?_⟩
  have h1 : (⟨u, hu⟩ : ↥R) * e.symm r = e.symm r * ⟨u, hu⟩ := Subtype.ext hcomm
  have h2 := congrArg e h1
  simpa using h2

theorem IsQ8.cent {R : Subgroup G} (h : IsQ8 R) {u : G} (hu : u ∈ R) (hu4 : orderOf u = 4)
    {y : G} (hy : y ∈ R) (hyu : y * u = u * y) :
    y = 1 ∨ y = u ∨ y = u * u ∨ y = u * u * u := by
  obtain ⟨e⟩ := h
  have h4 : orderOf (e ⟨u, hu⟩) = 4 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hu4
  have h2 : e ⟨u, hu⟩ * e ⟨y, hy⟩ = e ⟨y, hy⟩ * e ⟨u, hu⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext hyu.symm)
  rcases orb4_q8_cent_cases _ _ (orb4_sq_ne_one_of_orderOf_eq_four h4) h2 with h1 | h1 | h1 | h1
  · left
    have := e.injective (h1.trans (map_one e).symm)
    exact congrArg Subtype.val this
  · right; left
    exact congrArg Subtype.val (e.injective h1)
  · right; right; left
    rw [← map_mul] at h1
    exact congrArg Subtype.val (e.injective h1)
  · right; right; right
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (e.injective h1)

theorem orb4_q8_central_cases : ∀ a y : QuaternionGroup 2, a * a ≠ 1 → (∀ r, y * r = r * y) →
    y = 1 ∨ y = a * a := by decide

theorem IsQ8.central {R : Subgroup G} (h : IsQ8 R) {u : G} (hu : u ∈ R) (hu4 : orderOf u = 4)
    {y : G} (hy : y ∈ R) (hyc : ∀ r ∈ R, y * r = r * y) : y = 1 ∨ y = u * u := by
  obtain ⟨e⟩ := h
  have h4 : orderOf (e ⟨u, hu⟩) = 4 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hu4
  have hb : ∀ r : QuaternionGroup 2, e ⟨y, hy⟩ * r = r * e ⟨y, hy⟩ := by
    intro r
    have h1 := hyc ((e.symm r : ↥R) : G) (e.symm r).2
    have h2 : (⟨y, hy⟩ : ↥R) * e.symm r = e.symm r * ⟨y, hy⟩ := Subtype.ext h1
    have h3 := congrArg e h2
    simpa using h3
  rcases orb4_q8_central_cases _ _ (orb4_sq_ne_one_of_orderOf_eq_four h4) hb with h1 | h1
  · left
    have := e.injective (h1.trans (map_one e).symm)
    exact congrArg Subtype.val this
  · right
    rw [← map_mul] at h1
    exact congrArg Subtype.val (e.injective h1)

end Q8

section Shape

variable {G : Type} [Group G]

@[expose] def D4Shape (S : Subgroup G) (t d₁ d₂ : G) : Prop :=
  ∃ A : Subgroup G, d₁ ∈ A ∧ d₂ ∈ A ∧
    (∀ c ∈ S, c * t = t * c → c * d₂ = d₂ * c → conjSub c A = A) ∧
    ∀ w ∈ A, w * w = 1 → w * t = t * w → w = 1 ∨ w = d₁ ∨ w = d₂ ∨ w = d₁ * d₂

theorem orb4_conjSub_le_of_mem {S X : Subgroup G} {s : G} (hs : s ∈ S) (hX : X ≤ S) :
    conjSub s X ≤ S := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  have h1 : s⁻¹ * x * s ∈ S := hX hx
  have : x = s * (s⁻¹ * x * s) * s⁻¹ := by group
  rw [this]
  exact S.mul_mem (S.mul_mem hs h1) (S.inv_mem hs)

theorem commutes_conj_twins [Finite G] {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    {K₀ R₀ S₁ : Subgroup G} {t : G} (hK₀ : K₀ ∈ Ω) (ht : IsUniqueInvolution K₀ t)
    (hR₀K : R₀ ≤ K₀) (hS₁ : IsPGroup 2 S₁) (hR₀S : R₀ ≤ S₁) {a b : G} (ha : a ∈ S₁) (hb : b ∈ S₁)
    (hat : a * t = t * a) (hbt : b * t = t * b) (hne : conjSub a K₀ ≠ conjSub b K₀) :
    Commutes (conjSub a R₀) (conjSub b R₀) := by
  have hKa : conjSub a K₀ ∈ Ω := hΩ.conjInvariant a K₀ hK₀
  have hKb : conjSub b K₀ ∈ Ω := hΩ.conjInvariant b K₀ hK₀
  have hta : IsUniqueInvolution (conjSub a K₀) t := by
    have := ht.conj a
    rwa [show a * t * a⁻¹ = t by rw [hat]; group] at this
  have htb : IsUniqueInvolution (conjSub b K₀) t := by
    have := ht.conj b
    rwa [show b * t * b⁻¹ = t by rw [hbt]; group] at this
  exact hΩ.commutes_of_twin_of_isPGroup hKa hKb hne hta htb (conjSub_mono hR₀K)
    (conjSub_mono hR₀K)
    (hS₁.to_le (sup_le (orb4_conjSub_le_of_mem ha hR₀S) (orb4_conjSub_le_of_mem hb hR₀S)))

private theorem inv_conj_conj {d : G} (hd : d * d = 1) (a : G) :
    d * (d * a * d⁻¹) * d⁻¹ = a := by
  have : d * (d * a * d⁻¹) * d⁻¹ = (d * d) * a * (d * d)⁻¹ := by group
  rw [this, hd]
  group

theorem orbit4_core [Finite G] {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    {K₀ R₀ H S S₁ A : Subgroup G} {t d₁ d₂ : G} (hK₀ : K₀ ∈ Ω) (ht : IsUniqueInvolution K₀ t)
    (hR₀K : R₀ ≤ K₀) (hq8 : IsQ8 R₀) (hS₁ : IsPGroup 2 S₁) (hR₀S : R₀ ≤ S₁)
    (g₁ : GoodInv H t d₁) (g₂ : GoodInv H t d₂) (g₃ : GoodInv H t (d₁ * d₂))
    (hc : d₁ * d₂ = d₂ * d₁) (hd₁S : d₁ ∈ S₁) (hd₂S : d₂ ∈ S₁)
    (m₁ : conjSub d₁ K₀ ≠ K₀) (m₂ : conjSub d₂ K₀ ≠ K₀) (m₃ : conjSub (d₁ * d₂) K₀ ≠ K₀)
    (hF6 : ∀ v ∈ S₁, v * t = t * v → v ∈ H → v ∈ S)
    (hbad : ∀ u ∈ K₀, orderOf u = 4 → u ∉ H) (hA₁ : d₁ ∈ A)
    (hAN : ∀ c ∈ S, c * t = t * c → c * d₂ = d₂ * c → conjSub c A = A)
    (hAD : ∀ w ∈ A, w * w = 1 → w * t = t * w → w = 1 ∨ w = d₁ ∨ w = d₂ ∨ w = d₁ * d₂) :
    False := by
  obtain ⟨x, hxR, hx4⟩ := hq8.exists_order_four
  obtain ⟨r, hrR, hxr⟩ := hq8.noncentral hxR hx4
  have hxK : x ∈ K₀ := hR₀K hxR
  have hxS : x ∈ S₁ := hR₀S hxR
  have hxsq : x * x = t := sq_eq_of_orderOf_four ht hxK hx4
  have ht2 : t * t = 1 := ht.sq
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hd₁t := g₁.comm_t
  have hd₂t := g₂.comm_t
  have hd₃t := g₃.comm_t
  have hd₁i : d₁⁻¹ = d₁ := inv_eq_of_mul_eq_one_right g₁.sq
  have hd₂i : d₂⁻¹ = d₂ := inv_eq_of_mul_eq_one_right g₂.sq
  have hd₃i : (d₁ * d₂)⁻¹ = d₁ * d₂ := inv_eq_of_mul_eq_one_right g₃.sq
  have hd₃S : d₁ * d₂ ∈ S₁ := S₁.mul_mem hd₁S hd₂S
  obtain ⟨y₁, hy₁⟩ : ∃ y, y = d₁ * x * d₁⁻¹ := ⟨_, rfl⟩
  obtain ⟨y₂, hy₂⟩ : ∃ y, y = d₂ * x * d₂⁻¹ := ⟨_, rfl⟩
  obtain ⟨y₃, hy₃⟩ : ∃ y, y = (d₁ * d₂) * x * (d₁ * d₂)⁻¹ := ⟨_, rfl⟩
  have hy₁R : y₁ ∈ conjSub d₁ R₀ := hy₁ ▸ conj_mem_conjSub hxR
  have hy₂R : y₂ ∈ conjSub d₂ R₀ := hy₂ ▸ conj_mem_conjSub hxR
  have hy₃R : y₃ ∈ conjSub (d₁ * d₂) R₀ := hy₃ ▸ conj_mem_conjSub hxR
  have hxR' : x ∈ conjSub 1 R₀ := by rw [conjSub_one]; exact hxR
  have hrR' : r ∈ conjSub 1 R₀ := by rw [conjSub_one]; exact hrR
  have hconj_eq : ∀ a b : G, conjSub a K₀ = conjSub b K₀ → conjSub (a⁻¹ * b) K₀ = K₀ := by
    intro a b h
    rw [conjSub_mul, ← h, conjSub_inv_conjSub]
  have n01 : conjSub 1 K₀ ≠ conjSub d₁ K₀ := by
    intro h
    have := hconj_eq _ _ h
    rw [inv_one, one_mul] at this
    exact m₁ this
  have n02 : conjSub 1 K₀ ≠ conjSub d₂ K₀ := by
    intro h
    have := hconj_eq _ _ h
    rw [inv_one, one_mul] at this
    exact m₂ this
  have n03 : conjSub 1 K₀ ≠ conjSub (d₁ * d₂) K₀ := by
    intro h
    have := hconj_eq _ _ h
    rw [inv_one, one_mul] at this
    exact m₃ this
  have n12 : conjSub d₁ K₀ ≠ conjSub d₂ K₀ := by
    intro h
    have := hconj_eq _ _ h
    rw [hd₁i] at this
    exact m₃ this
  have n13 : conjSub d₁ K₀ ≠ conjSub (d₁ * d₂) K₀ := by
    intro h
    have := hconj_eq _ _ h
    rw [hd₁i, ← mul_assoc, g₁.sq, one_mul] at this
    exact m₂ this
  have n23 : conjSub d₂ K₀ ≠ conjSub (d₁ * d₂) K₀ := by
    intro h
    have := hconj_eq _ _ h
    have e : d₂⁻¹ * (d₁ * d₂) = d₁ := by
      rw [hd₂i, ← mul_assoc, ← hc, mul_assoc, g₂.sq, mul_one]
    rw [e] at this
    exact m₁ this
  have hcomm := fun {a b : G} (ha : a ∈ S₁) (hb : b ∈ S₁) (hat : a * t = t * a)
    (hbt : b * t = t * b) (hne : conjSub a K₀ ≠ conjSub b K₀) =>
      commutes_conj_twins hΩ hK₀ ht hR₀K hS₁ hR₀S ha hb hat hbt hne
  have h1S : (1 : G) ∈ S₁ := S₁.one_mem
  have h1t : (1 : G) * t = t * 1 := by simp
  have c01 := hcomm h1S hd₁S h1t hd₁t n01
  have c02 := hcomm h1S hd₂S h1t hd₂t n02
  have c03 := hcomm h1S hd₃S h1t hd₃t n03
  have c12 := hcomm hd₁S hd₂S hd₁t hd₂t n12
  have c13 := hcomm hd₁S hd₃S hd₁t hd₃t n13
  have c23 := hcomm hd₂S hd₃S hd₂t hd₃t n23
  have hxy₁ : Commute x y₁ := (c01 x hxR' y₁ hy₁R)
  have hxy₂ : Commute x y₂ := (c02 x hxR' y₂ hy₂R)
  have hxy₃ : Commute x y₃ := (c03 x hxR' y₃ hy₃R)
  have hy₁y₂ : Commute y₁ y₂ := (c12 y₁ hy₁R y₂ hy₂R)
  have hy₁y₃ : Commute y₁ y₃ := (c13 y₁ hy₁R y₃ hy₃R)
  have hy₂y₃ : Commute y₂ y₃ := (c23 y₂ hy₂R y₃ hy₃R)
  have hry₁ : Commute r y₁ := (c01 r hrR' y₁ hy₁R)
  have hry₂ : Commute r y₂ := (c02 r hrR' y₂ hy₂R)
  have hry₃ : Commute r y₃ := (c03 r hrR' y₃ hy₃R)
  have hsq : ∀ δ y : G, δ * t = t * δ → y = δ * x * δ⁻¹ → y * y = t := by
    intro δ y hδ hy
    rw [hy]
    calc δ * x * δ⁻¹ * (δ * x * δ⁻¹) = δ * (x * x) * δ⁻¹ := by group
      _ = δ * t * δ⁻¹ := by rw [hxsq]
      _ = t := by rw [hδ]; group
  have hy₁sq : y₁ * y₁ = t := hsq d₁ y₁ hd₁t hy₁
  have hy₂sq : y₂ * y₂ = t := hsq d₂ y₂ hd₂t hy₂
  have hy₃sq : y₃ * y₃ = t := hsq (d₁ * d₂) y₃ hd₃t hy₃
  have hxy₂' : Commute x y₂⁻¹ := hxy₂.inv_right
  have hcc : (x * y₂⁻¹) * (x * y₂⁻¹) = 1 := by
    have e : (x * y₂⁻¹) * (x * y₂⁻¹) = (x * x) * (y₂⁻¹ * y₂⁻¹) := by
      calc (x * y₂⁻¹) * (x * y₂⁻¹) = x * (y₂⁻¹ * x) * y₂⁻¹ := by group
        _ = x * (x * y₂⁻¹) * y₂⁻¹ := by rw [← hxy₂'.eq]
        _ = (x * x) * (y₂⁻¹ * y₂⁻¹) := by group
    rw [e, hxsq]
    have : y₂⁻¹ * y₂⁻¹ = t⁻¹ := by
      rw [← hy₂sq]; group
    rw [this, hti, ht2]
  have hci : (x * y₂⁻¹)⁻¹ = x * y₂⁻¹ := inv_eq_of_mul_eq_one_right hcc
  have hcd₂ : (x * y₂⁻¹) * d₂ = d₂ * (x * y₂⁻¹) := by
    have e1 : d₂ * (x * y₂⁻¹) * d₂⁻¹ = y₂ * x⁻¹ := by
      calc d₂ * (x * y₂⁻¹) * d₂⁻¹ = (d₂ * x * d₂⁻¹) * (d₂ * y₂⁻¹ * d₂⁻¹) := by group
        _ = y₂ * (d₂ * y₂ * d₂⁻¹)⁻¹ := by rw [← hy₂]; group
        _ = y₂ * x⁻¹ := by rw [hy₂, inv_conj_conj g₂.sq]
    have e2 : y₂ * x⁻¹ = x * y₂⁻¹ := by
      have : (x * y₂⁻¹)⁻¹ = y₂ * x⁻¹ := by group
      rw [← this, hci]
    rw [e2] at e1
    exact (mul_inv_eq_iff_eq_mul.mp e1).symm
  have hsqt : ∀ y : G, y * y = t → y * t = t * y := by
    intro y hy
    calc y * t = y * (y * y) := by rw [hy]
      _ = (y * y) * y := by group
      _ = t * y := by rw [hy]
  have hxt : x * t = t * x := hsqt x hxsq
  have hy₁t : y₁ * t = t * y₁ := hsqt y₁ hy₁sq
  have hy₂t : y₂ * t = t * y₂ := hsqt y₂ hy₂sq
  have hy₃t : y₃ * t = t * y₃ := hsqt y₃ hy₃sq
  have hct : (x * y₂⁻¹) * t = t * (x * y₂⁻¹) := by
    have h1 : Commute x t := hxt
    have h2 : Commute y₂⁻¹ t := (show Commute y₂ t from hy₂t).inv_left
    exact (h1.mul_left h2).eq
  have hy₂S : y₂ ∈ S₁ := hy₂ ▸ S₁.mul_mem (S₁.mul_mem hd₂S hxS) (S₁.inv_mem hd₂S)
  have hcS₁ : x * y₂⁻¹ ∈ S₁ := S₁.mul_mem hxS (S₁.inv_mem hy₂S)
  have hcH : x * y₂⁻¹ ∈ H := by
    apply g₂.cent
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcd₂
  have hcS : x * y₂⁻¹ ∈ S := hF6 _ hcS₁ hct hcH
  have hcA : conjSub (x * y₂⁻¹) A = A := hAN _ hcS hct hcd₂
  have hwA' : (x * y₂⁻¹) * d₁ * (x * y₂⁻¹)⁻¹ * d₁⁻¹ ∈ A := by
    have h1 : (x * y₂⁻¹) * d₁ * (x * y₂⁻¹)⁻¹ ∈ conjSub (x * y₂⁻¹) A := conj_mem_conjSub hA₁
    rw [hcA] at h1
    exact A.mul_mem h1 (A.inv_mem hA₁)
  have e3 : d₁ * y₂ * d₁⁻¹ = y₃ := by rw [hy₂, hy₃]; group
  have hd₁y : d₁ * (x * y₂⁻¹) * d₁⁻¹ = y₁ * y₃⁻¹ := by
    calc d₁ * (x * y₂⁻¹) * d₁⁻¹ = (d₁ * x * d₁⁻¹) * (d₁ * y₂ * d₁⁻¹)⁻¹ := by group
      _ = y₁ * y₃⁻¹ := by rw [e3, ← hy₁]
  have hwdef : (x * y₂⁻¹) * d₁ * (x * y₂⁻¹)⁻¹ * d₁⁻¹ = (x * y₂⁻¹) * (y₁ * y₃⁻¹) := by
    rw [hci]
    calc (x * y₂⁻¹) * d₁ * (x * y₂⁻¹) * d₁⁻¹ = (x * y₂⁻¹) * (d₁ * (x * y₂⁻¹) * d₁⁻¹) := by group
      _ = _ := by rw [hd₁y]
  rw [hwdef] at hwA'
  have pairsq : ∀ a b : G, Commute a b → a * a = t → b * b = t → (a * b⁻¹) * (a * b⁻¹) = 1 := by
    intro a b hab ha hb
    have hab' : Commute a b⁻¹ := hab.inv_right
    have e : (a * b⁻¹) * (a * b⁻¹) = (a * a) * (b⁻¹ * b⁻¹) := by
      calc (a * b⁻¹) * (a * b⁻¹) = a * (b⁻¹ * a) * b⁻¹ := by group
        _ = a * (a * b⁻¹) * b⁻¹ := by rw [← hab'.eq]
        _ = (a * a) * (b⁻¹ * b⁻¹) := by group
    rw [e, ha]
    have : b⁻¹ * b⁻¹ = t⁻¹ := by rw [← hb]; group
    rw [this, hti, ht2]
  have hab : Commute (x * y₂⁻¹) (y₁ * y₃⁻¹) :=
    (hxy₁.mul_right hxy₃.inv_right).mul_left
      (hy₁y₂.symm.inv_left.mul_right hy₂y₃.inv_left.inv_right)
  have hww : ((x * y₂⁻¹) * (y₁ * y₃⁻¹)) * ((x * y₂⁻¹) * (y₁ * y₃⁻¹)) = 1 := by
    have h1 := pairsq x y₂ hxy₂ hxsq hy₂sq
    have h2 := pairsq y₁ y₃ hy₁y₃ hy₁sq hy₃sq
    calc ((x * y₂⁻¹) * (y₁ * y₃⁻¹)) * ((x * y₂⁻¹) * (y₁ * y₃⁻¹))
        = (x * y₂⁻¹) * ((y₁ * y₃⁻¹) * (x * y₂⁻¹)) * (y₁ * y₃⁻¹) := by group
      _ = (x * y₂⁻¹) * ((x * y₂⁻¹) * (y₁ * y₃⁻¹)) * (y₁ * y₃⁻¹) := by rw [← hab.eq]
      _ = ((x * y₂⁻¹) * (x * y₂⁻¹)) * ((y₁ * y₃⁻¹) * (y₁ * y₃⁻¹)) := by group
      _ = 1 := by rw [h1, h2, one_mul]
  have hwt : ((x * y₂⁻¹) * (y₁ * y₃⁻¹)) * t = t * ((x * y₂⁻¹) * (y₁ * y₃⁻¹)) := by
    have h1 : Commute x t := hxt
    have h2 : Commute y₂⁻¹ t := (show Commute y₂ t from hy₂t).inv_left
    have h3 : Commute y₁ t := hy₁t
    have h4 : Commute y₃⁻¹ t := (show Commute y₃ t from hy₃t).inv_left
    exact ((h1.mul_left h2).mul_left (h3.mul_left h4)).eq
  have hw1 : (x * y₂⁻¹) * (y₁ * y₃⁻¹) ≠ 1 := by
    intro h
    have hq : x * (y₂⁻¹ * (y₁ * y₃⁻¹)) = 1 := by rw [← mul_assoc]; exact h
    have hxq : x = (y₂⁻¹ * (y₁ * y₃⁻¹))⁻¹ := eq_inv_of_mul_eq_one_left hq
    have hrq : Commute r (y₂⁻¹ * (y₁ * y₃⁻¹)) := hry₂.inv_right.mul_right (hry₁.mul_right hry₃.inv_right)
    have hrx : Commute r x := by rw [hxq]; exact hrq.inv_right
    exact hxr hrx.eq.symm
  have hxw : x * ((x * y₂⁻¹) * (y₁ * y₃⁻¹)) = ((x * y₂⁻¹) * (y₁ * y₃⁻¹)) * x :=
    (((Commute.refl x).mul_right hxy₂.inv_right).mul_right (hxy₁.mul_right hxy₃.inv_right)).eq
  rcases hAD _ hwA' hww hwt with h | h | h | h
  · exact hw1 h
  · apply hbad x hxK hx4
    apply g₁.cent
    rw [Subgroup.mem_centralizer_singleton_iff, ← h]
    exact hxw
  · apply hbad x hxK hx4
    apply g₂.cent
    rw [Subgroup.mem_centralizer_singleton_iff, ← h]
    exact hxw
  · apply hbad x hxK hx4
    apply g₃.cent
    rw [Subgroup.mem_centralizer_singleton_iff, ← h]
    exact hxw


theorem orb4_conjSub_inf (g : G) (A B : Subgroup G) :
    conjSub g (A ⊓ B) = conjSub g A ⊓ conjSub g B := by
  ext x
  simp only [mem_conjSub_iff, Subgroup.mem_inf]

theorem orb4_conjSub_sup (g : G) (A B : Subgroup G) :
    conjSub g (A ⊔ B) = conjSub g A ⊔ conjSub g B := by
  unfold conjSub
  exact Subgroup.map_sup _ _ _

theorem orb4_rset_commutes [Finite G] {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) (S : Sylow 2 G)
    {R R' : Subgroup G} (hR : R ∈ RSet Ω) (hR' : R' ∈ RSet Ω) (hRS : R ≤ (S : Subgroup G))
    (hR'S : R' ≤ (S : Subgroup G)) (hne : R ≠ R') : Commutes R R' :=
  Q3T8.Asc77.l6_7_proved G Ω hΩ S R hR R' hR' hRS hR'S hne

theorem orb4_conjSub_sSup_eq {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {S : Subgroup G}
    {𝒮 : Set (Subgroup G)} {d : G} (h𝒮 : ∀ R ∈ 𝒮, R ∈ RSet Ω ∧ R ≤ S)
    (hsupp : ∀ R ∈ RSet Ω, R ≤ S → (R ∈ 𝒮 ↔ ¬ ∀ r ∈ R, r * d = d * r))
    {c : G} (hc : c ∈ S) (hcd : c * d = d * c) : conjSub c (sSup 𝒮) = sSup 𝒮 := by
  have key : ∀ c ∈ S, c * d = d * c → conjSub c (sSup 𝒮) ≤ sSup 𝒮 := by
    intro c hc hcd
    have hmem : ∀ R ∈ 𝒮, conjSub c R ∈ 𝒮 := by
      intro R hR
      obtain ⟨hRΩ, hRS⟩ := h𝒮 R hR
      have hcR : conjSub c R ∈ RSet Ω := RSet.conj hΩ.conjInvariant hRΩ c
      have hcRS : conjSub c R ≤ S := orb4_conjSub_le_of_mem hc hRS
      refine (hsupp _ hcR hcRS).mpr ?_
      intro hall
      have hnot := (hsupp R hRΩ hRS).mp hR
      apply hnot
      intro r hr
      have h1 : c * r * c⁻¹ * d = d * (c * r * c⁻¹) := hall _ (conj_mem_conjSub hr)
      have hcomm : Commute c d := hcd
      have h2 : Commute (c⁻¹ * (c * r * c⁻¹) * c) d :=
        (hcomm.inv_left.mul_left (show Commute (c * r * c⁻¹) d from h1)).mul_left hcomm
      have e : c⁻¹ * (c * r * c⁻¹) * c = r := by group
      rw [e] at h2
      exact h2.eq
    unfold conjSub
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun R hR => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (hmem R hR)
  refine le_antisymm (key c hc hcd) ?_
  have hcd' : c⁻¹ * d = d * c⁻¹ := (show Commute c d from hcd).inv_left.eq
  have hcinv := key c⁻¹ (S.inv_mem hc) hcd'
  have := conjSub_mono (n := c) hcinv
  rwa [conjSub_conjSub_inv] at this

theorem orb4_not_all_commute {R : Subgroup G} (hR : IsQ8 R) {v a b : G} (hv : v ∈ R)
    (hv4 : orderOf v = 4) (ha : ∀ r ∈ R, r * a = a * r) (hb : ∀ r ∈ R, r * b = b * r) :
    ¬ ∀ r ∈ R, r * (a * v * b) = (a * v * b) * r := by
  intro hall
  obtain ⟨r, hrR, hr⟩ := hR.noncentral hv hv4
  apply hr
  have h1 : Commute r (a * v * b) := hall r hrR
  have hra : Commute r a := ha r hrR
  have hrb : Commute r b := hb r hrR
  have h2 : Commute r (a * v) := by
    have : a * v = (a * v * b) * b⁻¹ := by group
    rw [this]
    exact h1.mul_right hrb.inv_right
  have h3 : Commute r v := by
    have : v = a⁻¹ * (a * v) := by group
    rw [this]
    exact hra.inv_right.mul_right h2
  exact h3.eq.symm

theorem orb4_d4_cases {u u' z y y' : G} (huu' : u * u' = u' * u) (hz : u * u = z) (hz' : u' * u' = z)
    (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hy : y = 1 ∨ y = u ∨ y = u * u ∨ y = u * u * u)
    (hy' : y' = 1 ∨ y' = u' ∨ y' = u' * u' ∨ y' = u' * u' * u')
    (hw : (y * y') * (y * y') = 1) :
    y * y' = 1 ∨ y * y' = z ∨ y * y' = u * u' ∨ y * y' = z * (u * u') := by
  have hzu : Commute z u := by
    show z * u = u * z
    rw [← hz]; group
  have hzu' : Commute z u' := by
    show z * u' = u' * z
    rw [← hz']; group
  have nf : ∀ (v : G), Commute z v → v * v = z → (∀ x, x = 1 ∨ x = v ∨ x = v * v ∨ x = v * v * v →
      ((x = 1 ∨ x = z) ∧ x * x = 1) ∨ ((x = v ∨ x = z * v) ∧ x * x = z)) := by
    intro v hzv hvv x hx
    rcases hx with h | h | h | h
    · left; rw [h]; exact ⟨Or.inl rfl, mul_one 1⟩
    · right; rw [h]; exact ⟨Or.inl rfl, hvv⟩
    · left; rw [h]; refine ⟨Or.inr hvv, ?_⟩; rw [hvv]; exact hz2
    · right
      have e : v * v * v = z * v := by rw [hvv]
      rw [h]
      refine ⟨Or.inr e, ?_⟩
      rw [e]
      calc z * v * (z * v) = z * (v * z) * v := by group
        _ = z * (z * v) * v := by rw [← hzv.eq]
        _ = (z * z) * (v * v) := by group
        _ = z := by rw [hz2, hvv, one_mul]
  rcases nf u hzu hz y hy with ⟨hye, hyy⟩ | ⟨hyo, hyy⟩ <;>
    rcases nf u' hzu' hz' y' hy' with ⟨hye', hyy'⟩ | ⟨hyo', hyy'⟩
  ·
    rcases hye with h | h <;> rcases hye' with h' | h' <;> rw [h, h']
    · left; exact one_mul 1
    · right; left; exact one_mul z
    · right; left; exact mul_one z
    · left; exact hz2
  ·
    exfalso
    have hc : Commute y y' := by
      rcases hye with h | h
      · rw [h]; exact Commute.one_left _
      · rw [h]
        rcases hyo' with h' | h'
        · rw [h']; exact hzu'
        · rw [h']; exact (Commute.refl z).mul_right hzu'
    apply hz1
    calc z = y' * y' := hyy'.symm
      _ = (y * y) * (y' * y') := by rw [hyy, one_mul]
      _ = (y * y') * (y * y') := by
          calc (y * y) * (y' * y') = y * (y * y') * y' := by group
            _ = y * (y' * y) * y' := by rw [hc.eq]
            _ = (y * y') * (y * y') := by group
      _ = 1 := hw
  ·
    exfalso
    have hc : Commute y y' := by
      rcases hye' with h' | h'
      · rw [h']; exact Commute.one_right _
      · rw [h']
        rcases hyo with h | h
        · rw [h]; exact hzu.symm
        · rw [h]; exact ((Commute.refl z).mul_right hzu).symm
    apply hz1
    calc z = y * y := hyy.symm
      _ = (y * y) * (y' * y') := by rw [hyy', mul_one]
      _ = (y * y') * (y * y') := by
          calc (y * y) * (y' * y') = y * (y * y') * y' := by group
            _ = y * (y' * y) * y' := by rw [hc.eq]
            _ = (y * y') * (y * y') := by group
      _ = 1 := hw
  ·
    rcases hyo with h | h <;> rcases hyo' with h' | h' <;> rw [h, h']
    · right; right; left; rfl
    · right; right; right
      calc u * (z * u') = (u * z) * u' := by group
        _ = (z * u) * u' := by rw [hzu.eq]
        _ = z * (u * u') := by group
    · right; right; right; exact mul_assoc _ _ _
    · right; right; left
      calc z * u * (z * u') = z * (u * z) * u' := by group
        _ = z * (z * u) * u' := by rw [hzu.eq]
        _ = (z * z) * (u * u') := by group
        _ = u * u' := by rw [hz2, one_mul]


theorem orb4_four_pow_eq {u z : G} (hu4 : orderOf u = 4) (hz : u * u = z) : z * z = 1 := by
  have h4 : u ^ 4 = 1 := by rw [← hu4]; exact pow_orderOf_eq_one u
  rw [← hz]
  calc u * u * (u * u) = u ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := h4

theorem orb4_commute_AD' [Finite G] {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) (S : Sylow 2 G)
    (hQ8 : ∀ P ∈ RSet Ω, IsQ8 P) {Ra Rb : Subgroup G} (hRa : Ra ∈ RSet Ω) (hRb : Rb ∈ RSet Ω)
    (hRaS : Ra ≤ (S : Subgroup G)) (hRbS : Rb ≤ (S : Subgroup G)) (hne : Ra ≠ Rb) {u u' z : G}
    (hua : u ∈ Ra) (hu4 : orderOf u = 4) (hub : u' ∈ Rb) (hu'4 : orderOf u' = 4)
    (hz : u * u = z) (hz' : u' * u' = z) {w : G} (hwP : w ∈ Ra ⊔ Rb) (hwu : w * u = u * w)
    (hwu' : w * u' = u' * w) (hww : w * w = 1) :
    w = 1 ∨ w = z ∨ w = u * u' ∨ w = z * (u * u') := by
  have hcomm : Commutes Ra Rb := orb4_rset_commutes hΩ S hRa hRb hRaS hRbS hne
  obtain ⟨y, hy, y', hy', rfl⟩ := exists_mul_of_mem_sup_of_commutes hcomm hwP
  have hyu : y * u = u * y := by
    have h2 : u * y' = y' * u := hcomm u hua y' hy'
    have : (y * u) * y' = (u * y) * y' := by
      calc (y * u) * y' = y * (u * y') := by group
        _ = y * (y' * u) := by rw [h2]
        _ = y * y' * u := by group
        _ = u * (y * y') := hwu
        _ = (u * y) * y' := by group
    exact mul_right_cancel this
  have hyu' : y' * u' = u' * y' := by
    have h2 : y * u' = u' * y := hcomm y hy u' hub
    have : y * (y' * u') = y * (u' * y') := by
      calc y * (y' * u') = y * y' * u' := by group
        _ = u' * (y * y') := hwu'
        _ = (u' * y) * y' := by group
        _ = (y * u') * y' := by rw [h2]
        _ = y * (u' * y') := by group
    exact mul_left_cancel this
  have hz2 : z * z = 1 := orb4_four_pow_eq hu4 hz
  have hz1 : z ≠ 1 := by rw [← hz]; exact orb4_sq_ne_one_of_orderOf_eq_four hu4
  exact orb4_d4_cases (hcomm u hua u' hub) hz hz' hz2 hz1 ((hQ8 Ra hRa).cent hua hu4 hy hyu)
    ((hQ8 Rb hRb).cent hub hu'4 hy' hyu') hww


theorem orb4_commutes_sup_left {A B C : Subgroup G} (hA : Commutes A C) (hB : Commutes B C) :
    Commutes (A ⊔ B) C := by
  have hle : A ⊔ B ≤ Subgroup.centralizer (C : Set G) :=
    sup_le (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => (hA x hx y hy).symm)
      (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => (hB x hx y hy).symm)
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (hle hx) y hy).symm

theorem orb4_commutes_sup_right {A B C : Subgroup G} (hA : Commutes C A) (hB : Commutes C B) :
    Commutes C (A ⊔ B) := (orb4_commutes_sup_left hA.symm hB.symm).symm

theorem orb4_center_pair {Ra Rb : Subgroup G} (hcomm : Commutes Ra Rb) (hqa : IsQ8 Ra) (hqb : IsQ8 Rb)
    {u u' z : G} (hua : u ∈ Ra) (hu4 : orderOf u = 4) (hub : u' ∈ Rb) (hu'4 : orderOf u' = 4)
    (hz : u * u = z) (hz' : u' * u' = z) (hz2 : z * z = 1) {v : G} (hv : v ∈ Ra ⊔ Rb)
    (hva : ∀ r ∈ Ra, r * v = v * r) (hvb : ∀ r ∈ Rb, r * v = v * r) : v = 1 ∨ v = z := by
  obtain ⟨y, hy, y', hy', rfl⟩ := exists_mul_of_mem_sup_of_commutes hcomm hv
  have hyc : ∀ r ∈ Ra, y * r = r * y := by
    intro r hr
    have h1 := hva r hr
    have h2 : r * y' = y' * r := hcomm r hr y' hy'
    have : (r * y) * y' = (y * r) * y' := by
      calc (r * y) * y' = r * (y * y') := by group
        _ = (y * y') * r := h1
        _ = y * (y' * r) := by group
        _ = y * (r * y') := by rw [h2]
        _ = (y * r) * y' := by group
    exact (mul_right_cancel this).symm
  have hyc' : ∀ r ∈ Rb, y' * r = r * y' := by
    intro r hr
    have h1 := hvb r hr
    have h2 : y * r = r * y := hcomm y hy r hr
    have : y * (r * y') = y * (y' * r) := by
      calc y * (r * y') = (y * r) * y' := by group
        _ = (r * y) * y' := by rw [h2]
        _ = r * (y * y') := by group
        _ = (y * y') * r := h1
        _ = y * (y' * r) := by group
    exact (mul_left_cancel this).symm
  rcases (hqa.central hua hu4 hy hyc) with h | h <;> rcases (hqb.central hub hu'4 hy' hyc') with h' | h'
  · left; rw [h, h', one_mul]
  · right; rw [h, h', hz', one_mul]
  · right; rw [h, h', hz, mul_one]
  · left; rw [h, h', hz, hz']; exact hz2

theorem orb4_comm4_id {a b c d : G} (hab : Commute a b) (had : Commute a d) (hbc : Commute b c)
    (hbd : Commute b d) (hcd : Commute c d) (hac : Commute a c) :
    ((a * b) * (c * d)) * (b * d) = ((b * b) * (d * d)) * (a * c) := by
  calc (a * b) * (c * d) * (b * d) = (a * c) * (b * d) * (b * d) := by
        rw [hbc.mul_mul_mul_comm a d]
    _ = (a * c) * ((b * d) * (b * d)) := by group
    _ = (a * c) * ((b * b) * (d * d)) := by rw [hbd.symm.mul_mul_mul_comm b d]
    _ = ((b * b) * (d * d)) * (a * c) := by
        have h1 : Commute (a * c) (b * b) :=
          (hab.mul_right hab).mul_left (hbc.symm.mul_right hbc.symm)
        have h2 : Commute (a * c) (d * d) :=
          (had.mul_right had).mul_left (hcd.mul_right hcd)
        exact (h1.mul_right h2).eq

theorem shape_commute [Finite G] {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) (S : Sylow 2 G)
    {W : Subgroup G} (hWn : ∀ s ∈ (S : Subgroup G), conjSub s W = W)
    (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hQ8 : ∀ P ∈ RSet Ω, IsQ8 P)
    {Ra Rb : Subgroup G} (hRa : Ra ∈ RSet Ω) (hRb : Rb ∈ RSet Ω)
    (hRaS : Ra ≤ (S : Subgroup G)) (hRbS : Rb ≤ (S : Subgroup G)) (hne : Ra ≠ Rb) {u u' z : G}
    (hua : u ∈ Ra) (huW : u ∈ W) (hu4 : orderOf u = 4) (hub : u' ∈ Rb) (hu'W : u' ∈ W)
    (hu'4 : orderOf u' = 4) (hz : u * u = z) (hz' : u' * u' = z) (t : G) :
    D4Shape (S : Subgroup G) t z (u * u') := by
  have hcomm : Commutes Ra Rb := orb4_rset_commutes hΩ S hRa hRb hRaS hRbS hne
  refine ⟨(Ra ⊔ Rb) ⊓ W, ?_, ?_, ?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [← hz]
      exact Subgroup.mem_sup_left (Ra.mul_mem hua hua)
    · rw [← hz]
      exact W.mul_mem huW huW
  · exact Subgroup.mem_inf.mpr ⟨(Ra ⊔ Rb).mul_mem (Subgroup.mem_sup_left hua)
      (Subgroup.mem_sup_right hub), W.mul_mem huW hu'W⟩
  · intro c hc hct hcd
    have hsupp : ∀ R ∈ RSet Ω, R ≤ (S : Subgroup G) → (R ∈ ({Ra, Rb} : Set (Subgroup G)) ↔
        ¬ ∀ r ∈ R, r * (u * u') = (u * u') * r) := by
      intro R hR hRS
      constructor
      · rintro (rfl | rfl)
        · have := orb4_not_all_commute (hQ8 _ hRa) (v := u) (a := 1) (b := u') hua hu4
            (fun r _ => by simp) (fun r hr => hcomm r hr u' hub)
          simpa using this
        · have := orb4_not_all_commute (hQ8 _ hRb) (v := u') (a := u) (b := 1) hub hu'4
            (fun r hr => (hcomm u hua r hr).symm) (fun r _ => by simp)
          simpa using this
      · intro hnot
        by_contra hR'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hR'
        apply hnot
        have hRa' := orb4_rset_commutes hΩ S hR hRa hRS hRaS hR'.1
        have hRb' := orb4_rset_commutes hΩ S hR hRb hRS hRbS hR'.2
        intro r hr
        exact ((show Commute r u from hRa' r hr u hua).mul_right
          (show Commute r u' from hRb' r hr u' hub)).eq
    have hP : conjSub c (Ra ⊔ Rb) = Ra ⊔ Rb := by
      have := orb4_conjSub_sSup_eq (𝒮 := {Ra, Rb}) (d := u * u') hΩ (S := (S : Subgroup G))
        (by
          rintro R (rfl | rfl)
          · exact ⟨hRa, hRaS⟩
          · exact ⟨hRb, hRbS⟩) hsupp hc hcd
      rwa [sSup_pair] at this
    rw [orb4_conjSub_inf, hP, hWn c hc]
  · intro w hw hww _
    exact orb4_commute_AD' hΩ S hQ8 hRa hRb hRaS hRbS hne hua hu4 hub hu'4 hz hz'
      (Subgroup.mem_inf.mp hw).1 (hWab _ (Subgroup.mem_inf.mp hw).2 u huW)
      (hWab _ (Subgroup.mem_inf.mp hw).2 u' hu'W) hww


theorem shape_noncommute [Finite G] {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) (S : Sylow 2 G)
    {W : Subgroup G} (hWn : ∀ s ∈ (S : Subgroup G), conjSub s W = W)
    (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hQ8 : ∀ P ∈ RSet Ω, IsQ8 P)
    {R₁ R₂ : Subgroup G} (hR₁ : R₁ ∈ RSet Ω) (hR₂ : R₂ ∈ RSet Ω)
    (hR₁S : R₁ ≤ (S : Subgroup G)) (hR₂S : R₂ ≤ (S : Subgroup G)) {t : G}
    (htS : t ∈ (S : Subgroup G)) (ht2 : t * t = 1) (hne₁₂ : R₁ ≠ R₂)
    (hne₁₃ : R₁ ≠ conjSub t R₁) (hne₁₄ : R₁ ≠ conjSub t R₂) (hne₂₃ : R₂ ≠ conjSub t R₁)
    (hne₂₄ : R₂ ≠ conjSub t R₂) {u u' z : G} (hu : u ∈ R₁) (huW : u ∈ W) (hu4 : orderOf u = 4)
    (hu' : u' ∈ R₂) (hu'W : u' ∈ W) (hu'4 : orderOf u' = 4) (hz : u * u = z) (hz' : u' * u' = z)
    (hzt : t * z * t⁻¹ ≠ z) :
    D4Shape (S : Subgroup G) t (z * (t * z * t⁻¹))
      ((u * (t * u * t⁻¹)) * (u' * (t * u' * t⁻¹))⁻¹) := by
  classical
  obtain ⟨R₃, hR₃def⟩ : ∃ R, R = conjSub t R₁ := ⟨_, rfl⟩
  obtain ⟨R₄, hR₄def⟩ : ∃ R, R = conjSub t R₂ := ⟨_, rfl⟩
  obtain ⟨u₃, hu₃def⟩ : ∃ y, y = t * u * t⁻¹ := ⟨_, rfl⟩
  obtain ⟨u₄, hu₄def⟩ : ∃ y, y = t * u' * t⁻¹ := ⟨_, rfl⟩
  obtain ⟨zt, hztdef⟩ : ∃ y, y = t * z * t⁻¹ := ⟨_, rfl⟩
  rw [← hR₃def] at hne₁₃ hne₂₃
  rw [← hR₄def] at hne₁₄ hne₂₄
  rw [← hu₃def, ← hu₄def, ← hztdef]
  rw [← hztdef] at hzt
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hR₃Ω : R₃ ∈ RSet Ω := hR₃def ▸ RSet.conj hΩ.conjInvariant hR₁ t
  have hR₄Ω : R₄ ∈ RSet Ω := hR₄def ▸ RSet.conj hΩ.conjInvariant hR₂ t
  have hR₃S : R₃ ≤ (S : Subgroup G) := hR₃def ▸ orb4_conjSub_le_of_mem htS hR₁S
  have hR₄S : R₄ ≤ (S : Subgroup G) := hR₄def ▸ orb4_conjSub_le_of_mem htS hR₂S
  have hne₃₄ : R₃ ≠ R₄ := by
    rw [hR₃def, hR₄def]
    exact fun h => hne₁₂ (conjSub_injective t h)
  have C12 := orb4_rset_commutes hΩ S hR₁ hR₂ hR₁S hR₂S hne₁₂
  have C13 := orb4_rset_commutes hΩ S hR₁ hR₃Ω hR₁S hR₃S hne₁₃
  have C14 := orb4_rset_commutes hΩ S hR₁ hR₄Ω hR₁S hR₄S hne₁₄
  have C23 := orb4_rset_commutes hΩ S hR₂ hR₃Ω hR₂S hR₃S hne₂₃
  have C24 := orb4_rset_commutes hΩ S hR₂ hR₄Ω hR₂S hR₄S hne₂₄
  have C34 := orb4_rset_commutes hΩ S hR₃Ω hR₄Ω hR₃S hR₄S hne₃₄
  have hu₃ : u₃ ∈ R₃ := hu₃def ▸ hR₃def ▸ conj_mem_conjSub hu
  have hu₄ : u₄ ∈ R₄ := hu₄def ▸ hR₄def ▸ conj_mem_conjSub hu'
  have hu₃W : u₃ ∈ W := by
    have := conj_mem_conjSub (n := t) huW
    rw [hWn t htS] at this
    rwa [hu₃def]
  have hu₄W : u₄ ∈ W := by
    have := conj_mem_conjSub (n := t) hu'W
    rw [hWn t htS] at this
    rwa [hu₄def]
  have hu₃4 : orderOf u₃ = 4 := by rw [hu₃def, orderOf_conj_mul_inv_eq]; exact hu4
  have hu₄4 : orderOf u₄ = 4 := by rw [hu₄def, orderOf_conj_mul_inv_eq]; exact hu'4
  have hzt₃ : u₃ * u₃ = zt := by rw [hu₃def, hztdef, ← hz]; group
  have hzt₄ : u₄ * u₄ = zt := by rw [hu₄def, hztdef, ← hz']; group
  have hz2 : z * z = 1 := orb4_four_pow_eq hu4 hz
  have hzt2 : zt * zt = 1 := orb4_four_pow_eq hu₃4 hzt₃
  have hz1 : z ≠ 1 := by rw [← hz]; exact orb4_sq_ne_one_of_orderOf_eq_four hu4
  have hc12 : Commute u u' := C12 u hu u' hu'
  have hc13 : Commute u u₃ := C13 u hu u₃ hu₃
  have hc14 : Commute u u₄ := C14 u hu u₄ hu₄
  have hc23 : Commute u' u₃ := C23 u' hu' u₃ hu₃
  have hc24 : Commute u' u₄ := C24 u' hu' u₄ hu₄
  have hc34 : Commute u₃ u₄ := C34 u₃ hu₃ u₄ hu₄
  have hsupp : ∀ R ∈ RSet Ω, R ≤ (S : Subgroup G) →
      (R ∈ ({R₁, R₂, R₃, R₄} : Set (Subgroup G)) ↔
        ¬ ∀ r ∈ R, r * ((u * u₃) * (u' * u₄)⁻¹) = ((u * u₃) * (u' * u₄)⁻¹) * r) := by
    intro R hR hRS
    constructor
    · rintro (h | h | h | h)
      · rw [h]
        have h1 := orb4_not_all_commute (hQ8 R₁ hR₁) (v := u) (a := 1)
          (b := u₃ * (u' * u₄)⁻¹) hu hu4 (fun r _ => by simp)
          (fun r hr => (((show Commute r u₃ from C13 r hr u₃ hu₃).mul_right
            (((show Commute r u' from C12 r hr u' hu').mul_right
              (show Commute r u₄ from C14 r hr u₄ hu₄)).inv_right))).eq)
        have e1 : (u * u₃) * (u' * u₄)⁻¹ = 1 * u * (u₃ * (u' * u₄)⁻¹) := by group
        rw [e1]
        exact h1
      · rw [h]
        have h1 := orb4_not_all_commute (hQ8 R₂ hR₂) (v := u'⁻¹) (a := u * u₃ * u₄⁻¹) (b := 1)
          (R₂.inv_mem hu') (by rw [orderOf_inv]; exact hu'4)
          (fun r hr => ((((show Commute r u from (C12 u hu r hr).symm).mul_right
            (show Commute r u₃ from C23 r hr u₃ hu₃)).mul_right
              (show Commute r u₄ from C24 r hr u₄ hu₄).inv_right)).eq)
          (fun r _ => by simp)
        have e1 : (u * u₃) * (u' * u₄)⁻¹ = (u * u₃ * u₄⁻¹) * u'⁻¹ * 1 := by group
        rw [e1]
        exact h1
      · rw [h]
        exact orb4_not_all_commute (hQ8 R₃ hR₃Ω) (v := u₃) (a := u) (b := (u' * u₄)⁻¹) hu₃ hu₃4
          (fun r hr => (C13 u hu r hr).symm)
          (fun r hr => (((show Commute r u' from (C23 u' hu' r hr).symm).mul_right
            (show Commute r u₄ from C34 r hr u₄ hu₄)).inv_right).eq)
      · rw [h]
        have h1 := orb4_not_all_commute (hQ8 R₄ hR₄Ω) (v := u₄⁻¹) (a := u * u₃) (b := u'⁻¹)
          (R₄.inv_mem hu₄) (by rw [orderOf_inv]; exact hu₄4)
          (fun r hr => (((show Commute r u from (C14 u hu r hr).symm).mul_right
            (show Commute r u₃ from (C34 u₃ hu₃ r hr).symm)).eq))
          (fun r hr => ((show Commute r u' from (C24 u' hu' r hr).symm).inv_right).eq)
        have e1 : (u * u₃) * (u' * u₄)⁻¹ = (u * u₃) * u₄⁻¹ * u'⁻¹ := by group
        rw [e1]
        exact h1
    · intro hnot
      by_contra hR'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hR'
      obtain ⟨h1, h2, h3, h4⟩ := hR'
      apply hnot
      have k1 := orb4_rset_commutes hΩ S hR hR₁ hRS hR₁S h1
      have k2 := orb4_rset_commutes hΩ S hR hR₂ hRS hR₂S h2
      have k3 := orb4_rset_commutes hΩ S hR hR₃Ω hRS hR₃S h3
      have k4 := orb4_rset_commutes hΩ S hR hR₄Ω hRS hR₄S h4
      intro r hr
      exact (((show Commute r u from k1 r hr u hu).mul_right (show Commute r u₃ from k3 r hr u₃ hu₃)).mul_right
        (((show Commute r u' from k2 r hr u' hu').mul_right
          (show Commute r u₄ from k4 r hr u₄ hu₄)).inv_right)).eq
  have hP : ∀ c ∈ (S : Subgroup G), c * ((u * u₃) * (u' * u₄)⁻¹) = ((u * u₃) * (u' * u₄)⁻¹) * c →
      conjSub c ((R₁ ⊔ R₂) ⊔ (R₃ ⊔ R₄)) = (R₁ ⊔ R₂) ⊔ (R₃ ⊔ R₄) := by
    intro c hc hcd
    have := orb4_conjSub_sSup_eq (𝒮 := {R₁, R₂, R₃, R₄}) (d := (u * u₃) * (u' * u₄)⁻¹) hΩ
      (S := (S : Subgroup G))
      (by
        rintro R (h | h | h | h) <;> rw [h]
        · exact ⟨hR₁, hR₁S⟩
        · exact ⟨hR₂, hR₂S⟩
        · exact ⟨hR₃Ω, hR₃S⟩
        · exact ⟨hR₄Ω, hR₄S⟩) hsupp hc hcd
    have e : sSup ({R₁, R₂, R₃, R₄} : Set (Subgroup G)) = (R₁ ⊔ R₂) ⊔ (R₃ ⊔ R₄) := by
      simp [sSup_insert, sup_assoc]
    rwa [e] at this
  have hPP' : Commutes (R₁ ⊔ R₂) (R₃ ⊔ R₄) :=
    orb4_commutes_sup_right (orb4_commutes_sup_left C13 C23) (orb4_commutes_sup_left C14 C24)
  have hinter : ∀ v, v ∈ R₁ ⊔ R₂ → v ∈ R₃ ⊔ R₄ → v = 1 := by
    intro v hv1 hv2
    have hva : ∀ r ∈ R₁, r * v = v * r := fun r hr =>
      hPP' r (Subgroup.mem_sup_left hr) v hv2
    have hvb : ∀ r ∈ R₂, r * v = v * r := fun r hr =>
      hPP' r (Subgroup.mem_sup_right hr) v hv2
    have hv3 : ∀ r ∈ R₃, r * v = v * r := fun r hr =>
      (hPP' v hv1 r (Subgroup.mem_sup_left hr)).symm
    have hv4 : ∀ r ∈ R₄, r * v = v * r := fun r hr =>
      (hPP' v hv1 r (Subgroup.mem_sup_right hr)).symm
    rcases orb4_center_pair C12 (hQ8 _ hR₁) (hQ8 _ hR₂) hu hu4 hu' hu'4 hz hz' hz2 hv1 hva hvb with h | h
    · exact h
    · rcases orb4_center_pair C34 (hQ8 _ hR₃Ω) (hQ8 _ hR₄Ω) hu₃ hu₃4 hu₄ hu₄4 hzt₃ hzt₄ hzt2 hv2 hv3
        hv4 with h' | h'
      · exact h'
      · exact absurd (h'.symm.trans h) hzt
  have hconjP : ∀ x ∈ R₃ ⊔ R₄, t * x * t⁻¹ ∈ R₁ ⊔ R₂ := by
    intro x hx
    have h3 : conjSub t R₃ = R₁ := by rw [hR₃def, ← conjSub_mul, ht2, conjSub_one]
    have h4 : conjSub t R₄ = R₂ := by rw [hR₄def, ← conjSub_mul, ht2, conjSub_one]
    have := conj_mem_conjSub (n := t) hx
    rwa [orb4_conjSub_sup, h3, h4] at this
  have hconjP' : ∀ x ∈ R₁ ⊔ R₂, t * x * t⁻¹ ∈ R₃ ⊔ R₄ := by
    intro x hx
    have := conj_mem_conjSub (n := t) hx
    rwa [orb4_conjSub_sup, ← hR₃def, ← hR₄def] at this
  have hd₁ : z * zt ∈ ((R₁ ⊔ R₂) ⊔ (R₃ ⊔ R₄)) ⊓ W := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ ?_ ?_, W.mul_mem ?_ ?_⟩
    · rw [← hz]; exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (R₁.mul_mem hu hu))
    · rw [← hzt₃]
      exact Subgroup.mem_sup_right (Subgroup.mem_sup_left (R₃.mul_mem hu₃ hu₃))
    · rw [← hz]; exact W.mul_mem huW huW
    · rw [← hzt₃]; exact W.mul_mem hu₃W hu₃W
  have hd₂ : (u * u₃) * (u' * u₄)⁻¹ ∈ ((R₁ ⊔ R₂) ⊔ (R₃ ⊔ R₄)) ⊓ W := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_)
      (Subgroup.inv_mem _ (Subgroup.mul_mem _ ?_ ?_)), W.mul_mem (W.mul_mem huW hu₃W)
        (W.inv_mem (W.mul_mem hu'W hu₄W))⟩
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hu)
    · exact Subgroup.mem_sup_right (Subgroup.mem_sup_left hu₃)
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hu')
    · exact Subgroup.mem_sup_right (Subgroup.mem_sup_right hu₄)
  have hczt : Commute z zt := by
    rw [← hz, ← hzt₃]
    exact (hc13.mul_right hc13).mul_left (hc13.mul_right hc13)
  have hdd : (z * zt) * (z * zt) = 1 := by
    calc (z * zt) * (z * zt) = z * (zt * z) * zt := by group
      _ = z * (z * zt) * zt := by rw [← hczt.eq]
      _ = (z * z) * (zt * zt) := by group
      _ = 1 := by rw [hz2, hzt2, one_mul]
  have hdN : (z * zt) * ((u * u₃) * (u' * u₄)⁻¹) = (u * u') * (u₃ * u₄) := by
    have h := orb4_comm4_id hc12 hc14 hc23 hc24 hc34 hc13
    rw [hz', hzt₄] at h
    calc (z * zt) * ((u * u₃) * (u' * u₄)⁻¹) = ((z * zt) * (u * u₃)) * (u' * u₄)⁻¹ := by group
      _ = (((u * u') * (u₃ * u₄)) * (u' * u₄)) * (u' * u₄)⁻¹ := by rw [h]
      _ = (u * u') * (u₃ * u₄) := by group
  have hczt' : Commute (u * u') zt := by
    rw [← hzt₃]
    exact (hc13.mul_right hc13).mul_left (hc23.mul_right hc23)
  refine ⟨((R₁ ⊔ R₂) ⊔ (R₃ ⊔ R₄)) ⊓ W, hd₁, hd₂, ?_, ?_⟩
  · intro c hc _ hcd
    rw [orb4_conjSub_inf, hP c hc hcd, hWn c hc]
  · intro w hw hww hwt
    obtain ⟨hwP, hwW⟩ := Subgroup.mem_inf.mp hw
    obtain ⟨a, ha, a', ha', rfl⟩ := exists_mul_of_mem_sup_of_commutes hPP' hwP
    have hp : t * a' * t⁻¹ ∈ R₁ ⊔ R₂ := hconjP a' ha'
    have hq : t * a * t⁻¹ ∈ R₃ ⊔ R₄ := hconjP' a ha
    have e1 : (t * a * t⁻¹) * (t * a' * t⁻¹) = a * a' := by
      calc (t * a * t⁻¹) * (t * a' * t⁻¹) = t * (a * a') * t⁻¹ := by group
        _ = a * a' := by rw [mul_inv_eq_iff_eq_mul]; exact hwt.symm
    have hcomm_pq : (t * a' * t⁻¹) * (t * a * t⁻¹) = (t * a * t⁻¹) * (t * a' * t⁻¹) :=
      hPP' _ hp _ hq
    have e2 : a * a' = (t * a' * t⁻¹) * (t * a * t⁻¹) := by rw [hcomm_pq, e1]
    have e3 : (t * a' * t⁻¹)⁻¹ * a = (t * a * t⁻¹) * a'⁻¹ := by
      calc (t * a' * t⁻¹)⁻¹ * a = (t * a' * t⁻¹)⁻¹ * (a * a') * a'⁻¹ := by group
        _ = (t * a' * t⁻¹)⁻¹ * ((t * a' * t⁻¹) * (t * a * t⁻¹)) * a'⁻¹ := by rw [← e2]
        _ = (t * a * t⁻¹) * a'⁻¹ := by group
    have e4 : (t * a' * t⁻¹)⁻¹ * a = 1 :=
      hinter _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hp) ha)
        (by rw [e3]; exact Subgroup.mul_mem _ hq (Subgroup.inv_mem _ ha'))
    have hap : a = t * a' * t⁻¹ := (inv_mul_eq_one.mp e4).symm
    have ha'q : a' = t * a * t⁻¹ := by
      rw [hap]
      calc a' = (t * t) * a' * (t * t)⁻¹ := by rw [ht2]; group
        _ = t * (t * a' * t⁻¹) * t⁻¹ := by group
    have haa : a * a = 1 := by
      have h1 : (a * a) * (a' * a') = 1 := by
        calc (a * a) * (a' * a') = a * (a * a') * a' := by group
          _ = a * (a' * a) * a' := by rw [hPP' a ha a' ha']
          _ = (a * a') * (a * a') := by group
          _ = 1 := hww
      have h2 : a * a = (a' * a')⁻¹ := eq_inv_of_mul_eq_one_left h1
      exact hinter _ (Subgroup.mul_mem _ ha ha)
        (by rw [h2]; exact Subgroup.inv_mem _ (Subgroup.mul_mem _ ha' ha'))
    have hau : a * u = u * a := by
      have h1 := hWab _ hwW u huW
      have h2 : u * a' = a' * u := hPP' u (Subgroup.mem_sup_left hu) a' ha'
      have : (a * u) * a' = (u * a) * a' := by
        calc (a * u) * a' = a * (u * a') := by group
          _ = a * (a' * u) := by rw [h2]
          _ = a * a' * u := by group
          _ = u * (a * a') := h1
          _ = (u * a) * a' := by group
      exact mul_right_cancel this
    have hau' : a * u' = u' * a := by
      have h1 := hWab _ hwW u' hu'W
      have h2 : u' * a' = a' * u' := hPP' u' (Subgroup.mem_sup_right hu') a' ha'
      have : (a * u') * a' = (u' * a) * a' := by
        calc (a * u') * a' = a * (u' * a') := by group
          _ = a * (a' * u') := by rw [h2]
          _ = a * a' * u' := by group
          _ = u' * (a * a') := h1
          _ = (u' * a) * a' := by group
      exact mul_right_cancel this
    rw [ha'q]
    rcases orb4_commute_AD' hΩ S hQ8 hR₁ hR₂ hR₁S hR₂S hne₁₂ hu hu4 hu' hu'4 hz hz' ha hau hau' haa
      with h | h | h | h
    · left
      rw [h]
      simp
    · right; left
      rw [h, ← hztdef]
    · right; right; right
      rw [h, hdN]
      have : t * (u * u') * t⁻¹ = u₃ * u₄ := by rw [hu₃def, hu₄def]; group
      rw [this]
    · right; right; left
      rw [h]
      have h1 : t * (z * (u * u')) * t⁻¹ = zt * (u₃ * u₄) := by
        rw [hztdef, hu₃def, hu₄def]; group
      rw [h1]
      calc z * (u * u') * (zt * (u₃ * u₄)) = z * ((u * u') * zt) * (u₃ * u₄) := by group
        _ = z * (zt * (u * u')) * (u₃ * u₄) := by rw [hczt'.eq]
        _ = (z * zt) * ((u * u') * (u₃ * u₄)) := by group
        _ = (z * zt) * ((z * zt) * ((u * u₃) * (u' * u₄)⁻¹)) := by rw [hdN]
        _ = ((z * zt) * (z * zt)) * ((u * u₃) * (u' * u₄)⁻¹) := by group
        _ = (u * u₃) * (u' * u₄)⁻¹ := by rw [hdd, one_mul]

end Shape

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
