module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Setup
public import CFSG.LocalAnalysis.OddStandard.Seitz77FusionGen
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped commutatorElement

section Defs

structure Radicals {G : Type*} [Group G] (V V₁ V₂ : Subgroup G) : Prop where
  le₁ : V₁ ≤ V
  le₂ : V₂ ≤ V
  normal₁ : (V₁.subgroupOf V).Normal
  normal₂ : (V₂.subgroupOf V).Normal
  elem₁ : IsElemAbelian 2 V₁
  elem₂ : IsElemAbelian 2 V₂
  card₁ : Nat.card V₁ = 16
  card₂ : Nat.card V₂ = 16
  inf_eq : V₁ ⊓ V₂ = V ⊓ centralizer (V : Set G)
  sup_eq : V₁ ⊔ V₂ = V
  card_center : Nat.card ↥(V ⊓ centralizer (V : Set G)) = 4
  le_of_elem : ∀ E : Subgroup G, E ≤ V → IsElemAbelian 2 E → E ≤ V₁ ∨ E ≤ V₂
  eq_of_card : ∀ E : Subgroup G, E ≤ V → IsElemAbelian 2 E → Nat.card E = 16 → E = V₁ ∨ E = V₂
  le_of_sq : ∀ x ∈ V, x ^ 2 = 1 → x ∈ V₁ ∨ x ∈ V₂

structure Facts {G : Type*} [Group G] [Finite G] (A : Subgroup G) : Prop where
  odd_inf : Odd (Nat.card ↥(A ⊓ centralizer (A : Set G)))
  invol_conj : ∀ x ∈ A, ∀ y ∈ A, orderOf x = 2 → orderOf y = 2 → ∃ a ∈ A, a * x * a⁻¹ = y
  elem_inner : ∀ E : Subgroup G, E ≤ normalizer (A : Set G) → IsElemAbelian 2 E →
    16 * Nat.card ↥(E ⊓ centralizer (A : Set G)) ≤ Nat.card E →
      E ≤ A ⊔ centralizer (A : Set G)
  cent_V : ∀ V : Subgroup G, IsSylowOf 2 V A →
    normalizer (A : Set G) ⊓ centralizer (V : Set G) ≤
      (V ⊓ centralizer (V : Set G)) ⊔ centralizer (A : Set G)
  radicals : ∀ V : Subgroup G, IsSylowOf 2 V A → ∃ V₁ V₂ : Subgroup G, Radicals V V₁ V₂
  outer_fuse : ∀ y ∈ normalizer (A : Set G), y * y = 1 → y ∉ A ⊔ centralizer (A : Set G) →
    ∀ c ∈ A ⊓ centralizer ({y} : Set G), c * c = 1 → ∃ b ∈ A, b * y * b⁻¹ = y * c
  outer_core : ∀ y ∈ normalizer (A : Set G), y * y = 1 → y ∉ A ⊔ centralizer (A : Set G) →
    ¬ Group.IsSolvable ↥(A ⊓ centralizer ({y} : Set G)) →
      ∃ D : Subgroup G, D ≤ A ⊓ centralizer ({y} : Set G) ∧ ⁅D, D⁆ = D ∧
        ∃ c ∈ D, c * c = 1 ∧ c ≠ 1
  perfect_inv : ∀ D : Subgroup G, D ≤ normalizer (A : Set G) → ⁅D, D⁆ = D →
    ∀ c ∈ D, c * c = 1 → c ∈ A

end Defs

namespace Datum

section Basic

variable {G : Type*} [Group G] {A : Subgroup G} (d : Datum A)

abbrev V : Subgroup G := d.P ⊓ A

abbrev CU : Subgroup G := (d.V ⊓ centralizer (d.V : Set G)) ⊓ centralizer (d.P : Set G)

@[expose] def Alpha : Prop :=
  ∃ t' ∈ d.P ⊓ centralizer (d.P : Set G), IsConj d.t t' ∧ t' ≠ d.t

theorem t_mul_self : d.t * d.t = 1 := by
  have h : d.t ^ 2 = 1 := by rw [← d.sector.t_order]; exact pow_orderOf_eq_one d.t
  rwa [sq] at h

theorem t_mem_K : d.t ∈ centralizer (A : Set G) := t_mem_centralizer d.sector

theorem comm_t_of_mem {a : G} (ha : a ∈ A) : a * d.t = d.t * a :=
  mem_centralizer_iff.mp d.t_mem_K a ha

theorem V_comm_t {v : G} (hv : v ∈ d.V) : v * d.t = d.t * v := d.comm_t_of_mem hv.2

theorem mul_self_of_isConj {x : G} (hx : IsConj d.t x) : x * x = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hx
  calc c * d.t * c⁻¹ * (c * d.t * c⁻¹) = c * (d.t * d.t) * c⁻¹ := by group
    _ = 1 := by rw [d.t_mul_self]; group

theorem conj_mem_V {n : G} (hn : n ∈ d.P) {v : G} (hv : v ∈ d.V) : n * v * n⁻¹ ∈ d.V :=
  ⟨d.P.mul_mem (d.P.mul_mem hn hv.1) (d.P.inv_mem hn),
    (mem_normalizer_iff.mp (d.hP.le hn) v).mp hv.2⟩

end Basic

section Sylow

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G} (d : Datum A)

theorem V_isSylow : IsSylowOf 2 d.V A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact d.hP.inf_of_le_normalizer le_normalizer le_rfl

theorem P_comm_t {x : G} (hx : x ∈ d.P) : x * d.t = d.t * x :=
  mem_centralizer_singleton_iff.mp (d.P_le_centralizer hx)

theorem t_mem_centralizer_P : d.t ∈ centralizer (d.P : Set G) :=
  mem_centralizer_iff.mpr fun _ hx => d.P_comm_t hx

end Sylow

end Datum

namespace Radicals

variable {G : Type*} [Group G] {V V₁ V₂ : Subgroup G}

theorem property (hR : Radicals V V₁ V₂) {W : Subgroup G} (hW : W = V₁ ∨ W = V₂) :
    W ≤ V ∧ IsElemAbelian 2 W ∧ Nat.card W = 16 := by
  rcases hW with rfl | rfl
  · exact ⟨hR.le₁, hR.elem₁, hR.card₁⟩
  · exact ⟨hR.le₂, hR.elem₂, hR.card₂⟩

theorem ne (hR : Radicals V V₁ V₂) : V₁ ≠ V₂ := by
  intro h
  have h1 := hR.card_center
  rw [← hR.inf_eq, ← h, inf_idem, hR.card₁] at h1
  omega

theorem exists_noncomm [Finite G] (hR : Radicals V V₁ V₂) : ∃ x ∈ V, ∃ y ∈ V, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  have hle : V ≤ centralizer (V : Set G) := fun x hx => mem_centralizer_iff.mpr fun y hy =>
    hcon y hy x hx
  have h1 : V ⊓ centralizer (V : Set G) = V := inf_eq_left.mpr hle
  have h2 : Nat.card V₁ ≤ Nat.card ↥(V ⊓ centralizer (V : Set G)) := by
    rw [h1]
    exact Subgroup.card_le_of_le hR.le₁
  rw [hR.card_center, hR.card₁] at h2
  omega

theorem mul_self_of_mem_center (hR : Radicals V V₁ V₂) {u : G}
    (hu : u ∈ V ⊓ centralizer (V : Set G)) : u * u = 1 := by
  rw [← hR.inf_eq] at hu
  rw [← sq]
  exact hR.elem₁.2 u hu.1

end Radicals

section ElemGen

variable {G : Type*} [Group G]

theorem isElemAbelian_of_le {E H : Subgroup G} (hE : IsElemAbelian 2 E) (hle : H ≤ E) :
    IsElemAbelian 2 H := CFSG.Open.IsElemAbelian.mono hE hle

end ElemGen


namespace Facts

section Core1

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G}

theorem false_of_mem_inf (F : Facts A) {x : G} (hx2 : orderOf x = 2) (hxA : x ∈ A)
    (hxK : x ∈ centralizer (A : Set G)) : False := by
  have h1 : 2 ∣ Nat.card ↥(A ⊓ centralizer (A : Set G)) := by
    have := Subgroup.orderOf_dvd_natCard (A ⊓ centralizer (A : Set G)) ⟨hxA, hxK⟩
    rwa [hx2] at this
  exact (Nat.not_even_iff_odd.2 F.odd_inf) (even_iff_two_dvd.2 h1)

theorem t_not_mem_A (F : Facts A) (d : Datum A) : d.t ∉ A :=
  fun h => F.false_of_mem_inf d.sector.t_order h d.t_mem_K

theorem t_not_mem_V (F : Facts A) (d : Datum A) : d.t ∉ d.V := fun h => F.t_not_mem_A d h.2

theorem eq_one_or_eq_t (d : Datum A) {r : G} (hr : r ∈ d.P ⊓ centralizer (A : Set G))
    (hr2 : r * r = 1) : r = 1 ∨ r = d.t := by
  by_cases hr1 : r = 1
  · exact Or.inl hr1
  · refine Or.inr (eq_t_of_orderOf_eq_two d.sector ?_ ?_)
    · rw [← d.P_inf_centralizer_eq]
      exact hr
    · exact orderOf_eq_prime (by rw [sq]; exact hr2) hr1

theorem decomp_of_mul_self (F : Facts A) (d : Datum A) {x : G} (hxP : x ∈ d.P)
    (hxA : x ∈ A ⊔ centralizer (A : Set G)) (hx2 : x * x = 1) :
    ∃ v ∈ d.V, ∃ r ∈ d.P ⊓ centralizer (A : Set G), x = v * r ∧ v * v = 1 ∧ r * r = 1 := by
  obtain ⟨a, ha, k, hk, rfl⟩ :=
    mem_sup_of_commute (fun a ha k hk => mem_centralizer_iff.mp hk a ha) hxA
  have hak : a * k = k * a := mem_centralizer_iff.mp hk a ha
  have haa : a * a * (k * k) = 1 := by
    calc a * a * (k * k) = a * (a * k) * k := by group
      _ = a * (k * a) * k := by rw [hak]
      _ = (a * k) * (a * k) := by group
      _ = 1 := hx2
  have hzK : a * a ∈ centralizer (A : Set G) := by
    rw [eq_inv_of_mul_eq_one_left haa]
    exact inv_mem (mul_mem hk hk)
  obtain ⟨j, hj⟩ := F.odd_inf
  have hzm : (a * a) ^ Nat.card ↥(A ⊓ centralizer (A : Set G)) = 1 := by
    have := pow_card_eq_one' (G := ↥(A ⊓ centralizer (A : Set G)))
      (x := ⟨a * a, mul_mem ha ha, hzK⟩)
    exact congrArg Subtype.val this
  rw [hj] at hzm
  have hv_eq : a ^ (2 * j + 1) = (a * a) ^ j * a := by rw [pow_succ, pow_mul, sq]
  have hv2 : a ^ (2 * j + 1) * a ^ (2 * j + 1) = 1 := by
    rw [← pow_add, show 2 * j + 1 + (2 * j + 1) = 2 * (2 * j + 1) by ring, pow_mul, sq]
    exact hzm
  have hvA : a ^ (2 * j + 1) ∈ A := pow_mem ha _
  have hconjA : ∀ u ∈ d.V, a * u * a⁻¹ ∈ d.V := by
    intro u hu
    have h1 := d.conj_mem_V hxP hu
    have hku : k * u * k⁻¹ = u := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (mem_centralizer_iff.mp hk u hu.2).symm
    have : a * k * u * (a * k)⁻¹ = a * u * a⁻¹ := by
      calc a * k * u * (a * k)⁻¹ = a * (k * u * k⁻¹) * a⁻¹ := by group
        _ = a * u * a⁻¹ := by rw [hku]
    rwa [this] at h1
  have hzjK : (a * a) ^ j ∈ centralizer (A : Set G) := pow_mem hzK j
  have hvconj : ∀ u ∈ d.V, a ^ (2 * j + 1) * u * (a ^ (2 * j + 1))⁻¹ ∈ d.V := by
    intro u hu
    have hcomm : ∀ y ∈ A, (a * a) ^ j * y = y * (a * a) ^ j := fun y hy =>
      (mem_centralizer_iff.mp hzjK y hy).symm
    have hy : a * u * a⁻¹ ∈ A := mul_mem (mul_mem ha hu.2) (inv_mem ha)
    have : a ^ (2 * j + 1) * u * (a ^ (2 * j + 1))⁻¹ = a * u * a⁻¹ := by
      rw [hv_eq]
      calc (a * a) ^ j * a * u * ((a * a) ^ j * a)⁻¹
          = (a * a) ^ j * (a * u * a⁻¹) * ((a * a) ^ j)⁻¹ := by group
        _ = (a * u * a⁻¹) * (a * a) ^ j * ((a * a) ^ j)⁻¹ := by rw [hcomm _ hy]
        _ = a * u * a⁻¹ := by group
    rw [this]
    exact hconjA u hu
  have hvV : a ^ (2 * j + 1) ∈ d.V :=
    mem_of_mul_self_of_normalizes d.V_isSylow hvA hv2 hvconj
  refine ⟨a ^ (2 * j + 1), hvV, a ^ (2 * j + 1) * (a * k), ⟨?_, ?_⟩, ?_, hv2, ?_⟩
  · exact d.P.mul_mem hvV.1 hxP
  · have : a ^ (2 * j + 1) * (a * k) = (a * a) ^ (j + 1) * k := by
      rw [← mul_assoc, ← pow_succ, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, pow_mul, sq]
    rw [this]
    exact mul_mem (pow_mem hzK _) hk
  · rw [← mul_assoc, hv2, one_mul]
  · have hvk : a ^ (2 * j + 1) * k = k * a ^ (2 * j + 1) := mem_centralizer_iff.mp hk _ hvA
    have hvx : a ^ (2 * j + 1) * (a * k) = (a * k) * a ^ (2 * j + 1) := by
      calc a ^ (2 * j + 1) * (a * k) = (a ^ (2 * j + 1) * a) * k := by rw [mul_assoc]
        _ = (a * a ^ (2 * j + 1)) * k := by rw [(Commute.self_pow a (2 * j + 1)).eq]
        _ = a * (a ^ (2 * j + 1) * k) := by rw [mul_assoc]
        _ = a * (k * a ^ (2 * j + 1)) := by rw [hvk]
        _ = (a * k) * a ^ (2 * j + 1) := by rw [mul_assoc]
    have key : ∀ w y : G, w * y = y * w → w * w = 1 → y * y = 1 → w * y * (w * y) = 1 := by
      intro w y hwy hw hy
      calc w * y * (w * y) = w * (y * w) * y := by group
        _ = w * (w * y) * y := by rw [← hwy]
        _ = (w * w) * (y * y) := by group
        _ = 1 := by rw [hw, hy, one_mul]
    exact key _ _ hvx hv2 hx2

end Core1

end Facts

namespace Facts

section Elem

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G}

theorem elem_mem_V_or (F : Facts A) (d : Datum A) {E : Subgroup G} (hEP : E ≤ d.P)
    (hE : IsElemAbelian 2 E) (hcard : 32 ≤ Nat.card E) {x : G} (hx : x ∈ E) :
    x ∈ d.V ∨ x * d.t ∈ d.V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEK : Nat.card ↥(E ⊓ centralizer (A : Set G)) ≤ 2 := by
    have hle : E ⊓ centralizer (A : Set G) ≤ zpowers d.t := by
      intro y hy
      have hy2 : y * y = 1 := by rw [← sq]; exact hE.2 y hy.1
      rcases eq_one_or_eq_t d ⟨hEP hy.1, hy.2⟩ hy2 with rfl | rfl
      · exact one_mem _
      · exact mem_zpowers _
    have := Subgroup.card_le_of_le hle
    rwa [Nat.card_zpowers, d.sector.t_order] at this
  have hEA : E ≤ A ⊔ centralizer (A : Set G) :=
    F.elem_inner E (hEP.trans d.P_le_normalizer) hE (by omega)
  have hx2 : x * x = 1 := by rw [← sq]; exact hE.2 x hx
  obtain ⟨v, hv, r, hr, rfl, -, hr2⟩ := F.decomp_of_mul_self d (hEP hx) (hEA hx) hx2
  rcases eq_one_or_eq_t d hr hr2 with rfl | rfl
  · exact Or.inl (by rwa [mul_one])
  · refine Or.inr ?_
    have ht2 := d.t_mul_self
    rwa [mul_assoc, ht2, mul_one]

end Elem

end Facts

end CFSG.OddStandard.Seitz77
