module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage0Basic
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitCDefs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage0

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.SplitC
open CFSG.EvenSmallLie.OmegaEight.CPrime

variable {G : Type} [Group G]

structure StepK (t : G) (L : Subgroup G) : Prop where
  orderOf_eq : orderOf t = 2
  mem_centralizer : t ∈ centralizer (L : Set G)
  not_mem : t ∉ L
  inf_eq : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t
  le_centralizer : L ≤ centralizer ({t} : Set G)
  le_normalizer : centralizer ({t} : Set G) ≤ normalizer (L : Set G)

@[expose] def InvolutionLifting (L : Type*) [Group L] : Prop :=
  ∀ α : MulAut L, α ∉ inner L → α * α ∈ inner L →
    ∃ β : MulAut L, β * β = 1 ∧ α⁻¹ * β ∈ inner L

structure ShapeB (t : G) (L : Subgroup G) (r : G) : Prop where
  split : ShapeSplit t L (L ⊔ zpowers r)
  r_mem : r ∈ centralizer ({t} : Set G)
  r_not_mem : r ∉ L ⊔ zpowers t
  r_pow : r ^ 3 ∈ L ⊔ zpowers t
  r_order : ∃ k : ℕ, orderOf r = 3 ^ k
  relIndex_eq : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) = 3

structure ShapeC (t : G) (L : Subgroup G) (b : G) : Prop where
  split : ShapeSplit t L (L ⊔ zpowers b)
  b_mem : b ∈ centralizer ({t} : Set G)
  b_sq : b * b = 1
  b_not_mem : b ∉ L ⊔ zpowers t
  relIndex_eq : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) = 2

structure ShapeD (t : G) (L : Subgroup G) (b r : G) : Prop where
  split : ShapeSplit t L (L ⊔ zpowers r ⊔ zpowers b)
  b_mem : b ∈ centralizer ({t} : Set G)
  b_sq : b * b = 1
  b_not_mem : b ∉ L ⊔ zpowers t
  r_mem : r ∈ centralizer ({t} : Set G)
  r_not_mem : r ∉ L ⊔ zpowers t
  r_pow : r ^ 3 ∈ L ⊔ zpowers t
  r_order : ∃ k : ℕ, orderOf r = 3 ^ k
  normal : ∀ h ∈ centralizer ({t} : Set G), ∀ x ∈ L ⊔ zpowers r, h * x * h⁻¹ ∈ L ⊔ zpowers r
  relIndex_sup : (L ⊔ zpowers t ⊔ zpowers r).relIndex (centralizer ({t} : Set G)) = 2
  relIndex_eq : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) = 6

structure ShapeC' (t : G) (L : Subgroup G) (c : G) : Prop where
  cprime : ShapeCPrime t L c
  c_mem_normalizer : c ∈ normalizer (L : Set G)
  centralizer_eq : centralizer ({t} : Set G) = L ⊔ zpowers c
  c_not_mem : c ∉ L ⊔ zpowers t
  relIndex_eq : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) = 2

structure ShapeD' (t : G) (L : Subgroup G) (c r : G) : Prop where
  cprime : ShapeCPrime t L c
  c_not_mem : c ∉ L ⊔ zpowers t
  r_mem : r ∈ centralizer ({t} : Set G)
  r_not_mem : r ∉ L ⊔ zpowers t
  r_pow : r ^ 3 ∈ L ⊔ zpowers t
  r_order : ∃ k : ℕ, orderOf r = 3 ^ k
  le_centralizer : L ⊔ zpowers r ≤ centralizer ({t} : Set G)
  t_not_mem : t ∉ L ⊔ zpowers r
  c_mem_normalizer : c ∈ normalizer ((L ⊔ zpowers r : Subgroup G) : Set G)
  centralizer_eq : centralizer ({t} : Set G) = L ⊔ zpowers r ⊔ zpowers c
  odd : ∀ x ∈ L ⊔ zpowers r, x * x ∈ L → x ∈ L
  le_normalizer : L ⊔ zpowers r ≤ normalizer (L : Set G)
  relIndex_sup : (L ⊔ zpowers t ⊔ zpowers r).relIndex (centralizer ({t} : Set G)) = 2
  relIndex_eq : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) = 6

namespace StepK

variable {t : G} {L : Subgroup G} (hK : StepK t L)
include hK

theorem mul_self : t * t = 1 := by
  rw [← pow_two, ← hK.orderOf_eq, pow_orderOf_eq_one]

theorem commute_of_mem {l : G} (hl : l ∈ L) : l * t = t * l :=
  mem_centralizer_singleton_iff.1 (hK.le_centralizer hl)

theorem mem_zpowers_iff {z : G} : z ∈ zpowers t ↔ z = 1 ∨ z = t := by
  constructor
  · rintro ⟨k, rfl⟩
    change t ^ k = 1 ∨ t ^ k = t
    rw [← zpow_mod_orderOf, hK.orderOf_eq]
    rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [Nat.cast_ofNat, h]
    · exact Or.inl (zpow_zero t)
    · exact Or.inr (zpow_one t)
  · rintro (h | h) <;> rw [h]
    · exact one_mem _
    · exact mem_zpowers t

omit hK in
theorem t_mem_centralizer : t ∈ centralizer ({t} : Set G) :=
  mem_centralizer_singleton_iff.2 rfl

theorem sup_le_centralizer : L ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
  sup_le hK.le_centralizer (zpowers_le.2 t_mem_centralizer)

theorem mem_sup_iff {x : G} : x ∈ L ⊔ zpowers t ↔ ∃ l ∈ L, x = l ∨ x = l * t := by
  constructor
  · intro hx
    obtain ⟨u, hu, z, hz, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun u hu z hz => by
        rcases hK.mem_zpowers_iff.1 hz with rfl | rfl
        · rw [mul_one, one_mul]
        · exact hK.commute_of_mem hu) hx
    rcases hK.mem_zpowers_iff.1 hz with rfl | rfl
    · exact ⟨u, hu, Or.inl (mul_one u)⟩
    · exact ⟨u, hu, Or.inr rfl⟩
  · rintro ⟨u, hu, rfl | rfl⟩
    · exact mem_sup_left hu
    · exact mul_mem (mem_sup_left hu) (mem_sup_right (mem_zpowers t))

theorem eq_one_of_mem {z : G} (hzL : z ∈ L) (hz : z ∈ zpowers t) : z = 1 := by
  rcases hK.mem_zpowers_iff.1 hz with h | h
  · exact h
  · exact absurd (h ▸ hzL) hK.not_mem

theorem conj_mem_sup {h : G} (hh : h ∈ centralizer ({t} : Set G)) {y : G}
    (hy : y ∈ L ⊔ zpowers t) : h * y * h⁻¹ ∈ L ⊔ zpowers t := by
  have hhL := hK.le_normalizer hh
  have ht : h * t = t * h := mem_centralizer_singleton_iff.1 hh
  obtain ⟨l, hl, rfl | rfl⟩ := hK.mem_sup_iff.1 hy
  · exact mem_sup_left ((mem_normalizer_iff.1 hhL y).1 hl)
  · have e : h * (l * t) * h⁻¹ = h * l * h⁻¹ * t := by
      calc h * (l * t) * h⁻¹ = h * l * h⁻¹ * (h * t * h⁻¹) := by group
        _ = h * l * h⁻¹ * t := by rw [ht, mul_inv_cancel_right]
    rw [e]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.1 hhL l).1 hl))
      (mem_sup_right (mem_zpowers t))

theorem relIndex_L : L.relIndex (L ⊔ zpowers t) = 2 := by
  rw [relIndex_eq_two_iff]
  refine ⟨t, mem_sup_right (mem_zpowers t), fun x hx => ?_⟩
  obtain ⟨l, hl, rfl | rfl⟩ := hK.mem_sup_iff.1 hx
  · exact Or.inr ⟨hl, fun h => hK.not_mem (by simpa using L.mul_mem (L.inv_mem hl) h)⟩
  · rw [mul_assoc, hK.mul_self, mul_one]
    exact Or.inl ⟨hl, fun h => hK.not_mem (by simpa using L.mul_mem (L.inv_mem hl) h)⟩

theorem mul_conj_mem {h : G} (hh : h ∈ centralizer ({t} : Set G)) {y : G}
    (hy : y ∈ L ⊔ zpowers t) : y * (h * y * h⁻¹) ∈ L := by
  have hhL := hK.le_normalizer hh
  have ht : h * t = t * h := mem_centralizer_singleton_iff.1 hh
  obtain ⟨l, hl, rfl | rfl⟩ := hK.mem_sup_iff.1 hy
  · exact L.mul_mem hl ((mem_normalizer_iff.1 hhL y).1 hl)
  · have hl' : h * l * h⁻¹ ∈ L := (mem_normalizer_iff.1 hhL l).1 hl
    have e : l * t * (h * (l * t) * h⁻¹) = l * (h * l * h⁻¹) := by
      calc l * t * (h * (l * t) * h⁻¹) = l * t * (h * l * h⁻¹ * (h * t * h⁻¹)) := by group
        _ = l * (t * (h * l * h⁻¹)) * t := by rw [ht, mul_inv_cancel_right]; group
        _ = l * (h * l * h⁻¹ * t) * t := by rw [hK.commute_of_mem hl']
        _ = l * (h * l * h⁻¹) * (t * t) := by group
        _ = l * (h * l * h⁻¹) := by rw [hK.mul_self, mul_one]
    rw [e]
    exact L.mul_mem hl hl'

theorem not_mem_sup_of_odd {r : G} (hr : r ∈ normalizer (L : Set G)) (ho : Odd (orderOf r)) :
    t ∉ L ⊔ zpowers r := by
  intro h
  obtain ⟨l, hl, n, hln⟩ := (mem_sup_zpowers_iff hr).1 h
  have h1 : r ^ n = l⁻¹ * t := by rw [hln]; group
  have h2 : (l⁻¹ * t) ^ orderOf r = 1 := by
    rw [← h1, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
      one_zpow]
  obtain ⟨k, hk⟩ := ho
  have hc : Commute l⁻¹ t := hK.commute_of_mem (L.inv_mem hl)
  rw [hc.mul_pow, hk, pow_succ t, pow_mul, sq, hK.mul_self, one_pow, one_mul] at h2
  apply hK.not_mem
  rw [eq_inv_of_mul_eq_one_right h2]
  exact L.inv_mem (L.pow_mem (L.inv_mem hl) _)

theorem mul_sq_eq {x m : G} (hx : x ∈ centralizer ({t} : Set G)) (hx2 : x * x ∈ zpowers t)
    (hm : m ∈ L) (hc : x * m * (x * m) ∈ centralizer (L : Set G)) :
    x * m * (x * m) = x * x := by
  have hxm : x * m ∈ centralizer ({t} : Set G) := mul_mem hx (hK.le_centralizer hm)
  have hy : x * m * (x * m) ∈ zpowers t := by
    rw [← hK.inf_eq]
    exact ⟨hc, mul_mem hxm hxm⟩
  have hl : x⁻¹ * m * x * m ∈ L := by
    have := (mem_normalizer_iff.1 (hK.le_normalizer (inv_mem hx)) m).1 hm
    rw [inv_inv] at this
    exact mul_mem this hm
  have e : (x * x)⁻¹ * (x * m * (x * m)) = x⁻¹ * m * x * m := by group
  have h1 : (x * x)⁻¹ * (x * m * (x * m)) = 1 :=
    hK.eq_one_of_mem (e ▸ hl) (mul_mem (inv_mem hx2) hy)
  calc x * m * (x * m) = x * x * ((x * x)⁻¹ * (x * m * (x * m))) := by group
    _ = x * x := by rw [h1, mul_one]

end StepK

end CFSG.EvenSmallLie.OmegaEight.Stage0
