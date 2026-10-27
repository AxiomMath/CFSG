module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Coord
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeData
public import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.EvenSmallLie.OmegaEight.CPrime

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type*} [Group G]

structure ShapeCPrime (t : G) (L : Subgroup G) (c : G) : Prop where
  orderOf_eq : orderOf t = 2
  sq : c * c = t
  not_mem : t ∉ L
  le_centralizer : L ≤ centralizer ({t} : Set G)
  involution_mem : ∀ h ∈ centralizer ({t} : Set G), h * h = 1 → h ∈ L ⊔ zpowers t
  not_mem_closure_odd : t ∉ closure {g : G | g * t = t * g ∧ Odd (orderOf g)}

structure CPrimeData (ε : Eps) (t : G) (U Q P : Subgroup G) (ψ : V6 → G) (c : G) (v₀ : ℕ) :
    Prop where
  v₀_lt : v₀ < 64
  v₀_nonsingular : qfB ε v₀ = true
  c_act : ∀ v, c * ψ v * c⁻¹ = ψ (toMat 6 6 (reflRows ε v₀) *ᵥ v)
  c_normalizes_U : ∀ u ∈ U, c * u * c⁻¹ ∈ U
  sylow : ∀ V : Subgroup G, V ≤ centralizer ({t} : Set G) → IsPGroup 2 V →
    U ⊔ zpowers c ≤ V → V = U ⊔ zpowers c
  centralizer_Q : centralizer ({t} : Set G) ⊓ centralizer (Q : Set G) ≤ Q ⊔ zpowers t
  normalizer_E : centralizer ({t} : Set G) ⊓ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) ≤
    P ⊔ zpowers c

structure Setting (ε : Eps) (t : G) (L U Q P : Subgroup G) (a : G) (ψ : V6 → G) (p : Fin 6 → G)
    (c : G) (v₀ : ℕ) : Prop where
  shape : ShapeCPrime t L c
  rad : RadicalData ε L U Q P a ψ p
  data : CPrimeData ε t U Q P ψ c v₀

namespace ShapeCPrime

variable {t c : G} {L : Subgroup G} (hS : ShapeCPrime t L c)
include hS

theorem mul_self : t * t = 1 := by
  rw [← pow_two, ← hS.orderOf_eq, pow_orderOf_eq_one]

theorem ne_one : t ≠ 1 := fun h => by
  have := hS.orderOf_eq
  rw [h, orderOf_one] at this
  exact absurd this (by decide)

theorem commute_of_mem {l : G} (hl : l ∈ L) : l * t = t * l :=
  mem_centralizer_singleton_iff.1 (hS.le_centralizer hl)

theorem c_comm : c * t = t * c := by
  rw [← hS.sq, mul_assoc]

theorem c_mem_centralizer : c ∈ centralizer ({t} : Set G) :=
  mem_centralizer_singleton_iff.2 hS.c_comm

theorem c_mul_c_mul_c_mul_c : c * c * (c * c) = 1 := by
  rw [hS.sq, hS.mul_self]

theorem c_inv : c⁻¹ = c * t := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← mul_assoc, hS.sq, hS.mul_self]

theorem c_pow_four : c ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_two c, hS.sq, pow_two, hS.mul_self]

theorem mem_zpowers_iff {z : G} : z ∈ zpowers t ↔ z = 1 ∨ z = t := by
  constructor
  · rintro ⟨k, rfl⟩
    change t ^ k = 1 ∨ t ^ k = t
    rw [← zpow_mod_orderOf, hS.orderOf_eq]
    rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [Nat.cast_ofNat, h]
    · exact Or.inl (zpow_zero t)
    · exact Or.inr (zpow_one t)
  · rintro (h | h) <;> rw [h]
    · exact one_mem _
    · exact mem_zpowers t

theorem commute_sup {X : Subgroup G} (hXL : X ≤ L) : ∀ u ∈ X, ∀ z ∈ zpowers t, u * z = z * u := by
  intro u hu z hz
  rcases hS.mem_zpowers_iff.1 hz with rfl | rfl
  · rw [mul_one, one_mul]
  · exact hS.commute_of_mem (hXL hu)

theorem mem_sup_iff {X : Subgroup G} (hXL : X ≤ L) {x : G} :
    x ∈ X ⊔ zpowers t ↔ ∃ u ∈ X, x = u ∨ x = u * t := by
  constructor
  · intro hx
    obtain ⟨u, hu, z, hz, rfl⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute (hS.commute_sup hXL) hx
    rcases hS.mem_zpowers_iff.1 hz with rfl | rfl
    · exact ⟨u, hu, Or.inl (mul_one u)⟩
    · exact ⟨u, hu, Or.inr rfl⟩
  · rintro ⟨u, hu, rfl | rfl⟩
    · exact mem_sup_left hu
    · exact mul_mem (mem_sup_left hu) (mem_sup_right (mem_zpowers t))

theorem mul_self_mem {X : Subgroup G} (hXL : X ≤ L) {x : G} (hx : x ∈ X ⊔ zpowers t) :
    x * x ∈ X := by
  obtain ⟨u, hu, rfl | rfl⟩ := (hS.mem_sup_iff hXL).1 hx
  · exact mul_mem hu hu
  · have h : u * t * (u * t) = u * u * (t * t) := by
      rw [mul_assoc u t, ← mul_assoc t u, ← hS.commute_of_mem (hXL hu), mul_assoc u t t,
        ← mul_assoc u u]
    rw [h, hS.mul_self, mul_one]
    exact mul_mem hu hu

theorem c_not_mem : c ∉ L ⊔ zpowers t := fun h =>
  hS.not_mem (hS.sq ▸ hS.mul_self_mem le_rfl h)

theorem conj_not_mem (hodd : InvolutionsInOddPart L) (g : G) : g * t * g⁻¹ ∉ L := by
  intro hu
  set u : L := ⟨g * t * g⁻¹, hu⟩ with hudef
  have hu2 : orderOf u = 2 := by
    rw [hudef, Subgroup.orderOf_mk, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hS.orderOf_eq]
  have hle : closure {y : L | y * u = u * y ∧ Odd (orderOf y)} ≤
      (closure {x : G | x * t = t * x ∧ Odd (orderOf x)}).comap
        (((MulAut.conj g⁻¹).toMonoidHom).comp L.subtype) := by
    rw [closure_le]
    rintro y ⟨hyu, hyo⟩
    have hyu' : (y : G) * (g * t * g⁻¹) = g * t * g⁻¹ * y := congrArg Subtype.val hyu
    refine subset_closure ⟨?_, ?_⟩
    · change g⁻¹ * y * g⁻¹⁻¹ * t = t * (g⁻¹ * y * g⁻¹⁻¹)
      rw [inv_inv]
      calc g⁻¹ * y * g * t = g⁻¹ * ((y : G) * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * t * g⁻¹ * y) * g := by rw [hyu']
        _ = t * (g⁻¹ * y * g) := by group
    · change Odd (orderOf (MulAut.conj g⁻¹ (y : G)))
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe]
      exact hyo
  have h := hle (hodd u hu2)
  rw [mem_comap, MonoidHom.coe_comp, Function.comp_apply, coe_subtype, hudef,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h
  apply hS.not_mem_closure_odd
  convert h using 1
  group

end ShapeCPrime

end CFSG.EvenSmallLie.OmegaEight.CPrime
