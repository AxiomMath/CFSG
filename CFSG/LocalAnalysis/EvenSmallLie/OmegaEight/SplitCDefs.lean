module

public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Coord

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitC

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type*} [Group G]

structure ShapeSplit (t : G) (L H₀ : Subgroup G) : Prop where
  orderOf_eq : orderOf t = 2
  le_centralizer : H₀ ≤ centralizer ({t} : Set G)
  not_mem : t ∉ H₀
  centralizer_eq : centralizer ({t} : Set G) = H₀ ⊔ zpowers t
  L_le : L ≤ H₀

structure SplitData (t : G) (H₀ U Q S₀ : Subgroup G) : Prop where
  S₀_le : S₀ ≤ H₀
  U_le : U ≤ S₀
  pgroup : IsPGroup 2 S₀
  le_normalizer : S₀ ≤ normalizer (Q : Set G)
  sylow : ∀ V : Subgroup G, V ≤ centralizer ({t} : Set G) → IsPGroup 2 V →
    S₀ ⊔ zpowers t ≤ V → V = S₀ ⊔ zpowers t
  centralizer_Q : centralizer ({t} : Set G) ⊓ centralizer (Q : Set G) ≤ Q ⊔ zpowers t

structure Setting (ε : Eps) (t : G) (L H₀ U Q P S₀ : Subgroup G) (a : G) (ψ : V6 → G)
    (p : Fin 6 → G) : Prop where
  shape : ShapeSplit t L H₀
  rad : RadicalData ε L U Q P a ψ p
  data : SplitData t H₀ U Q S₀

namespace ShapeSplit

variable {t : G} {L H₀ : Subgroup G} (hS : ShapeSplit t L H₀)
include hS

theorem mul_self : t * t = 1 := by
  rw [← pow_two, ← hS.orderOf_eq, pow_orderOf_eq_one]

theorem ne_one : t ≠ 1 := fun h => by
  have := hS.orderOf_eq
  rw [h, orderOf_one] at this
  exact absurd this (by decide)

theorem commute_of_mem {h : G} (hh : h ∈ H₀) : h * t = t * h :=
  mem_centralizer_singleton_iff.1 (hS.le_centralizer hh)

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

theorem commute_sup {X : Subgroup G} (hX : X ≤ H₀) : ∀ u ∈ X, ∀ c ∈ zpowers t, u * c = c * u := by
  intro u hu c hc
  rcases hS.mem_zpowers_iff.1 hc with rfl | rfl
  · rw [mul_one, one_mul]
  · exact hS.commute_of_mem (hX hu)

theorem mem_sup_iff {X : Subgroup G} (hX : X ≤ H₀) {x : G} :
    x ∈ X ⊔ zpowers t ↔ ∃ u ∈ X, x = u ∨ x = u * t := by
  constructor
  · intro hx
    obtain ⟨u, hu, z, hz, rfl⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute (hS.commute_sup hX) hx
    rcases hS.mem_zpowers_iff.1 hz with rfl | rfl
    · exact ⟨u, hu, Or.inl (mul_one u)⟩
    · exact ⟨u, hu, Or.inr rfl⟩
  · rintro ⟨u, hu, rfl | rfl⟩
    · exact mem_sup_left hu
    · exact mul_mem (mem_sup_left hu) (mem_sup_right (mem_zpowers t))

theorem mul_t_not_mem {u : G} (hu : u ∈ H₀) : u * t ∉ H₀ := fun h =>
  hS.not_mem (by simpa using H₀.mul_mem (H₀.inv_mem hu) h)

theorem sup_inf_eq {X : Subgroup G} (hX : X ≤ H₀) : (X ⊔ zpowers t) ⊓ H₀ = X := by
  refine le_antisymm (fun x ⟨hx, hxH⟩ => ?_) (le_inf le_sup_left hX)
  obtain ⟨u, hu, rfl | rfl⟩ := (hS.mem_sup_iff hX).1 hx
  · exact hu
  · exact absurd hxH (hS.mul_t_not_mem (hX hu))

theorem isPGroup_sup {X : Subgroup G} (hX : X ≤ H₀) (hU : IsPGroup 2 X) :
    IsPGroup 2 (X ⊔ zpowers t : Subgroup G) := by
  rintro ⟨x, hx⟩
  obtain ⟨u, hu, z, hz, rfl⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute (hS.commute_sup hX) hx
  obtain ⟨k, hk⟩ := hU ⟨u, hu⟩
  have hk' : u ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hz2 : z ^ 2 = 1 := by
    rcases hS.mem_zpowers_iff.1 hz with rfl | rfl
    · exact one_pow 2
    · rw [pow_two, hS.mul_self]
  have hc : Commute u z := hS.commute_sup hX u hu z hz
  refine ⟨k + 1, Subtype.ext ?_⟩
  change (u * z) ^ 2 ^ (k + 1) = 1
  rw [hc.mul_pow, pow_succ, pow_mul u, hk', one_pow, one_mul, pow_mul' z, hz2, one_pow]

theorem relIndex_sup {X : Subgroup G} (hX : X ≤ H₀) : X.relIndex (X ⊔ zpowers t) = 2 := by
  rw [relIndex_eq_two_iff]
  refine ⟨t, mem_sup_right (mem_zpowers t), fun b hb => ?_⟩
  obtain ⟨u, hu, rfl | rfl⟩ := (hS.mem_sup_iff hX).1 hb
  · exact Or.inr ⟨hu, fun h => hS.not_mem (hX (by simpa using X.mul_mem (X.inv_mem hu) h))⟩
  · rw [mul_assoc, hS.mul_self, mul_one]
    exact Or.inl ⟨hu, fun h => hS.not_mem (hX (by simpa using X.mul_mem (X.inv_mem hu) h))⟩

theorem card_sup {X : Subgroup G} (hX : X ≤ H₀) :
    Nat.card (X ⊔ zpowers t : Subgroup G) = 2 * Nat.card X := by
  rw [← Subgroup.relIndex_mul_card (H := X) (K := X ⊔ zpowers t), hS.relIndex_sup hX,
    inf_of_le_left le_sup_left]

theorem mem_of_odd {g : G} (hg : g * t = t * g) (ho : Odd (orderOf g)) : g ∈ H₀ := by
  have hgC : g ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hg
  rw [hS.centralizer_eq] at hgC
  obtain ⟨u, hu, rfl | rfl⟩ := (hS.mem_sup_iff le_rfl).1 hgC
  · exact hu
  · exfalso
    obtain ⟨m, hm⟩ := ho
    have hc : Commute u t := hS.commute_of_mem hu
    have h1 : (u * t) ^ orderOf (u * t) = 1 := pow_orderOf_eq_one _
    have ht : t ^ orderOf (u * t) = t := by
      rw [hm, pow_succ, pow_mul, pow_two, hS.mul_self, one_pow, one_mul]
    rw [hc.mul_pow, ht] at h1
    apply hS.not_mem
    have h2 : t = (u ^ orderOf (u * t))⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact H₀.inv_mem (H₀.pow_mem hu _)

theorem not_mem_closure_odd : t ∉ closure {g : G | g * t = t * g ∧ Odd (orderOf g)} := by
  intro h
  have hle : closure {g : G | g * t = t * g ∧ Odd (orderOf g)} ≤ H₀ := by
    rw [closure_le]
    rintro g ⟨hg, ho⟩
    exact hS.mem_of_odd hg ho
  exact hS.not_mem (hle h)

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

end ShapeSplit

end CFSG.EvenSmallLie.OmegaEight.SplitC
