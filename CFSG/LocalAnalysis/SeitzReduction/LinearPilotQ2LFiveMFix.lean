module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveFFactor
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup

variable {G : Type*} [Group G]

section CommConj

variable {S : Subgroup G} {y : G}

@[expose] def commConjHom (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hy : y ∈ normalizer (S : Set G)) : S →* S where
  toFun s := ⟨(s : G) * (y * s * y⁻¹), S.mul_mem s.2 ((mem_normalizer_iff.1 hy s).1 s.2)⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    have hya : y * (a : G) * y⁻¹ ∈ S := (mem_normalizer_iff.1 hy a).1 a.2
    have hc : (b : G) * (y * a * y⁻¹) = (y * a * y⁻¹) * b := hS _ b.2 _ hya
    show (a : G) * b * (y * (a * b) * y⁻¹) = (a : G) * (y * a * y⁻¹) * ((b : G) * (y * b * y⁻¹))
    calc (a : G) * b * (y * (a * b) * y⁻¹)
        = a * ((b : G) * (y * a * y⁻¹)) * (y * b * y⁻¹) := by group
      _ = a * ((y * a * y⁻¹) * b) * (y * b * y⁻¹) := by rw [hc]
      _ = (a : G) * (y * a * y⁻¹) * ((b : G) * (y * b * y⁻¹)) := by group

theorem commConjHom_apply (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hy : y ∈ normalizer (S : Set G)) (s : S) :
    (commConjHom hS hy s : G) = (s : G) * (y * s * y⁻¹) :=
  rfl

theorem commConjHom_eq_one_iff (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hS2 : ∀ s ∈ S, s * s = 1) (hy : y ∈ normalizer (S : Set G)) (s : S) :
    commConjHom hS hy s = 1 ↔ (s : G) ∈ centralizer ({y} : Set G) := by
  rw [mem_centralizer_singleton_iff, ← Subtype.coe_inj, commConjHom_apply, Subgroup.coe_one]
  have hsinv : (s : G)⁻¹ = s := inv_eq_of_mul_eq_one_right (hS2 s s.2)
  constructor
  · intro h
    have h1 : y * (s : G) * y⁻¹ = s := by rw [eq_inv_of_mul_eq_one_right h, hsinv]
    calc (s : G) * y = y * s * y⁻¹ * y := by rw [h1]
      _ = y * s := by group
  · intro h
    have h1 : y * (s : G) * y⁻¹ = s := by rw [← h]; group
    rw [h1]
    exact hS2 s s.2

theorem commConjHom_mem_centralizer (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hy : y ∈ normalizer (S : Set G)) (hy2 : y * y ∈ centralizer (S : Set G)) (s : S) :
    (commConjHom hS hy s : G) ∈ centralizer ({y} : Set G) := by
  rw [mem_centralizer_singleton_iff, commConjHom_apply]
  have hys : y * (s : G) * y⁻¹ ∈ S := (mem_normalizer_iff.1 hy s).1 s.2
  have hc : (s : G) * (y * s * y⁻¹) = (y * s * y⁻¹) * s := hS _ s.2 _ hys
  have h2 : (s : G) * (y * y) = (y * y) * s := mem_centralizer_iff.1 hy2 s s.2
  calc (s : G) * (y * s * y⁻¹) * y = (y * s * y⁻¹) * s * y := by rw [hc]
    _ = y * s * (y⁻¹ * (s * (y * y)) * y⁻¹) := by group
    _ = y * s * (y⁻¹ * ((y * y) * s) * y⁻¹) := by rw [h2]
    _ = y * ((s : G) * (y * s * y⁻¹)) := by group

theorem card_inf_centralizer_mul_card_range [Finite G]
    (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hS2 : ∀ s ∈ S, s * s = 1)
    (hy : y ∈ normalizer (S : Set G)) :
    Nat.card (S ⊓ centralizer ({y} : Set G) : Subgroup G) *
      Nat.card ((commConjHom hS hy).range.map S.subtype) = Nat.card S := by
  have hker : (commConjHom hS hy).ker.map S.subtype = S ⊓ centralizer ({y} : Set G) := by
    ext g
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact mem_inf.2 ⟨s.2, (commConjHom_eq_one_iff hS hS2 hy s).1 (MonoidHom.mem_ker.1 hs)⟩
    · intro hg
      obtain ⟨hgS, hgy⟩ := mem_inf.1 hg
      exact ⟨⟨g, hgS⟩, MonoidHom.mem_ker.2 ((commConjHom_eq_one_iff hS hS2 hy ⟨g, hgS⟩).2 hgy),
        rfl⟩
  rw [← hker, Subgroup.card_map_of_injective S.subtype_injective,
    Subgroup.card_map_of_injective S.subtype_injective]
  exact Subgroup.card_ker_mul_card_range _

theorem map_range_commConjHom_le (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hy : y ∈ normalizer (S : Set G)) (hy2 : y * y ∈ centralizer (S : Set G)) :
    (commConjHom hS hy).range.map S.subtype ≤ S ⊓ centralizer ({y} : Set G) := by
  rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
  exact mem_inf.2 ⟨(commConjHom hS hy s).2, commConjHom_mem_centralizer hS hy hy2 s⟩

theorem le_normalizer_map_range_commConjHom (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hy : y ∈ normalizer (S : Set G)) {X : Subgroup G} (hXS : X ≤ normalizer (S : Set G))
    (hXy : ∀ x ∈ X, x * y * x⁻¹ * y⁻¹ ∈ centralizer (S : Set G)) :
    X ≤ normalizer (((commConjHom hS hy).range.map S.subtype : Subgroup G) : Set G) := by
  apply le_normalizer_of_mul_mul_inv_mem
  rintro x hx _ ⟨_, ⟨s, rfl⟩, rfl⟩
  have hs' : x * (s : G) * x⁻¹ ∈ S := (mem_normalizer_iff.1 (hXS hx) s).1 s.2
  refine ⟨_, ⟨⟨x * s * x⁻¹, hs'⟩, rfl⟩, ?_⟩
  have hys' : y * (x * (s : G) * x⁻¹) * y⁻¹ ∈ S := (mem_normalizer_iff.1 hy _).1 hs'
  have hcomm : (y * (x * (s : G) * x⁻¹) * y⁻¹) * (x * y * x⁻¹ * y⁻¹) =
      (x * y * x⁻¹ * y⁻¹) * (y * (x * (s : G) * x⁻¹) * y⁻¹) :=
    mem_centralizer_iff.1 (hXy x hx) _ hys'
  have key : x * (y * (s : G) * y⁻¹) * x⁻¹ =
      (x * y * x⁻¹ * y⁻¹) * (y * (x * (s : G) * x⁻¹) * y⁻¹) * (x * y * x⁻¹ * y⁻¹)⁻¹ := by
    group
  have hcu : (x * y * x⁻¹ * y⁻¹) * (y * (x * (s : G) * x⁻¹) * y⁻¹) * (x * y * x⁻¹ * y⁻¹)⁻¹ =
      y * (x * (s : G) * x⁻¹) * y⁻¹ := by
    rw [← hcomm, mul_inv_cancel_right]
  show (x * (s : G) * x⁻¹) * (y * (x * s * x⁻¹) * y⁻¹) = x * ((s : G) * (y * s * y⁻¹)) * x⁻¹
  calc (x * (s : G) * x⁻¹) * (y * (x * s * x⁻¹) * y⁻¹)
      = (x * s * x⁻¹) * (x * (y * (s : G) * y⁻¹) * x⁻¹) := by rw [key, hcu]
    _ = x * ((s : G) * (y * s * y⁻¹)) * x⁻¹ := by group

theorem le_normalizer_inf_centralizer_singleton_of_comm {X : Subgroup G}
    (hXS : X ≤ normalizer (S : Set G))
    (hXy : ∀ x ∈ X, x * y * x⁻¹ * y⁻¹ ∈ centralizer (S : Set G)) :
    X ≤ normalizer ((S ⊓ centralizer ({y} : Set G) : Subgroup G) : Set G) := by
  apply le_normalizer_of_mul_mul_inv_mem
  intro x hx g hg
  obtain ⟨hgS, hgy⟩ := mem_inf.1 hg
  refine mem_inf.2 ⟨(mem_normalizer_iff.1 (hXS hx) g).1 hgS, ?_⟩
  rw [mem_centralizer_singleton_iff] at hgy ⊢
  have hc := hXy x⁻¹ (X.inv_mem hx)
  rw [inv_inv] at hc
  have hgc : g * (x⁻¹ * y * x * y⁻¹) = (x⁻¹ * y * x * y⁻¹) * g := mem_centralizer_iff.1 hc g hgS
  calc x * g * x⁻¹ * y = x * (g * (x⁻¹ * y * x * y⁻¹)) * y * x⁻¹ := by group
    _ = x * ((x⁻¹ * y * x * y⁻¹) * g) * y * x⁻¹ := by rw [hgc]
    _ = y * x * y⁻¹ * (g * y) * x⁻¹ := by group
    _ = y * x * y⁻¹ * (y * g) * x⁻¹ := by rw [hgy]
    _ = y * (x * g * x⁻¹) := by group

end CommConj

section Involution

variable {W X : Subgroup G}

theorem mem_normalizer_of_conj_mem_finite [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem le_normalizer_inf_of_le_normalizer_both {A B : Subgroup G}
    (hA : X ≤ normalizer (A : Set G)) (hB : X ≤ normalizer (B : Set G)) :
    X ≤ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  apply le_normalizer_of_mul_mul_inv_mem
  intro x hx g hg
  obtain ⟨hgA, hgB⟩ := mem_inf.1 hg
  exact mem_inf.2 ⟨(mem_normalizer_iff.1 (hA hx) g).1 hgA, (mem_normalizer_iff.1 (hB hx) g).1 hgB⟩

end Involution

section Bound

variable {U X : Subgroup G}

@[expose] def conjPermNeOne (hXU : X ≤ normalizer (U : Set G)) :
    X →* Equiv.Perm {u : U // u ≠ 1} where
  toFun x :=
    { toFun := fun u => ⟨⟨(x : G) * u * (x : G)⁻¹, (mem_normalizer_iff.1 (hXU x.2) u).1 u.1.2⟩,
        fun h => u.2 (Subtype.ext (by
          have h' : (x : G) * u * (x : G)⁻¹ = 1 := congrArg Subtype.val h
          calc ((u : U) : G) = (x : G)⁻¹ * ((x : G) * u * (x : G)⁻¹) * x := by group
            _ = 1 := by rw [h']; group))⟩
      invFun := fun u => ⟨⟨(x : G)⁻¹ * u * x, by
          have h := (mem_normalizer_iff.1 (hXU (X.inv_mem x.2)) u).1 u.1.2
          rwa [inv_inv] at h⟩,
        fun h => u.2 (Subtype.ext (by
          have h' : (x : G)⁻¹ * u * x = 1 := congrArg Subtype.val h
          calc ((u : U) : G) = (x : G) * ((x : G)⁻¹ * u * x) * (x : G)⁻¹ := by group
            _ = 1 := by rw [h']; group))⟩
      left_inv := fun u => by
        apply Subtype.ext
        apply Subtype.ext
        show (x : G)⁻¹ * ((x : G) * u * (x : G)⁻¹) * x = u
        group
      right_inv := fun u => by
        apply Subtype.ext
        apply Subtype.ext
        show (x : G) * ((x : G)⁻¹ * u * x) * (x : G)⁻¹ = u
        group }
  map_one' := by
    ext u
    show (1 : G) * u * (1 : G)⁻¹ = u
    group
  map_mul' x z := by
    ext u
    show (x : G) * z * u * ((x : G) * z)⁻¹ = (x : G) * ((z : G) * u * (z : G)⁻¹) * (x : G)⁻¹
    group

theorem natCard_subtype_ne_one [Finite G] : Nat.card {u : U // u ≠ 1} = Nat.card U - 1 := by
  classical
  have := Fintype.ofFinite U
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (fun x => x = 1), Fintype.card_subtype_eq]

theorem nine_le_of_le_factorial {n : ℕ} (h : 20160 ≤ (n - 1).factorial) : 9 ≤ n := by
  by_contra hn
  have h1 : n - 1 ≤ 7 := by omega
  have h2 := Nat.factorial_le h1
  have h3 : Nat.factorial 7 = 5040 := by decide
  omega

end Bound

end CFSG.SeitzReduction.LinearPilot
