module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open Subgroup

theorem index_ne_two_of_commutator_eq_top {E : Type*} [Group E] (hE : _root_.commutator E = ⊤)
    (N : Subgroup E) : N.index ≠ 2 := by
  intro hN
  haveI : N.Normal := Subgroup.normal_of_index_eq_two hN
  have hcard : Nat.card (E ⧸ N) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact hN
  haveI : IsCyclic (E ⧸ N) := isCyclic_of_prime_card hcard
  have hcomm : _root_.commutator E ≤ N :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp IsCyclic.isMulCommutative
  rw [hE] at hcomm
  have htop : N = ⊤ := top_le_iff.mp hcomm
  rw [htop, Subgroup.index_top] at hN
  exact absurd hN (by norm_num)

theorem card_centralizer_subtype_le {E : Type*} [Group E] [Finite E] (S : Subgroup E) (u : S) :
    Nat.card (centralizer ({u} : Set S)) ≤ Nat.card (centralizer ({(u : E)} : Set E)) := by
  let f : centralizer ({u} : Set S) → centralizer ({(u : E)} : Set E) := fun c =>
    ⟨(c : S), by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg (fun z : S => (z : E))
        (Subgroup.mem_centralizer_singleton_iff.mp c.2)⟩
  exact Nat.card_le_card_of_injective f fun a _ h => by
    exact Subtype.ext <| Subtype.ext <|
      congrArg (fun z : centralizer ({(u : E)} : Set E) => (z : E)) h

theorem card_centralizer_conj {E : Type*} [Group E] [Finite E] (x t : E) :
    Nat.card (centralizer ({x⁻¹ * t * x} : Set E)) = Nat.card (centralizer ({t} : Set E)) := by
  let f : centralizer ({x⁻¹ * t * x} : Set E) → centralizer ({t} : Set E) := fun z =>
    ⟨x * (z : E) * x⁻¹, by
      have hz := Subgroup.mem_centralizer_singleton_iff.mp z.2
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * (z : E) * x⁻¹ * t
          = x * ((z : E) * (x⁻¹ * t * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * t * x) * (z : E)) * x⁻¹ := by rw [hz]
        _ = t * (x * (z : E) * x⁻¹) := by group⟩
  let g : centralizer ({t} : Set E) → centralizer ({x⁻¹ * t * x} : Set E) := fun y =>
    ⟨x⁻¹ * (y : E) * x, by
      have hy := Subgroup.mem_centralizer_singleton_iff.mp y.2
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x⁻¹ * (y : E) * x * (x⁻¹ * t * x)
          = x⁻¹ * ((y : E) * t) * x := by group
        _ = x⁻¹ * (t * (y : E)) * x := by rw [hy]
        _ = x⁻¹ * t * x * (x⁻¹ * (y : E) * x) := by group⟩
  exact Nat.card_congr
    ⟨f, g, (fun z => Subtype.ext (by
        change x⁻¹ * (x * (z : E) * x⁻¹) * x = (z : E)
        group)),
     (fun y => Subtype.ext (by
        change x * (x⁻¹ * (y : E) * x) * x⁻¹ = (y : E)
        group))⟩

theorem card_centralizer_subtype_eq {E : Type*} [Group E] [Finite E] {S : Subgroup E} {t : E}
    (htS : t ∈ S) (hCS : centralizer ({t} : Set E) ≤ S) :
    Nat.card (centralizer ({(⟨t, htS⟩ : S)} : Set S)) = Nat.card (centralizer ({t} : Set E)) := by
  let f : centralizer ({(⟨t, htS⟩ : S)} : Set S) → centralizer ({t} : Set E) := fun c =>
    ⟨(c : S), by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg (fun z : S => (z : E))
        (Subgroup.mem_centralizer_singleton_iff.mp c.2)⟩
  refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro a _ h
    exact Subtype.ext <| Subtype.ext <|
      congrArg (fun z : centralizer ({t} : Set E) => (z : E)) h
  · intro y
    refine ⟨⟨⟨(y : E), hCS y.2⟩, ?_⟩, Subtype.ext rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2)

end CFSG.GroupTheory.SmallFixedTwoGroup
