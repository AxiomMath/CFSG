module

public import CFSG.GH74.Uniqueness.SU.SU13TC5Main
public import CFSG.GH74.Uniqueness.SU.SU13TC2Ord

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

structure Ctx9 (G : Type) [Group G] [Finite G] (z : G) where
  L : Loc9 G z
  hz : orderOf z = 2
  l : Lem232 z L.e
  l3 : Lem233 z L.e L.E.E
  hWc : WAbel L.e
  hW5 : Nat.card (oc (centralizer ({L.e.s₁} : Set G))) = 3 ^ 5
  h39 : 3 ^ 9 ∣ Nat.card G

namespace Ctx9

variable {G : Type} [Group G] [Finite G] {z : G} (X : Ctx9 G z)

abbrev C : Subgroup G := centralizer ({X.L.e.s₂} : Set G)

abbrev Y : Subgroup G := oc X.C

abbrev E : Subgroup G := X.L.E.E

abbrev A : Subgroup G := Asub X.L.E X.hWc

abbrev Zy : Subgroup G := X.Y ⊓ centralizer (X.Y : Set G)

theorem Y_card : Nat.card X.Y = 3 ^ 7 := X.l3.Y_card

theorem Y_le_C : X.Y ≤ X.C := oc_le _

theorem conj_Y {c y : G} (hc : c ∈ X.C) (hy : y ∈ X.Y) : c * y * c⁻¹ ∈ X.Y := conj_mem_oc hc hy

theorem s₂_mem_Y : X.L.e.s₂ ∈ X.Y := zpowers_le_oc_cent X.L.e.s₂_ord (mem_zpowers _)

theorem E_le_Y : X.E ≤ X.Y := X.l3.E_le

theorem odd_orderOf {g : G} (hg : g ∈ X.Y) : Odd (Nat.card X.Y) → Odd (orderOf g) := fun h => by
  have h1 : orderOf (⟨g, hg⟩ : X.Y) ∣ Nat.card X.Y := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h1
  exact Odd.of_dvd_nat h h1

end Ctx9

variable {G : Type} [Group G] [Finite G] {z : G}

theorem lattice_num_a3 (n j : ℕ) (hj : j ≤ 3) (h : n * 3 ^ 2 = (3 ^ j) ^ 3) :
    n = 3 ∨ n = 3 ^ 4 ∨ n = 3 ^ 7 := by
  interval_cases j <;> omega

theorem lattice_num_a1 (n j : ℕ) (hj : j ≤ 3) (hn : n ≤ 3 ^ 7) (h : n * 1 ^ 2 = (3 ^ j) ^ 3) :
    n = 1 ∨ n = 3 ^ 3 ∨ n = 3 ^ 6 := by
  interval_cases j <;> omega

theorem lattice_orders (X : Ctx9 G z) {N : Subgroup G} (hNY : N ≤ X.Y)
    (hNC : ∀ c ∈ X.C, ∀ n ∈ N, c * n * c⁻¹ ∈ N) :
    (X.L.e.s₂ ∈ N → Nat.card N = 3 ∨ Nat.card N = 3 ^ 4 ∨ Nat.card N = 3 ^ 7) ∧
    (X.L.e.s₂ ∉ N → Nat.card N = 1 ∨ Nat.card N = 3 ^ 3 ∨ Nat.card N = 3 ^ 6) := by
  have hLL := lattice_card X.hz X.L.e X.l X.L.m hNY hNC
  have hNYc : Nat.card N ≤ 3 ^ 7 := X.Y_card ▸ Subgroup.card_le_of_le hNY
  have hcz : (N ⊓ centralizer ({z} : Set G) : Subgroup G) ≤ X.E := by
    intro x hx
    have hx' : x ∈ oc (centralizer ({X.L.e.s₂} : Set G)) ⊓ centralizer ({z} : Set G) :=
      mem_inf.mpr ⟨hNY (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩
    rw [X.l3.Y_cent] at hx'
    exact hx'
  have hcdvd : Nat.card (N ⊓ centralizer ({z} : Set G) : Subgroup G) ∣ 3 ^ 3 := by
    have := Subgroup.card_dvd_of_le hcz
    rwa [X.L.E.E_card, show (27 : ℕ) = 3 ^ 3 by norm_num] at this
  obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hcdvd
  have hs₂ord : Nat.card (zpowers X.L.e.s₂) = 3 := by rw [Nat.card_zpowers, X.L.e.s₂_ord]
  have hadvd : Nat.card (N ⊓ zpowers X.L.e.s₂ : Subgroup G) ∣ 3 := by
    have := Subgroup.card_dvd_of_le (inf_le_right : (N ⊓ zpowers X.L.e.s₂ : Subgroup G) ≤ zpowers X.L.e.s₂)
    rwa [hs₂ord] at this
  have hjc' : Nat.card (N ⊓ centralizer ({z} : Set G) : Subgroup G) = 3 ^ j := hjc
  constructor
  · intro hs
    have ha : Nat.card (N ⊓ zpowers X.L.e.s₂ : Subgroup G) = 3 := by
      have hle : zpowers X.L.e.s₂ ≤ N := (zpowers_le).mpr hs
      rw [inf_eq_right.mpr hle, hs₂ord]
    rw [ha, hjc'] at hLL
    exact lattice_num_a3 _ j hj hLL
  · intro hs
    have ha : Nat.card (N ⊓ zpowers X.L.e.s₂ : Subgroup G) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hadvd with h | h
      · exact h
      · exfalso
        apply hs
        have hle : (N ⊓ zpowers X.L.e.s₂ : Subgroup G) ≤ zpowers X.L.e.s₂ := inf_le_right
        have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [h, hs₂ord])
        have : X.L.e.s₂ ∈ (N ⊓ zpowers X.L.e.s₂ : Subgroup G) := by
          rw [heq]; exact mem_zpowers _
        exact (mem_inf.mp this).1
    rw [ha, hjc'] at hLL
    exact lattice_num_a1 _ j hj hNYc hLL

namespace Ctx9

variable (X : Ctx9 G z)

theorem s₂_mem_Zy : X.L.e.s₂ ∈ X.Zy := by
  refine mem_inf.mpr ⟨X.s₂_mem_Y, mem_centralizer_iff.mpr fun y hy => ?_⟩
  exact mem_centralizer_singleton_iff.mp (X.Y_le_C hy)

theorem conj_Zy {c n : G} (hc : c ∈ X.C) (hn : n ∈ X.Zy) : c * n * c⁻¹ ∈ X.Zy := by
  obtain ⟨hnY, hnc⟩ := mem_inf.mp hn
  refine mem_inf.mpr ⟨X.conj_Y hc hnY, mem_centralizer_iff.mpr fun y hy => ?_⟩
  have hy' : c⁻¹ * y * c ∈ X.Y := by
    have := X.conj_Y (X.C.inv_mem hc) hy
    simpa using this
  have h1 := (mem_centralizer_iff.mp hnc) _ hy'
  calc y * (c * n * c⁻¹) = c * ((c⁻¹ * y * c) * n) * c⁻¹ := by group
    _ = c * (n * (c⁻¹ * y * c)) * c⁻¹ := by rw [h1]
    _ = (c * n * c⁻¹) * y := by group

theorem Zy_le_A : X.Zy ≤ X.A := by
  intro g hg
  obtain ⟨hgY, hgc⟩ := mem_inf.mp hg
  obtain ⟨a, ha, h | h⟩ := cent_E_le X.L.f X.L.E X.hWc X.hz X.hW5 X.l (g := g) (fun x hx => by
    have := (mem_centralizer_iff.mp hgc) x (X.E_le_Y hx)
    exact this.symm)
  · rw [h]; exact ha
  · exfalso
    have hodd : Odd (orderOf g) := X.odd_orderOf hgY (odd_card_oc _)
    rw [h] at hodd
    exact not_odd_orderOf_mul_z X.L.f X.L.E X.hWc X.hz X.hW5 ha hodd

theorem card_Zy_le : Nat.card X.Zy ≤ 3 ^ 5 := by
  have := Subgroup.card_le_of_le X.Zy_le_A
  rwa [A_card X.L.f X.L.E X.hWc X.hz X.hW5] at this

theorem card_Zy_cases : Nat.card X.Zy = 3 ∨ Nat.card X.Zy = 3 ^ 4 := by
  have h := (lattice_orders X (N := X.Zy) inf_le_left (fun c hc n hn => X.conj_Zy hc hn)).1 X.s₂_mem_Zy
  have hle := X.card_Zy_le
  rcases h with h | h | h
  · left; exact h
  · right; exact h
  · exfalso; rw [h] at hle; norm_num at hle

end Ctx9

end CFSG.GH74.Uniqueness.SU.SU13
