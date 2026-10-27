module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec7End_card_autIn_mul [Finite G] {H Y : Subgroup G} (hH : H ≤ normalizer (Y : Set G)) :
    Nat.card (autIn H Y) * Nat.card ↥(H ⊓ centralizer (Y : Set G)) = Nat.card H := by
  classical
  let f : ↥(normalizer (Y : Set G)) →* MulAut ↥Y := Y.normalizerMonoidHom
  have hrange : (f.comp (Subgroup.inclusion hH)).range = autIn H Y := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range hH]
    unfold autIn
    rfl
  have hker : (f.comp (Subgroup.inclusion hH)).ker =
      (H ⊓ centralizer (Y : Set G)).subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    show f (Subgroup.inclusion hH x) = 1 ↔
      (x : G) ∈ H ∧ (x : G) ∈ centralizer (Y : Set G)
    have hfker : f.ker =
        (centralizer (Y : Set G)).subgroupOf (normalizer (Y : Set G)) :=
      Subgroup.normalizerMonoidHom_ker Y
    rw [← MonoidHom.mem_ker, hfker, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have key := Subgroup.card_ker_mul_card_range (f.comp (Subgroup.inclusion hH))
  rw [hker, hrange] at key
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (inf_le_left : H ⊓ centralizer (Y : Set G) ≤ H)).toEquiv] at key
  rw [mul_comm] at key
  exact key

theorem sec7End_autIn_comm {H Y : Subgroup G} (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) :
    ∀ a ∈ autIn H Y, ∀ b ∈ autIn H Y, a * b = b * a := by
  intro a ha b hb
  unfold autIn at ha hb
  rw [Subgroup.mem_map] at ha hb
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  have hxy : x * y = y * x := by
    apply Subtype.ext
    simpa using hH (x : G) (Subgroup.mem_subgroupOf.mp hx) (y : G)
      (Subgroup.mem_subgroupOf.mp hy)
  rw [← map_mul, ← map_mul, hxy]

theorem sec7End_card_le [Finite G] {H Q : Subgroup G} (hHQ : H ≤ Q) (hQ : IsCyclic ↥Q) {n : ℕ}
    (hn : 0 < n) (hexp : ∀ x ∈ H, x ^ n = 1) : Nat.card H ≤ n := by
  classical
  let C := ↥(H.subgroupOf Q)
  haveI : IsCyclic ↥Q := hQ
  haveI : IsCyclic C := Subgroup.isCyclic (H.subgroupOf Q)
  haveI : Fintype C := Fintype.ofFinite C
  have hcard : Nat.card H = Nat.card C :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHQ).toEquiv).symm
  rw [hcard]
  have hsub : (Finset.univ : Finset C) ⊆
      Finset.univ.filter (fun a : C => a ^ n = 1) := by
    intro a _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ a, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hexp (a : G) (Subgroup.mem_subgroupOf.mp a.2)
  have hle := IsCyclic.card_pow_eq_one_le (α := C) hn
  calc Nat.card C = Fintype.card C := Nat.card_eq_fintype_card
    _ = (Finset.univ : Finset C).card := Finset.card_univ.symm
    _ ≤ (Finset.univ.filter (fun a : C => a ^ n = 1)).card := Finset.card_le_card hsub
    _ ≤ n := hle

theorem sec7End_card_le_mul [Finite G] {E U Y : Subgroup G} (hUE : U ≤ E)
    (hEN : E ≤ normalizer (Y : Set G)) (hcyc : IsCyclic ↥(E ⊓ centralizer (Y : Set G))) {n : ℕ}
    (hn : 0 < n) (hexp : ∀ x ∈ U, x ^ n = 1) : Nat.card U ≤ n * Nat.card (autIn U Y) := by
  have hUN : U ≤ normalizer (Y : Set G) := hUE.trans hEN
  have h1 := sec7End_card_autIn_mul (H := U) (Y := Y) hUN
  have h3 : Nat.card ↥(U ⊓ centralizer (Y : Set G)) ≤ n :=
    sec7End_card_le (H := U ⊓ centralizer (Y : Set G))
      (Q := E ⊓ centralizer (Y : Set G)) (n := n)
      (le_inf (inf_le_left.trans hUE) inf_le_right) hcyc hn
      (fun x hx => hexp x (Subgroup.mem_inf.mp hx).1)
  calc Nat.card U = Nat.card (autIn U Y) * Nat.card ↥(U ⊓ centralizer (Y : Set G)) :=
        h1.symm
    _ ≤ Nat.card (autIn U Y) * n := mul_le_mul_right h3 _
    _ = n * Nat.card (autIn U Y) := by rw [mul_comm]

end CFSG.OddStandard.SmallF3.Omega
