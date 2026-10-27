module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPTwoThree
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTypes

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv Subgroup

namespace JankoRegular

open Janko JankoPTwoThree

theorem nine_add_eight_mul_eq {B : Subgroup (Perm (Fin 9))} (hB : Nat.card B = 9) {f : ℕ}
    (hf : ∀ g ∈ B, g ≠ 1 → (Finset.univ.filter fun i => g i = i).card = f) :
    9 + 8 * f = 9 * Nat.card (Quotient (MulAction.orbitRel B (Fin 9))) := by
  classical
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group B (Fin 9)
  rw [Fintype.card_eq_nat_card (α := Quotient _), Fintype.card_eq_nat_card (α := B), hB] at hburn
  have hfix : ∀ g : B, Fintype.card (MulAction.fixedBy (Fin 9) g) =
      (Finset.univ.filter fun i => (g : Perm (Fin 9)) i = i).card := by
    intro g
    rw [Fintype.card_subtype]
    rfl
  have hrest : ∑ g ∈ ({1}ᶜ : Finset B),
      (Finset.univ.filter fun i => (g : Perm (Fin 9)) i = i).card = 8 * f := by
    rw [Finset.sum_const_nat (m := f) (fun (g : B) hg => hf (g : Perm (Fin 9)) g.2
      (fun h => (Finset.mem_compl.mp hg) (Finset.mem_singleton.mpr (Subtype.ext h)))),
      Finset.card_compl, Finset.card_singleton, Fintype.card_eq_nat_card, hB]
  have h1 : (Finset.univ.filter fun i => ((1 : B) : Perm (Fin 9)) i = i).card = 9 := by
    simp
  simp only [hfix] at hburn
  rw [Fintype.sum_eq_add_sum_compl 1, hrest, h1] at hburn
  omega

theorem card_filter_apply_eq (g : Perm (Fin 9)) :
    (Finset.univ.filter fun i => g i = i).card = 9 - g.support.card := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 9))) (fun i => g i = i)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have hs : (Finset.univ.filter fun i => ¬ g i = i) = g.support := by
    ext i
    simp [Perm.mem_support]
  rw [hs] at h
  omega

theorem card_support_of_pow_three {g : Perm (Fin 9)} (h3 : g ^ 3 = 1) (h1 : g ≠ 1) :
    g.support.card = 3 ∨ g.support.card = 6 ∨ g.support.card = 9 := by
  rcases cycleType_of_pow_three_eq_one h3 h1 with h | h | h <;> rw [← Perm.sum_cycleType, h]
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem exists_ne_one_of_card_eq {X : Type*} [Group X] {B : Subgroup X} (hB : Nat.card B = 9) :
    ∃ g ∈ B, g ≠ 1 := by
  obtain ⟨⟨g, hg⟩, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := B)).mp fun h => by
    rw [h, card_bot] at hB
    norm_num at hB
  exact ⟨g, hg, fun h => hg1 (Subtype.ext h)⟩

theorem card_support_eq_nine {B : Subgroup (Perm (Fin 9))} (hB : Nat.card B = 9)
    (h3 : ∀ g ∈ B, g ^ 3 = 1) {m : ℕ} (hm : ∀ g ∈ B, g ≠ 1 → g.support.card = m) : m = 9 := by
  obtain ⟨g, hg, hg1⟩ := exists_ne_one_of_card_eq hB
  have hm' := card_support_of_pow_three (h3 g hg) hg1
  rw [hm g hg hg1] at hm'
  have := nine_add_eight_mul_eq hB (f := 9 - m) fun g hg hg1 => by
    rw [card_filter_apply_eq, hm g hg hg1]
  rcases hm' with rfl | rfl | rfl <;> omega

theorem exists_ne_card_support_nine {B : Subgroup (Perm (Fin 9))} (hB : Nat.card B = 9)
    (h0 : ∀ g ∈ B, ((g 0 : Fin 9) : ℕ) < 3) : ∃ g ∈ B, g ≠ 1 ∧ g.support.card ≠ 9 := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have h1 := nine_add_eight_mul_eq hB (f := 0) fun g hg hg1 => by
    rw [card_filter_apply_eq, h g hg hg1]
  have hne : (Quotient.mk _ (3 : Fin 9) : Quotient (MulAction.orbitRel B (Fin 9))) ≠
      Quotient.mk _ 0 := by
    intro heq
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp (Quotient.exact heq)
    have hg' : (g : Perm (Fin 9)) 0 = 3 := hg
    have := h0 g g.2
    rw [hg'] at this
    exact absurd this (by decide)
  have h2 : 1 < Nat.card (Quotient (MulAction.orbitRel B (Fin 9))) :=
    Finite.one_lt_card_iff_nontrivial.mpr (nontrivial_of_ne _ _ hne)
  omega

private theorem eword_apply_zero_lt : ∀ p : Fin 3 × Fin 3 × Fin 3,
    ((((eword p : alternatingGroup (Fin 9)) : Perm (Fin 9)) 0 : Fin 9) : ℕ) < 3 := by
  decide +kernel

theorem apply_zero_lt_of_mem_Ebar {g : alternatingGroup (Fin 9)} (hg : g ∈ Ebar) :
    (((g : Perm (Fin 9)) 0 : Fin 9) : ℕ) < 3 := by
  obtain ⟨p, rfl⟩ := exists_eword_eq hg
  exact eword_apply_zero_lt p

private theorem card_eword_support_eq_nine :
    Fintype.card {p : Fin 3 × Fin 3 × Fin 3 //
      ((eword p : alternatingGroup (Fin 9)) : Perm (Fin 9)).support.card = 9} = 8 := by
  decide +kernel

variable {J : Type*} [Group J] (hJ : IsTwoANine J) (e : J ⧸ center J ≃* alternatingGroup (Fin 9))
include hJ

theorem pow_three_of_mem_liftOddSubgroup_Ebar {x : J} (hx : x ∈ liftOddSubgroup e Ebar) :
    x ^ 3 = 1 :=
  hJ.eq_of_proj_eq_of_odd e ((hJ.odd_card_liftOddSubgroup e odd_card_Ebar).of_dvd_nat
    ((liftOddSubgroup e Ebar).orderOf_dvd_natCard (pow_mem hx 3)))
    (by rw [orderOf_one]; exact odd_one) (by
      rw [map_pow, map_one,
        pow_three_of_mem_Ebar ((hJ.mem_liftOddSubgroup_iff e odd_card_Ebar).mp hx).1])

theorem card_centralizer_eq_iff {x : J} (hx3 : x ^ 3 = 1) :
    Nat.card (centralizer ({x} : Set J)) = 162 ↔
      ((proj e x : alternatingGroup (Fin 9)) : Perm (Fin 9)).support.card = 9 := by
  have h3' : ((proj e x : alternatingGroup (Fin 9)) : Perm (Fin 9)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hx3, map_one, OneMemClass.coe_one]
  constructor
  · intro hc
    have hx1 : x ≠ 1 := by
      rintro rfl
      rw [show centralizer ({1} : Set J) = ⊤ from
        eq_top_iff.mpr fun g _ => mem_centralizer_singleton_iff.mpr (by rw [mul_one, one_mul]),
        card_top, hJ.card_eq] at hc
      norm_num at hc
    have hp1 : ((proj e x : alternatingGroup (Fin 9)) : Perm (Fin 9)) ≠ 1 := fun h =>
      (hJ.orderOf_eq_three_of_pow_three e hx3 hx1).2.2 (Subtype.ext h)
    rcases cycleType_of_pow_three_eq_one h3' hp1 with h | h | h
    · rw [hJ.card_centralizer_of_cycleType_eq_three e hx3 h] at hc
      norm_num at hc
    · rw [hJ.card_centralizer_of_cycleType_eq_three_three e hx3 h] at hc
      norm_num at hc
    · rw [← Perm.sum_cycleType, h]
      rfl
  · intro hs
    exact hJ.card_centralizer_of_cycleType_eq_three_three_three e hx3
      ((cycleType_eq_replicate_iff_of_pow_three_eq_one h3' 3).mpr hs)

end JankoRegular

namespace Janko

open JankoPTwoThree JankoRegular

variable {G : Type*} [Group G] {z : G} (hH : IsTwoANine (centralizer ({z} : Set G)))
include hH

omit hH in
private theorem card_subgroupOf' {B : Subgroup G} (hB : B ≤ centralizer ({z} : Set G)) :
    Nat.card (B.subgroupOf (centralizer ({z} : Set G))) = Nat.card B :=
  Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv

private theorem card_image_eq
    (e : centralizer ({z} : Set G) ⧸ center (centralizer ({z} : Set G)) ≃*
      alternatingGroup (Fin 9))
    {B : Subgroup G} (hB : B ≤ centralizer ({z} : Set G)) (h9 : Nat.card B = 9) :
    Nat.card (((B.subgroupOf (centralizer ({z} : Set G))).map (proj e)).map
      (alternatingGroup (Fin 9)).subtype) = 9 := by
  have hB' := card_subgroupOf' hB
  rw [h9] at hB'
  rw [card_map_of_injective (alternatingGroup (Fin 9)).subtype_injective,
    hH.card_map_proj_of_odd e (by rw [hB']; exact ⟨4, rfl⟩), hB']

theorem type_s₃_of_conj : ∀ B : Subgroup G, B ≤ centralizer ({z} : Set G) → Nat.card B = 9 →
    (∀ x ∈ B, ∀ y ∈ B, x ≠ 1 → y ≠ 1 → ∃ h ∈ centralizer ({z} : Set G), h * x * h⁻¹ = y) →
    ∀ x ∈ B, x ≠ 1 →
      Nat.card (centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 162 := by
  intro B hB h9 hconj x hx hx1
  obtain ⟨e⟩ := hH.nonempty_mulEquiv
  have := hH.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB' := card_subgroupOf' hB
  rw [h9] at hB'
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card'
    (G := B.subgroupOf (centralizer ({z} : Set G))) 3 (by rw [hB']; norm_num)
  have hx₀B : ((x₀ : centralizer ({z} : Set G)) : G) ∈ B := mem_subgroupOf.mp x₀.2
  have hox₀ : orderOf ((x₀ : centralizer ({z} : Set G)) : G) = 3 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx₀]
  have hx₀3 : ((x₀ : centralizer ({z} : Set G)) : G) ^ 3 = 1 := by
    rw [← hox₀]
    exact pow_orderOf_eq_one _
  have hx₀1 : ((x₀ : centralizer ({z} : Set G)) : G) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hox₀
    exact absurd hox₀ (by norm_num)
  have hpow : ∀ y ∈ B, y ^ 3 = 1 := by
    intro y hy
    by_cases hy1 : y = 1
    · rw [hy1, one_pow]
    obtain ⟨h, -, hh⟩ := hconj _ hx₀B y hy hx₀1 hy1
    rw [← hh, conj_pow, hx₀3, mul_one, mul_inv_cancel]
  set x' : centralizer ({z} : Set G) := ⟨x, hB hx⟩
  set m := ((proj e x' : alternatingGroup (Fin 9)) : Perm (Fin 9)).support.card
  have hm : ∀ g ∈ ((B.subgroupOf (centralizer ({z} : Set G))).map (proj e)).map
      (alternatingGroup (Fin 9)).subtype, g ≠ 1 → g.support.card = m := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩ hg1
    have hy1 : (y : G) ≠ 1 := fun h => hg1 (by
      rw [show y = 1 from Subtype.ext h, map_one, map_one])
    obtain ⟨h, hh, hhy⟩ := hconj x hx (y : G) (mem_subgroupOf.mp hy) hx1 hy1
    have hy' : y = ⟨h, hh⟩ * x' * ⟨h, hh⟩⁻¹ := Subtype.ext hhy.symm
    simp only [coe_subtype, hy', map_mul, map_inv]
    exact Perm.card_support_conj
  have h3 : ∀ g ∈ ((B.subgroupOf (centralizer ({z} : Set G))).map (proj e)).map
      (alternatingGroup (Fin 9)).subtype, g ^ 3 = 1 := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [coe_subtype, ← Subgroup.coe_pow, ← map_pow,
      show y ^ 3 = 1 from Subtype.ext (hpow _ (mem_subgroupOf.mp hy)), map_one,
      OneMemClass.coe_one]
  have h9' := card_support_eq_nine (card_image_eq hH e hB h9) h3 hm
  rw [show x = (x' : G) from rfl, card_centralizer_inf_eq]
  exact (card_centralizer_eq_iff hH e (Subtype.ext (hpow x hx))).mpr h9'

variable (e : centralizer ({z} : Set G) ⧸ center (centralizer ({z} : Set G)) ≃*
  alternatingGroup (Fin 9))

theorem exists_ne_type_s₃ : ∀ B : Subgroup G, B ≤ E e → Nat.card B = 9 →
    ∃ x ∈ B, x ≠ 1 ∧
      Nat.card (centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) ≠ 162 := by
  intro B hBE h9
  have hB : B ≤ centralizer ({z} : Set G) := hBE.trans (E_le e)
  have hmemE : ∀ y ∈ B.subgroupOf (centralizer ({z} : Set G)), y ∈ liftOddSubgroup e Ebar :=
    fun y hy => (mem_map_iff_mem (centralizer ({z} : Set G)).subtype_injective).mp
      (hBE (mem_subgroupOf.mp hy))
  have h0 : ∀ g ∈ ((B.subgroupOf (centralizer ({z} : Set G))).map (proj e)).map
      (alternatingGroup (Fin 9)).subtype, ((g 0 : Fin 9) : ℕ) < 3 := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact apply_zero_lt_of_mem_Ebar
      ((hH.mem_liftOddSubgroup_iff e odd_card_Ebar).mp (hmemE y hy)).1
  obtain ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, hg1, hg9⟩ :=
    exists_ne_card_support_nine (card_image_eq hH e hB h9) h0
  refine ⟨(y : G), mem_subgroupOf.mp hy, fun h => hg1 ?_, fun hc => hg9 ?_⟩
  · rw [show y = 1 from Subtype.ext h, map_one, map_one]
  · rw [card_centralizer_inf_eq] at hc
    exact (card_centralizer_eq_iff hH e
      (pow_three_of_mem_liftOddSubgroup_Ebar hH e (hmemE y hy))).mp hc

theorem card_type_s₃_E : Nat.card {x : G // x ∈ E e ∧
    Nat.card (centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 162} = 8 := by
  have hodd := odd_card_Ebar
  have hwo : ∀ p, Odd (orderOf (eword p)) := fun p =>
    hodd.of_dvd_nat (Ebar.orderOf_dvd_natCard (eword_mem p))
  have hmem : ∀ p, liftOdd e (eword p) ∈ liftOddSubgroup e Ebar := fun p =>
    hH.liftOdd_mem_liftOddSubgroup e hodd (eword_mem p)
  let f : {p : Fin 3 × Fin 3 × Fin 3 //
      ((eword p : alternatingGroup (Fin 9)) : Perm (Fin 9)).support.card = 9} →
      {x : G // x ∈ E e ∧ Nat.card (centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) :
        Subgroup G) = 162} := fun p =>
    ⟨((liftOdd e (eword p.1) : centralizer ({z} : Set G)) : G), ⟨_, hmem p.1, rfl⟩, by
      rw [card_centralizer_inf_eq]
      refine (card_centralizer_eq_iff hH e
        (pow_three_of_mem_liftOddSubgroup_Ebar hH e (hmem p.1))).mpr ?_
      rw [hH.proj_liftOdd e (hwo p.1)]
      exact p.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q h => ?_, ?_⟩
    · have h1 := congrArg Subtype.val h
      change ((liftOdd e (eword p.1) : centralizer ({z} : Set G)) : G) =
        ((liftOdd e (eword q.1) : centralizer ({z} : Set G)) : G) at h1
      have h' := congrArg (proj e) (Subtype.ext h1 : liftOdd e (eword p.1) = liftOdd e (eword q.1))
      rw [hH.proj_liftOdd e (hwo p.1), hH.proj_liftOdd e (hwo q.1)] at h'
      exact Subtype.ext (eword_injective h')
    · rintro ⟨_, ⟨x', hx', rfl⟩, hxc⟩
      obtain ⟨p, hp⟩ := exists_eword_eq ((hH.mem_liftOddSubgroup_iff e hodd).mp hx').1
      simp only [coe_subtype] at hxc
      rw [card_centralizer_inf_eq] at hxc
      have hs := (card_centralizer_eq_iff hH e
        (pow_three_of_mem_liftOddSubgroup_Ebar hH e hx')).mp hxc
      refine ⟨⟨p, by rw [hp]; exact hs⟩, Subtype.ext ?_⟩
      show ((liftOdd e (eword p) : centralizer ({z} : Set G)) : G) = x'
      rw [hp, ← hH.eq_liftOdd e ((hH.mem_liftOddSubgroup_iff e hodd).mp hx').2]
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card,
    card_eword_support_eq_nine]

end Janko

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
