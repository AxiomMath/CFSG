module

public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.GroupTheory

open Subgroup

theorem exists_involution_commute_of_isPGroup_le_normalizer {G : Type*} [Group G] [Finite G]
    {A P : Subgroup G} (hP : IsPGroup 2 P) (hPA : P ≤ normalizer (A : Set G))
    (hA : Even (Nat.card A)) : ∃ a ∈ A, orderOf a = 2 ∧ ∀ p ∈ P, p * a = a * p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : MulAction P A :=
    { smul := fun p a => ⟨p * a * p⁻¹, (mem_normalizer_iff.mp (hPA p.2) a).mp a.2⟩
      one_smul := fun a => Subtype.ext (show (1 : G) * a * (1 : G)⁻¹ = a by group)
      mul_smul := fun p q a => Subtype.ext (show (p * q : G) * a * (p * q : G)⁻¹ =
        p * (q * a * (q : G)⁻¹) * (p : G)⁻¹ by group) }
  have hsmul : ∀ (p : P) (a : A), ((p • a : A) : G) = p * a * p⁻¹ := fun _ _ => rfl
  let C := A ⊓ centralizer (P : Set G)
  let e : MulAction.fixedPoints P A ≃ C :=
    { toFun := fun a => ⟨a.1, a.1.2, mem_centralizer_iff.mpr fun p hp => by
        have h : p * (a.1 : G) * p⁻¹ = a.1 := congrArg Subtype.val (a.2 ⟨p, hp⟩)
        calc p * (a.1 : G) = p * a.1 * p⁻¹ * p := by group
          _ = a.1 * p := by rw [h]⟩
      invFun := fun c => ⟨⟨c, c.2.1⟩, fun p => Subtype.ext (by
        rw [hsmul]
        change (p : G) * c * (p : G)⁻¹ = c
        rw [mem_centralizer_iff.mp c.2.2 p p.2, mul_inv_cancel_right])⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hmod := hP.card_modEq_card_fixedPoints A
  rw [Nat.card_congr e] at hmod
  have h2 : 2 ∣ Nat.card C := (hmod.dvd_iff dvd_rfl).mp (even_iff_two_dvd.mp hA)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 h2
  exact ⟨c, c.2.1, by rw [Subgroup.orderOf_coe, hc], fun p hp => mem_centralizer_iff.mp c.2.2 p hp⟩

theorem eq_top_of_isPerfect_of_quotient_commute {X : Type*} [Group X] [Group.IsPerfect X]
    (N : Subgroup X) [N.Normal] (hcomm : ∀ a b : X ⧸ N, a * b = b * a) : N = ⊤ := by
  have := Subgroup.Normal.quotient_commutative_iff_commutator_le.mp ⟨⟨hcomm⟩⟩
  rwa [Group.IsPerfect.commutator_eq_top, top_le_iff] at this

theorem four_le_index_center_subgroupOf_sylow_two {B : Type*} [Group B] [Finite B]
    [Group.IsPerfect B] (R : Sylow 2 B) (hR : (R : Subgroup B) ≠ ⊥) :
    4 ≤ ((center B).subgroupOf (R : Subgroup B)).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := (center B).subgroupOf (R : Subgroup B) with hIdef
  obtain ⟨k, hk⟩ := R.isPGroup'.index I
  have hnot : ¬ (R : Subgroup B) ≤ center B := by
    intro hRZ
    have hP : normalizer ((R : Subgroup B) : Set B) ≤ centralizer ((R : Subgroup B) : Set B) :=
      fun x _ => mem_centralizer_iff.mpr fun r hr => (mem_center_iff.mp (hRZ hr) x).symm
    obtain ⟨K, hKn, -, -, -, -, -, -, hinf, -, hcomm⟩ := burnside_normal_complement R hP
    rw [eq_top_of_isPerfect_of_quotient_commute K hcomm, top_inf_eq] at hinf
    exact hR hinf
  have hI1 : I.index ≠ 1 := fun h =>
    hnot fun r hr => (show (⟨r, hr⟩ : (R : Subgroup B)) ∈ I from
      (Subgroup.index_eq_one.mp h) ▸ Subgroup.mem_top _)
  set π := QuotientGroup.mk' (center B)
  set S : Sylow 2 (B ⧸ center B) := R.mapSurjective (QuotientGroup.mk'_surjective (center B))
  have hker : (π.comp (R : Subgroup B).subtype).ker = I := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  have hrange : (π.comp (R : Subgroup B).subtype).range = (S : Subgroup (B ⧸ center B)) := by
    rw [Sylow.coe_mapSurjective, MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardS : Nat.card (S : Subgroup (B ⧸ center B)) = I.index := by
    rw [← hrange, ← Subgroup.index_ker, hker]
  refine Nat.le_of_not_lt fun hlt => ?_
  have hI2 : I.index = 2 := by
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hI1 (by rw [hk, pow_zero])
    have hk2 : k < 2 := by
      by_contra h2
      have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.mp h2)
      rw [← hk] at this
      omega
    rw [hk, show k = 1 by omega, pow_one]
  have hS2 : Nat.card (S : Subgroup (B ⧸ center B)) = 2 := hcardS.trans hI2
  have hScyc : IsCyclic S := isCyclic_of_prime_card (p := 2) hS2
  obtain ⟨N, hN, hNS⟩ := CFSG.exists_normal_isComplement'_of_isCyclic_sylow_two S hScyc
  have hNidx : N.index = 2 := hNS.symm.index_eq_card.trans hS2
  have hQ2 : Nat.card ((B ⧸ center B) ⧸ N) = 2 := (Subgroup.index_eq_card N).symm.trans hNidx
  have hQcyc : IsCyclic ((B ⧸ center B) ⧸ N) := isCyclic_of_prime_card (p := 2) hQ2
  have hNtop := eq_top_of_isPerfect_of_quotient_commute N fun a b => Std.Commutative.comm a b
  rw [hNtop, Subgroup.index_top] at hNidx
  exact absurd hNidx (by norm_num)

end CFSG.GroupTheory
