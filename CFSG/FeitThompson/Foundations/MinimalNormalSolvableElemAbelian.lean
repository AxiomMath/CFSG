module

public import CFSG.FeitThompson.Foundations.SolvablePerfectTrivial
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem characteristic_ker_powMonoidHom (A : Type*) [CommGroup A] (n : ℕ) :
    ((powMonoidHom n : A →* A).ker).Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ x hx
  simp only [MonoidHom.mem_ker, powMonoidHom_apply] at hx
  simp [Subgroup.mem_comap, MonoidHom.mem_ker, powMonoidHom_apply, ← map_pow, hx]

theorem exists_linearEquiv_fin_of_finite (p : ℕ) [Fact p.Prime] (V : Type*) [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] [Nontrivial V] :
    ∃ d : ℕ, 1 ≤ d ∧ Nonempty (V ≃ₗ[ZMod p] (Fin d → ZMod p)) := by
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  exact ⟨Module.finrank (ZMod p) V, Module.finrank_pos, ⟨(Module.finBasis (ZMod p) V).equivFun⟩⟩

theorem exists_mulEquiv_of_forall_pow_eq_one {A : Type*} [CommGroup A] [Finite A] [Nontrivial A]
    {p : ℕ} (hp : p.Prime) (hexp : ∀ x : A, x ^ p = 1) :
    ∃ d : ℕ, 1 ≤ d ∧ Nonempty (A ≃* Multiplicative (Fin d → ZMod p)) := by
  have hfact : Fact p.Prime := ⟨hp⟩
  have hsm : ∀ x : Additive A, p • x = 0 := fun x => hexp (Additive.toMul x)
  let _inst : Module (ZMod p) (Additive A) := AddCommGroup.zmodModule hsm
  obtain ⟨d, hd, ⟨e⟩⟩ := exists_linearEquiv_fin_of_finite p (Additive A)
  exact ⟨d, hd, ⟨AddEquiv.toMultiplicativeRight e.toAddEquiv⟩⟩

variable {G : Type*} [Group G]

theorem eq_top_of_characteristic_of_forall_normal_lt_eq_bot {N : Subgroup G} [N.Normal]
    (hmin : ∀ K : Subgroup G, K.Normal → K < N → K = ⊥)
    (H : Subgroup ↥N) [H.Characteristic] (hH : H ≠ ⊥) : H = ⊤ := by
  rw [← Subgroup.map_subtype_inj, ← MonoidHom.range_eq_map, Subgroup.subtype_range]
  have hle : H.map N.subtype ≤ N := Subgroup.map_subtype_le H
  have hne : H.map N.subtype ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff]
    simpa [le_bot_iff] using hH
  rcases lt_or_eq_of_le hle with h | h
  · exact absurd (hmin _ inferInstance h) hne
  · exact h

theorem isMulCommutative_of_isSolvable_of_forall_normal_lt_eq_bot {N : Subgroup G} [N.Normal]
    [Group.IsSolvable ↥N] (hN : N ≠ ⊥)
    (hmin : ∀ K : Subgroup G, K.Normal → K < N → K = ⊥) : IsMulCommutative ↥N := by
  have hnt : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN
  rw [← commutator_eq_bot_iff]
  by_contra h
  have htop := eq_top_of_characteristic_of_forall_normal_lt_eq_bot hmin (_root_.commutator ↥N) h
  exact absurd (subsingleton_of_isSolvable_of_commutator_eq_top ↥N htop) (not_subsingleton ↥N)

theorem exists_prime_forall_pow_eq_one_of_isSolvable_of_forall_normal_lt_eq_bot [Finite G]
    {N : Subgroup G} [N.Normal] [Group.IsSolvable ↥N] (hN : N ≠ ⊥)
    (hmin : ∀ K : Subgroup G, K.Normal → K < N → K = ⊥) :
    ∃ p : ℕ, p.Prime ∧ ∀ x : ↥N, x ^ p = 1 := by
  have hnt : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN
  have hcomm : IsMulCommutative ↥N :=
    isMulCommutative_of_isSolvable_of_forall_normal_lt_eq_bot hN hmin
  let _inst : CommGroup ↥N := IsMulCommutative.instCommGroup
  obtain ⟨p, hp, hpd⟩ := (Nat.card ↥N).exists_prime_and_dvd (by
    have : 1 < Nat.card ↥N := Finite.one_lt_card
    omega)
  have hfact : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p hpd
  refine ⟨p, hp, ?_⟩
  have hker : ((powMonoidHom p : ↥N →* ↥N).ker) = ⊤ := by
    have := characteristic_ker_powMonoidHom ↥N p
    refine eq_top_of_characteristic_of_forall_normal_lt_eq_bot hmin _ ?_
    intro h
    have hxm : x ∈ (powMonoidHom p : ↥N →* ↥N).ker := by
      simp [MonoidHom.mem_ker, powMonoidHom_apply, ← hx, pow_orderOf_eq_one]
    rw [h, Subgroup.mem_bot] at hxm
    rw [hxm, orderOf_one] at hx
    exact hp.one_lt.ne hx
  intro y
  have hy : y ∈ (powMonoidHom p : ↥N →* ↥N).ker := hker ▸ Subgroup.mem_top y
  simpa [MonoidHom.mem_ker, powMonoidHom_apply] using hy

theorem exists_prime_nonempty_mulEquiv_of_isSolvable_of_forall_normal_lt_eq_bot [Finite G]
    {N : Subgroup G} [N.Normal] [Group.IsSolvable ↥N] (hN : N ≠ ⊥)
    (hmin : ∀ K : Subgroup G, K.Normal → K < N → K = ⊥) :
    ∃ p d : ℕ, p.Prime ∧ 1 ≤ d ∧ Nonempty (↥N ≃* Multiplicative (Fin d → ZMod p)) := by
  have hnt : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN
  have hcomm : IsMulCommutative ↥N :=
    isMulCommutative_of_isSolvable_of_forall_normal_lt_eq_bot hN hmin
  let _inst : CommGroup ↥N := IsMulCommutative.instCommGroup
  obtain ⟨p, hp, hexp⟩ :=
    exists_prime_forall_pow_eq_one_of_isSolvable_of_forall_normal_lt_eq_bot hN hmin
  obtain ⟨d, hd, he⟩ := exists_mulEquiv_of_forall_pow_eq_one hp hexp
  exact ⟨p, d, hp, hd, he⟩

theorem exists_prime_card_eq_pow_of_isSolvable_of_forall_normal_lt_eq_bot [Finite G]
    {N : Subgroup G} [N.Normal] [Group.IsSolvable ↥N] (hN : N ≠ ⊥)
    (hmin : ∀ K : Subgroup G, K.Normal → K < N → K = ⊥) :
    ∃ p d : ℕ, p.Prime ∧ 1 ≤ d ∧ Nat.card ↥N = p ^ d := by
  obtain ⟨p, d, hp, hd, ⟨e⟩⟩ :=
    exists_prime_nonempty_mulEquiv_of_isSolvable_of_forall_normal_lt_eq_bot hN hmin
  have hfact : Fact p.Prime := ⟨hp⟩
  refine ⟨p, d, hp, hd, ?_⟩
  rw [Nat.card_eq_of_bijective e e.bijective]
  simp [Nat.card_eq_fintype_card]

end CFSG.FeitThompson
