module

public import Mathlib.RingTheory.Norm.Defs
import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LinearAlgebra.RootGroupSL

open Module

theorem exists_norm_one_generator {k E : Type} [Field k] [Field E] [Algebra k E] [Finite k]
    [Finite E] (hd : 2 ≤ Module.finrank k E) :
    ∃ ν : Eˣ, Algebra.norm k (ν : E) = 1 ∧ ν ≠ 1 ∧
      ∀ L : Subfield E, (ν : E) ∈ L → L = ⊤ := by
  classical
  let Q := Nat.card k
  let d := Module.finrank k E
  let φ : Eˣ →* kˣ := Units.map (Algebra.norm k)
  let N₁ : Subgroup Eˣ := φ.ker
  haveI : Finite N₁ := inferInstance
  haveI : IsCyclic N₁ := isCyclic_subgroup_units (R := E) N₁
  obtain ⟨ν₀, hgen⟩ := IsCyclic.exists_generator (α := N₁)
  let ν : Eˣ := (ν₀ : Eˣ)
  have hQ2 : 2 ≤ Q := by
    have := Finite.one_lt_card (α := k)
    dsimp [Q]; omega
  have hd2 : 2 ≤ d := hd
  have hcardN : Nat.card N₁ * (Q - 1) = Q ^ d - 1 := by
    have h := Subgroup.card_ker_mul_card_of_surjective
      (f := φ) (FiniteField.unitsMap_norm_surjective k E)
    have hk : Nat.card kˣ = Q - 1 := Nat.card_units (α := k)
    have hE : Nat.card E = Q ^ d := by
      simpa [Q, d] using Module.natCard_eq_pow_finrank (K := k) (V := E)
    have hE' : Nat.card Eˣ = Q ^ d - 1 := by
      rw [Nat.card_units (α := E), hE]
    rw [show φ.ker = N₁ from rfl, hk, hE'] at h
    exact h
  have hN : Nat.card N₁ = (Q ^ d - 1) / (Q - 1) := by
    refine Nat.eq_div_of_mul_eq_right (by omega) ?_
    rw [Nat.mul_comm]
    exact hcardN
  have hNgt : Q ^ (d - 1) < Nat.card N₁ := by
    rw [hN, ← Nat.geomSum_eq hQ2 d]
    have hsplit : (∑ k ∈ Finset.range d, Q ^ k)
        = (∑ k ∈ Finset.range (d - 1), Q ^ k) + Q ^ (d - 1) := by
      conv_lhs => rw [show d = d - 1 + 1 by omega]
      rw [Finset.sum_range_succ]
    rw [hsplit]
    have hTpos : 0 < ∑ k ∈ Finset.range (d - 1), Q ^ k := by
      have hmem : 0 ∈ Finset.range (d - 1) := Finset.mem_range.mpr (by omega)
      have hle : (1 : ℕ) ≤ ∑ k ∈ Finset.range (d - 1), Q ^ k := by
        simpa using Finset.single_le_sum (s := Finset.range (d - 1))
          (f := fun k => Q ^ k) (fun k _ => Nat.zero_le _) hmem
      omega
    omega
  have hnorm : Algebra.norm k (ν : E) = 1 := by
    have hmem : φ (ν : Eˣ) = 1 := MonoidHom.mem_ker.mp ν₀.2
    have h := congrArg (fun u : kˣ => (u : k)) hmem
    simpa [φ, ν] using h
  have horder : orderOf ν = Nat.card N₁ := by
    show orderOf ((ν₀ : N₁) : Eˣ) = Nat.card N₁
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_card_of_forall_mem_zpowers hgen
  have hν1 : ν ≠ 1 := by
    intro h1
    have ho : orderOf ν = 1 := by rw [h1, orderOf_one]
    have h1' : Nat.card N₁ = 1 := by rw [← horder, ho]
    have hbig : 2 ≤ Q ^ (d - 1) := by
      calc 2 ≤ Q := hQ2
        _ = Q ^ 1 := (pow_one Q).symm
        _ ≤ Q ^ (d - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  refine ⟨ν, hnorm, hν1, ?_⟩
  intro L hνL
  by_contra hLne
  have hf2 : 2 ≤ Module.finrank L E := by
    obtain ⟨x, hxL⟩ : ∃ x : E, x ∉ L := by
      by_contra hcon
      apply hLne
      ext y
      simp only [Subfield.mem_top, iff_true]
      by_contra hy
      exact hcon ⟨y, hy⟩
    have hlind : LinearIndependent L ![(1 : E), x] :=
      (LinearIndependent.pair_iff' (x := (1 : E)) (y := x) one_ne_zero).mpr (by
        intro a ha
        apply hxL
        have hsmul : a • (1 : E) = (a : E) := by
          rw [Algebra.smul_def, mul_one]
          rfl
        rw [← ha, hsmul]
        exact a.2)
    simpa using hlind.fintype_card_le_finrank
  have hνLne : (⟨(ν : E), hνL⟩ : L) ≠ 0 := by
    intro h
    exact ν.ne_zero (Subtype.ext_iff.mp h)
  let νL : Lˣ := Units.mk0 ⟨(ν : E), hνL⟩ hνLne
  have horderL : orderOf νL = orderOf ν := by
    have h2 : orderOf νL = orderOf (νL : L) := (orderOf_units).symm
    have h3 : orderOf (ν : E) = orderOf (νL : L) := by
      have hinj : Function.Injective (Subfield.subtype L : L →* E) :=
        fun a b h => Subtype.ext h
      have h := orderOf_injective (Subfield.subtype L : L →* E) hinj (νL : L)
      have hval : ((Subfield.subtype L : L →* E)) (νL : L) = (ν : E) := rfl
      rw [hval] at h
      exact h
    have h4 : orderOf (ν : E) = orderOf ν := orderOf_units
    exact h2.trans (h3.symm.trans h4)
  have hdvdL : Nat.card N₁ ∣ Nat.card L - 1 := by
    have h := orderOf_dvd_natCard νL
    rw [Nat.card_units (α := L)] at h
    rw [horderL, horder] at h
    exact h
  have hNlt : Nat.card N₁ < Nat.card L := by
    have hpos : 0 < Nat.card L - 1 := by
      have := Finite.one_lt_card (α := L)
      omega
    have hle : Nat.card N₁ ≤ Nat.card L - 1 := Nat.le_of_dvd hpos hdvdL
    have := Finite.one_lt_card (α := L)
    omega
  have hEcard : Nat.card E = Q ^ d := by
    simpa [Q, d] using Module.natCard_eq_pow_finrank (K := k) (V := E)
  have hcardL : Nat.card E = Nat.card L ^ Module.finrank L E :=
    Module.natCard_eq_pow_finrank (K := L) (V := E)
  have hL2 : Nat.card L ^ 2 ≤ Q ^ d := by
    have hle : Nat.card L ^ 2 ≤ Nat.card L ^ Module.finrank L E :=
      Nat.pow_le_pow_right (Nat.card_pos (α := L)) hf2
    rw [← hcardL, hEcard] at hle
    exact hle
  have hsq_gt : Q ^ d < Nat.card N₁ ^ 2 := by
    have h2d : d ≤ 2 * d - 2 := by omega
    have h1 : Q ^ d ≤ (Q ^ (d - 1)) ^ 2 := by
      calc Q ^ d ≤ Q ^ (2 * d - 2) := Nat.pow_le_pow_right (by omega) h2d
        _ = (Q ^ (d - 1)) ^ 2 := by
          rw [← pow_mul]
          congr 1
          omega
    exact lt_of_le_of_lt h1 (by
      rw [pow_two, pow_two]
      exact Nat.mul_self_lt_mul_self hNgt)
  have hsq_lt : Nat.card N₁ ^ 2 < Nat.card L ^ 2 := by
    rw [pow_two, pow_two]
    exact Nat.mul_self_lt_mul_self hNlt
  exact absurd (lt_of_le_of_lt hL2 (lt_trans hsq_gt hsq_lt)) (lt_irrefl _)

end CFSG.LinearAlgebra.RootGroupSL
