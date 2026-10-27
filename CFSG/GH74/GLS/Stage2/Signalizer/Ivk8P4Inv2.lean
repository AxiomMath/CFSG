module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup

section Coset

variable {K : Type} [Group K] [Finite K]

theorem exists_fixed_of_odd_coset_pgroup (N : Subgroup K) [N.Normal] (hodd : Odd (Nat.card N))
    (R : Subgroup K) (hR : IsPGroup 2 R) (h : K) (hh : ∀ t ∈ R, t * h * t⁻¹ * h⁻¹ ∈ N) :
    ∃ n ∈ N, ∀ t ∈ R, t * (h * n) * t⁻¹ = h * n := by
  classical
  let T : Type := {x : K // ∃ n ∈ N, x = h * n}
  have hmem : ∀ (t : K), t ∈ R → ∀ x : T, ∃ n ∈ N, t * x.1 * t⁻¹ = h * n := by
    intro t ht x
    obtain ⟨n, hn, hx⟩ := x.2
    refine ⟨h⁻¹ * (t * h * t⁻¹ * h⁻¹) * h * (t * n * t⁻¹), ?_, ?_⟩
    · refine N.mul_mem (by simpa using Subgroup.Normal.conj_mem inferInstance _ (hh t ht) h⁻¹) ?_
      simpa using Subgroup.Normal.conj_mem inferInstance n hn t
    · rw [hx]; group
  let _ : MulAction ↥R T :=
    { smul := fun t x => ⟨t.1 * x.1 * t.1⁻¹, hmem t.1 t.2 x⟩
      one_smul := fun x => Subtype.ext (by
        show (1 : K) * x.1 * (1 : K)⁻¹ = x.1
        group)
      mul_smul := fun s t x => Subtype.ext (by
        show (s.1 * t.1) * x.1 * (s.1 * t.1)⁻¹ = s.1 * (t.1 * x.1 * t.1⁻¹) * s.1⁻¹
        group) }
  have : Finite T := Subtype.finite
  have hcard : Nat.card T = Nat.card N := by
    refine Nat.card_congr
      { toFun := fun x => ⟨h⁻¹ * x.1, by
          obtain ⟨n, hn, hx⟩ := x.2
          rw [hx]
          simpa using hn⟩
        invFun := fun n => ⟨h * n.1, n.1, n.2, rfl⟩
        left_inv := fun x => by
          obtain ⟨x, n, hn, hx⟩ := x
          subst hx
          apply Subtype.ext
          simp
        right_inv := fun n => by
          apply Subtype.ext
          simp }
  have hmod := hR.card_modEq_card_fixedPoints T
  have hodd' : Nat.card T % 2 = 1 := by rw [hcard]; exact Nat.odd_iff.mp hodd
  have hfix : Nat.card (MulAction.fixedPoints ↥R T) ≠ 0 := by
    intro h0
    have := hmod
    rw [h0] at this
    have h1 : Nat.card T % 2 = 0 := by simpa [Nat.ModEq] using this
    omega
  have hne : Nonempty (MulAction.fixedPoints ↥R T) := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    exact hfix (by rw [Nat.card_of_isEmpty])
  obtain ⟨⟨x, hxfix⟩⟩ := hne
  obtain ⟨n, hn, hxn⟩ := x.2
  refine ⟨n, hn, fun t ht => ?_⟩
  have := congrArg Subtype.val ((MulAction.mem_fixedPoints).1 hxfix ⟨t, ht⟩)
  rw [← hxn]
  exact this

end Coset

section Quotient

variable {K : Type} [Group K] [Finite K]

theorem exists_centralizer_lift_of_odd_kernel (N : Subgroup K) [N.Normal]
    (hodd : Odd (Nat.card N)) (R : Subgroup K) (hR : IsPGroup 2 R) (y : K ⧸ N)
    (hy : ∀ t ∈ R, (t : K ⧸ N) * y = y * (t : K ⧸ N)) :
    ∃ x : K, (x : K ⧸ N) = y ∧ ∀ t ∈ R, t * x = x * t := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  have hh : ∀ t ∈ R, t * h * t⁻¹ * h⁻¹ ∈ N := by
    intro t ht
    have h1 : ((t * h * t⁻¹ * h⁻¹ : K) : K ⧸ N) = 1 := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hy t ht]
      group
    exact (QuotientGroup.eq_one_iff _).1 h1
  obtain ⟨n, hn, hfix⟩ := exists_fixed_of_odd_coset_pgroup N hodd R hR h hh
  refine ⟨h * n, ?_, fun t ht => ?_⟩
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).2 hn, mul_one]
  · have := hfix t ht
    calc t * (h * n) = t * (h * n) * t⁻¹ * t := by group
      _ = h * n * t := by rw [this]

theorem centralizer_map_mk_eq (N : Subgroup K) [N.Normal] (hodd : Odd (Nat.card N))
    (R : Subgroup K) (hR : IsPGroup 2 R) :
    centralizer ((R.map (QuotientGroup.mk' N) : Subgroup (K ⧸ N)) : Set (K ⧸ N)) =
      (centralizer (R : Set K)).map (QuotientGroup.mk' N) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, hxc⟩ := exists_centralizer_lift_of_odd_kernel N hodd R hR y (fun t ht => by
      exact Subgroup.mem_centralizer_iff.1 hy ((t : K) : K ⧸ N) ⟨t, ht, rfl⟩)
    exact ⟨x, Subgroup.mem_centralizer_iff.2 fun t ht => hxc t ht, hx⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 hx t ht
    show (t : K ⧸ N) * (x : K ⧸ N) = (x : K ⧸ N) * (t : K ⧸ N)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, this]

end Quotient

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
