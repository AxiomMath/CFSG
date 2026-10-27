module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.TransFin

open Equiv

theorem isPGroup_closure_of_comm {G : Type*} [Group G] {I : Set G} (hsq : ∀ u ∈ I, u * u = 1)
    (hcomm : ∀ u ∈ I, ∀ v ∈ I, u * v = v * u) : IsPGroup 2 (Subgroup.closure I) := by
  have h1 : ∀ x ∈ Subgroup.closure I, ∀ u ∈ I, x * u = u * x := by
    intro x hx u hu
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hcomm x hx u hu
    | one => simp
    | mul x y _ _ ihx ihy => rw [mul_assoc, ihy, ← mul_assoc, ihx, mul_assoc]
    | inv x _ ihx => exact (Commute.inv_left (show Commute x u from ihx))
  have h2 : ∀ x ∈ Subgroup.closure I, ∀ y ∈ Subgroup.closure I, x * y = y * x := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact h1 x hx y hy
    | one => simp
    | mul y z _ _ ihy ihz => rw [← mul_assoc, ihy, mul_assoc, ihz, mul_assoc]
    | inv y _ ihy => exact (Commute.inv_right (show Commute x y from ihy))
  have h3 : ∀ x ∈ Subgroup.closure I, x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hsq x hx
    | one => simp
    | mul x y hx hy ihx ihy =>
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [h2 y hy x hx]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [ihx, ihy, one_mul]
    | inv x _ ihx => rw [← mul_inv_rev, ihx, inv_one]
  intro g
  exact ⟨1, Subtype.ext (by simpa [sq] using h3 g g.2)⟩

theorem isPGroup_closure_pair {G : Type*} [Group G] {a q : G} (ha : a * a = 1) (hq : q * q = 1)
    (h4 : (a * q) ^ 4 = 1) : IsPGroup 2 (Subgroup.closure {a, q}) := by
  set r := a * q with hr
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hqi : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq
  have hra : a * r * a⁻¹ = r⁻¹ := by
    rw [hr, mul_inv_rev, hai, hqi, ← mul_assoc, ha, one_mul]
  have hconj : ∀ k : ℤ, a * r ^ k = r ^ (-k) * a := by
    intro k
    have : a * r ^ k * a⁻¹ = r ^ (-k) := by
      rw [← conj_zpow, hra, inv_zpow, zpow_neg]
    calc a * r ^ k = (a * r ^ k * a⁻¹) * a := by group
      _ = r ^ (-k) * a := by rw [this]
  have hr4 : ∀ k : ℤ, (r ^ k) ^ 4 = 1 := by
    intro k
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h4, one_zpow]
  let D : Subgroup G :=
    { carrier := {x | ∃ k : ℤ, x = r ^ k ∨ x = r ^ k * a}
      one_mem' := ⟨0, Or.inl (zpow_zero r).symm⟩
      mul_mem' := by
        rintro x y ⟨i, rfl | rfl⟩ ⟨j, rfl | rfl⟩
        · exact ⟨i + j, Or.inl (zpow_add r i j).symm⟩
        · exact ⟨i + j, Or.inr (by rw [zpow_add, mul_assoc])⟩
        · refine ⟨i - j, Or.inr ?_⟩
          calc r ^ i * a * r ^ j = r ^ i * (a * r ^ j) := by rw [mul_assoc]
            _ = r ^ i * (r ^ (-j) * a) := by rw [hconj]
            _ = r ^ (i - j) * a := by rw [← mul_assoc, ← zpow_add, sub_eq_add_neg]
        · refine ⟨i - j, Or.inl ?_⟩
          calc r ^ i * a * (r ^ j * a) = r ^ i * (a * r ^ j) * a := by group
            _ = r ^ i * (r ^ (-j) * a) * a := by rw [hconj]
            _ = r ^ i * r ^ (-j) * (a * a) := by group
            _ = r ^ (i - j) := by rw [ha, mul_one, ← zpow_add, sub_eq_add_neg]
      inv_mem' := by
        rintro x ⟨i, rfl | rfl⟩
        · exact ⟨-i, Or.inl (zpow_neg r i).symm⟩
        · refine ⟨i, Or.inr ?_⟩
          rw [mul_inv_rev, hai, ← zpow_neg, hconj, neg_neg] }
  have hsub : Subgroup.closure {a, q} ≤ D := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨0, Or.inr (by simp)⟩
    · refine ⟨-1, Or.inr ?_⟩
      rw [zpow_neg, zpow_one, hr, mul_inv_rev, hai, hqi, mul_assoc, ha, mul_one]
  intro g
  refine ⟨2, Subtype.ext ?_⟩
  obtain ⟨k, hk | hk⟩ := hsub g.2
  · have : (g : G) ^ 4 = 1 := by rw [hk]; exact hr4 k
    simpa using this
  · have h2 : (g : G) * g = 1 := by
      rw [hk]
      calc r ^ k * a * (r ^ k * a) = r ^ k * (a * r ^ k) * a := by group
        _ = r ^ k * (r ^ (-k) * a) * a := by rw [hconj]
        _ = r ^ k * r ^ (-k) * (a * a) := by group
        _ = 1 := by rw [ha, mul_one, ← zpow_add, add_neg_cancel, zpow_zero]
    have : (g : G) ^ 4 = 1 := by
      calc (g : G) ^ 4 = (g * g) * (g * g) := by simp [pow_succ, mul_assoc]
        _ = 1 := by rw [h2, mul_one]
    simpa using this

theorem exists_noncomm_swap {Q : Type*} [Group Q] (ι : Q →* Perm (Fin 6))
    (hι : Function.Injective ι)
    (hO2 : ∀ N : Subgroup Q, N.Normal → IsPGroup 2 N → N = ⊥) {t : Q} (ht : (ι t).IsSwap) :
    ∃ s : Q, (ι s).IsSwap ∧ s * t ≠ t * s := by
  by_contra hcon
  push Not at hcon
  set I : Set Q := {u | (ι u).IsSwap ∧ ∀ s, (ι s).IsSwap → s * u = u * s} with hI
  have htI : t ∈ I := ⟨ht, hcon⟩
  have hsq : ∀ u ∈ I, u * u = 1 := by
    intro u hu
    apply hι
    obtain ⟨x, y, hxy, hxy'⟩ := hu.1
    rw [map_mul, map_one, hxy', Equiv.swap_mul_self]
  have hcomm : ∀ u ∈ I, ∀ v ∈ I, u * v = v * u := fun u hu v hv => hv.2 u hu.1
  have hconjSwap : ∀ (g s : Q), (ι s).IsSwap → (ι (g * s * g⁻¹)).IsSwap := by
    intro g s ⟨x, y, hxy, hxy'⟩
    refine ⟨ι g x, ι g y, fun h => hxy ((ι g).injective h), ?_⟩
    rw [map_mul, map_mul, map_inv, hxy', Equiv.swap_apply_apply]
  have hinv : ∀ (g u : Q), u ∈ I → g * u * g⁻¹ ∈ I := by
    intro g u hu
    refine ⟨hconjSwap g u hu.1, fun s hs => ?_⟩
    have hs' : (ι (g⁻¹ * s * g⁻¹⁻¹)).IsSwap := hconjSwap g⁻¹ s hs
    rw [inv_inv] at hs'
    have := hu.2 _ hs'
    calc s * (g * u * g⁻¹) = g * ((g⁻¹ * s * g) * u) * g⁻¹ := by group
      _ = g * (u * (g⁻¹ * s * g)) * g⁻¹ := by rw [this]
      _ = (g * u * g⁻¹) * s := by group
  have hnormal : (Subgroup.closure I).Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (hinv g x hx)
    | one => simpa using Subgroup.one_mem _
    | mul x y _ _ ihx ihy =>
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ ihx ihy
    | inv x _ ihx =>
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ ihx
  have hbot := hO2 _ hnormal (isPGroup_closure_of_comm hsq hcomm)
  have : t ∈ Subgroup.closure I := Subgroup.subset_closure htI
  rw [hbot, Subgroup.mem_bot] at this
  obtain ⟨x, y, hxy, hxy'⟩ := ht
  rw [this, map_one] at hxy'
  have := congrArg (fun f => f x) hxy'
  simp at this
  exact hxy this

end CFSG.GF2Type.Aschbacher1976Full.HS.TransFin
