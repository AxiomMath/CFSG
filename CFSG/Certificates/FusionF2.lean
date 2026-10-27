module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Certificates

variable {G : Type*} [Group G]

open scoped IsMulCommutative

theorem subgroup_card_le_two (N : Subgroup G) [Finite N] (hN : Nat.card N ≤ 2) {a b c : G}
    (ha : a ∈ N) (hb : b ∈ N) (hc : c ∈ N) : a = b ∨ a = c ∨ b = c := by
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2, h3⟩ := hne
  have hfin : (N : Set G).Finite := Set.toFinite _
  have : 2 < (N : Set G).ncard :=
    (Set.two_lt_ncard hfin).mpr ⟨a, ha, b, hb, c, hc, h1, h2, h3⟩
  have hcard : Nat.card N = (N : Set G).ncard := Nat.card_coe_set_eq (N : Set G)
  omega

theorem kernel_central_sq (N : Subgroup G) [N.Normal] [Finite N] (hN : Nat.card N ≤ 2) {ν : G}
    (hν : ν ∈ N) : ν * ν = 1 ∧ ∀ g : G, g * ν = ν * g := by
  constructor
  · rcases subgroup_card_le_two N hN N.one_mem hν (N.mul_mem hν hν) with h | h | h
    · rw [← h]; simp
    · exact h.symm
    · have : ν * ν = ν * 1 := by rw [mul_one]; exact h.symm
      have := mul_left_cancel this
      rw [this]; simp
  · intro g
    have hc : g * ν * g⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance ν hν g
    rcases subgroup_card_le_two N hN N.one_mem hν hc with h | h | h
    · rw [← h]; simp
    · have : ν = 1 := by
        have h' : g * ν * g⁻¹ = 1 := h.symm
        simpa using h'
      rw [this]; simp
    · calc g * ν = g * ν * g⁻¹ * g := by group
        _ = ν * g := by rw [← h]

theorem lift_conj {k : ℕ} (f : Fin k → G) (g : G) (r : FreeGroup (Fin k)) :
    FreeGroup.lift (fun i => g⁻¹ * f i * g) r = g⁻¹ * FreeGroup.lift f r * g := by
  have : (MulAut.conj g⁻¹ : G ≃* G).toMonoidHom.comp (FreeGroup.lift f) =
      FreeGroup.lift (fun i => g⁻¹ * f i * g) := by
    apply FreeGroup.ext_hom
    intro i
    simp
  rw [← this]
  simp

theorem prod_eq_one_of_even {k : ℕ} (ν : Fin k → G) (hc : ∀ i g, g * ν i = ν i * g)
    (hsq : ∀ i, ν i * ν i = 1) (w : List (Fin k × Bool))
    (hev : ∀ i, Even ((w.map Prod.fst).count i)) : (w.map fun l => ν l.1).prod = 1 := by
  set C := Subgroup.center G
  let ν' : Fin k → C := fun i => ⟨ν i, Subgroup.mem_center_iff.mpr fun g => (hc i g)⟩
  have hsq' : ∀ i, ν' i * ν' i = 1 := fun i => Subtype.ext (hsq i)
  have key : ((w.map Prod.fst).map ν').prod = 1 := by
    rw [Finset.prod_list_map_count]
    apply Finset.prod_eq_one
    intro i _
    obtain ⟨j, hj⟩ := hev i
    rw [hj, ← two_mul, pow_mul, pow_two, hsq' i, one_pow]
  have hmap : (w.map fun l => ν l.1) = ((w.map Prod.fst).map ν').map C.subtype := by
    simp [List.map_map, Function.comp_def, ν']
  rw [hmap, ← map_list_prod, key]
  simp

theorem eq_one_of_fusion (N : Subgroup G) [N.Normal] [Finite N] (hN : Nat.card N ≤ 2) (n : G)
    {k : ℕ} (f f' : Fin k → G) (g : G) (hconj : ∀ i, g⁻¹ * f i * g * (f' i)⁻¹ ∈ N)
    (ρ : List (Fin k × Bool)) (hev : ∀ i, Even ((ρ.map Prod.fst).count i))
    (h1 : FreeGroup.lift f (FreeGroup.mk ρ) = n) (h2 : FreeGroup.lift f' (FreeGroup.mk ρ) = 1) :
    n = 1 := by
  obtain ⟨ν, hν⟩ : ∃ ν : Fin k → G, ∀ i, ν i = g⁻¹ * f i * g * (f' i)⁻¹ := ⟨_, fun _ => rfl⟩
  have hνN : ∀ i, ν i ∈ N := fun i => hν i ▸ hconj i
  have hνc : ∀ i g', g' * ν i = ν i * g' := fun i g' => (kernel_central_sq N hN (hνN i)).2 g'
  have hνsq : ∀ i, ν i * ν i = 1 := fun i => (kernel_central_sq N hN (hνN i)).1
  have hf : ∀ i, g⁻¹ * f i * g = ν i * f' i := by
    intro i; rw [hν]; group
  have hνinv : ∀ i, (ν i)⁻¹ = ν i := fun i => inv_eq_of_mul_eq_one_right (hνsq i)
  have hP : ∀ w : List (Fin k × Bool), ∀ g', g' * (w.map fun l => ν l.1).prod =
      (w.map fun l => ν l.1).prod * g' := by
    intro w
    induction w with
    | nil => intro g'; simp
    | cons l w ih =>
      intro g'
      simp only [List.map_cons, List.prod_cons]
      calc g' * (ν l.1 * (w.map fun l => ν l.1).prod)
          = (g' * ν l.1) * (w.map fun l => ν l.1).prod := by rw [mul_assoc]
        _ = (ν l.1 * g') * (w.map fun l => ν l.1).prod := by rw [hνc]
        _ = ν l.1 * (g' * (w.map fun l => ν l.1).prod) := by rw [mul_assoc]
        _ = ν l.1 * ((w.map fun l => ν l.1).prod * g') := by rw [ih]
        _ = (ν l.1 * (w.map fun l => ν l.1).prod) * g' := by rw [mul_assoc]
  have hA : ∀ w : List (Fin k × Bool),
      FreeGroup.lift (fun i => g⁻¹ * f i * g) (FreeGroup.mk w) =
        (w.map fun l => ν l.1).prod * FreeGroup.lift f' (FreeGroup.mk w) := by
    intro w
    induction w with
    | nil => simp [← FreeGroup.one_eq_mk]
    | cons l w ih =>
      obtain ⟨i, b⟩ := l
      rw [show FreeGroup.mk ((i, b) :: w) = FreeGroup.mk [(i, b)] * FreeGroup.mk w from rfl,
        map_mul, map_mul, ih]
      simp only [List.map_cons, List.prod_cons]
      set Pw := (w.map fun l => ν l.1).prod with hPw
      set Lw := FreeGroup.lift f' (FreeGroup.mk w) with hLw
      have hPc := hP w
      cases b
      · rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv, map_inv,
          FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, hf, mul_inv_rev, hνinv]
        have c1 : (f' i)⁻¹ * ν i = ν i * (f' i)⁻¹ := hνc i _
        have c2 : (f' i)⁻¹ * Pw = Pw * (f' i)⁻¹ := hPc _
        calc (f' i)⁻¹ * ν i * (Pw * Lw) = ν i * (f' i)⁻¹ * (Pw * Lw) := by rw [c1]
          _ = ν i * ((f' i)⁻¹ * Pw) * Lw := by simp only [mul_assoc]
          _ = ν i * (Pw * (f' i)⁻¹) * Lw := by rw [c2]
          _ = ν i * Pw * ((f' i)⁻¹ * Lw) := by simp only [mul_assoc]
      · rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of,
          FreeGroup.lift_apply_of, hf]
        have c2 : f' i * Pw = Pw * f' i := hPc _
        calc ν i * f' i * (Pw * Lw) = ν i * (f' i * Pw) * Lw := by simp only [mul_assoc]
          _ = ν i * (Pw * f' i) * Lw := by rw [c2]
          _ = ν i * Pw * (f' i * Lw) := by simp only [mul_assoc]
  have h3 : FreeGroup.lift (fun i => g⁻¹ * f i * g) (FreeGroup.mk ρ) = 1 := by
    rw [hA, prod_eq_one_of_even ν hνc hνsq ρ hev, h2, mul_one]
  rw [lift_conj, h1] at h3
  have : g⁻¹ * n * g = 1 := h3
  calc n = g * (g⁻¹ * n * g) * g⁻¹ := by group
    _ = 1 := by rw [this]; simp

end CFSG.Certificates
