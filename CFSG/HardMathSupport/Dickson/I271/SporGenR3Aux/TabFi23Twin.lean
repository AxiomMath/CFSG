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

namespace CFSG.HardMathSupport.Dickson.I271.TabFi23

section Twin

variable {S ι : Type*} [Group S] [MulAction S ι] (e : ι → S) (x : S)

@[expose] def Twin (a b : ι) : Prop :=
  x • a = a ∧ x • b = b ∧ a ≠ b ∧ e a * e b ≠ e b * e a ∧
    ∀ c, x • c = c → c ≠ a → c ≠ b → (e c * e a = e a * e c ↔ e c * e b = e b * e c)

@[expose] def twinProd : Set S := {s | ∃ a b, Twin e x a b ∧ s = e a * e b}

@[expose] def twinSub : Subgroup S := Subgroup.closure (twinProd e x)

variable {e x}

theorem twin_conj_comm_iff (g a b : S) :
    (g * a * g⁻¹) * (g * b * g⁻¹) = (g * b * g⁻¹) * (g * a * g⁻¹) ↔ a * b = b * a := by
  have e1 : (g * a * g⁻¹) * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
  have e2 : (g * b * g⁻¹) * (g * a * g⁻¹) = g * (b * a) * g⁻¹ := by group
  rw [e1, e2]
  constructor
  · intro H
    exact mul_left_cancel (mul_right_cancel H)
  · intro H
    rw [H]

theorem e_comm_of_fix (hconj : ∀ (g : S) (i : ι), e (g • i) = g * e i * g⁻¹) {a : ι}
    (ha : x • a = a) : e a * x = x * e a := by
  have h := hconj x a
  rw [ha] at h
  calc e a * x = (x * e a * x⁻¹) * x := by rw [← h]
    _ = x * e a := by group

theorem rho_smul (hconj : ∀ (g : S) (i : ι), e (g • i) = g * e i * g⁻¹) (g : S) (a b : ι) :
    g * (e a * e b) * g⁻¹ = e (g • a) * e (g • b) := by
  rw [hconj, hconj]
  group

theorem smul_comm_of_comm {g : S} (hg : g * x = x * g) (i : ι) : x • g • i = g • x • i := by
  rw [← mul_smul, ← mul_smul, hg.symm]

theorem twin_smul (hconj : ∀ (g : S) (i : ι), e (g • i) = g * e i * g⁻¹) {g : S}
    (hg : g * x = x * g) {a b : ι} (h : Twin e x a b) : Twin e x (g • a) (g • b) := by
  obtain ⟨ha, hb, hab, hnc, hc⟩ := h
  have hg' : g⁻¹ * x = x * g⁻¹ := by
    calc g⁻¹ * x = g⁻¹ * (x * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * x) * g⁻¹ := by rw [hg]
      _ = x * g⁻¹ := by group
  refine ⟨by rw [smul_comm_of_comm hg, ha], by rw [smul_comm_of_comm hg, hb],
    fun h => hab (MulAction.injective g h), ?_, ?_⟩
  · rw [hconj, hconj]
    intro H
    exact hnc ((twin_conj_comm_iff g (e a) (e b)).1 H)
  · intro c hcx hca hcb
    obtain ⟨c', rfl⟩ : ∃ c', c = g • c' := ⟨g⁻¹ • c, by rw [smul_inv_smul]⟩
    have hc'x : x • c' = c' := by
      have h1 : x • g • c' = g • c' := hcx
      rw [smul_comm_of_comm hg] at h1
      exact MulAction.injective g h1
    have hc'a : c' ≠ a := fun h => hca (by rw [h])
    have hc'b : c' ≠ b := fun h => hcb (by rw [h])
    have h2 := hc c' hc'x hc'a hc'b
    rw [hconj g c', hconj g a, hconj g b, twin_conj_comm_iff, twin_conj_comm_iff]
    exact h2

theorem twinProd_comm_x (hconj : ∀ (g : S) (i : ι), e (g • i) = g * e i * g⁻¹) :
    twinProd e x ⊆ (Subgroup.centralizer ({x} : Set S) : Set S) := by
  rintro _ ⟨a, b, ⟨ha, hb, -⟩, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  have h1 := e_comm_of_fix hconj ha
  have h2 := e_comm_of_fix hconj hb
  calc e a * e b * x = e a * (e b * x) := by rw [mul_assoc]
    _ = e a * (x * e b) := by rw [h2]
    _ = (e a * x) * e b := by rw [mul_assoc]
    _ = (x * e a) * e b := by rw [h1]
    _ = x * (e a * e b) := by rw [mul_assoc]

theorem twinSub_le_cent (hconj : ∀ (g : S) (i : ι), e (g • i) = g * e i * g⁻¹) :
    twinSub e x ≤ Subgroup.centralizer ({x} : Set S) :=
  (Subgroup.closure_le _).2 (twinProd_comm_x hconj)

theorem twinSub_conj_mem (hconj : ∀ (g : S) (i : ι), e (g • i) = g * e i * g⁻¹) {g : S}
    (hg : g ∈ Subgroup.centralizer ({x} : Set S)) {q : S} (hq : q ∈ twinSub e x) :
    g * q * g⁻¹ ∈ twinSub e x := by
  have hg' : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 hg
  induction hq using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨a, b, hab, rfl⟩ := hs
    rw [rho_smul hconj]
    exact Subgroup.subset_closure ⟨g • a, g • b, twin_smul hconj hg' hab, rfl⟩
  | one => simp
  | mul s t _ _ hs ht =>
    have : g * (s * t) * g⁻¹ = (g * s * g⁻¹) * (g * t * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hs ht
  | inv s _ hs =>
    have : g * s⁻¹ * g⁻¹ = (g * s * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hs

theorem smul_cube_of_cent (hconj : ∀ (g : S) (i : ι), e (g • i) = g * e i * g⁻¹)
    (third : ι → ι → ι)
    (hK2 : ∀ a b a' b', Twin e x a b → Twin e x a' b' → e a' * e b' = e a * e b →
      (a' = a ∧ b' = b) ∨ (a' = b ∧ b' = third a b) ∨ (a' = third a b ∧ b' = a))
    (hK2b : ∀ a b, Twin e x a b → third a b ≠ a ∧ third a b ≠ b)
    {g : S} (hgx : g * x = x * g)
    (hgc : ∀ a b, Twin e x a b → g * (e a * e b) = (e a * e b) * g)
    {a b : ι} (hab : Twin e x a b) : g • g • g • a = a := by
  have key : ∀ u v, Twin e x u v →
      Twin e x (g • u) (g • v) ∧ e (g • u) * e (g • v) = e u * e v := by
    intro u v h
    refine ⟨twin_smul hconj hgx h, ?_⟩
    rw [← rho_smul hconj]
    calc g * (e u * e v) * g⁻¹ = (e u * e v) * g * g⁻¹ := by rw [hgc u v h]
      _ = e u * e v := by group
  obtain ⟨hc1, hc2⟩ := hK2b a b hab
  obtain ⟨T1, E1⟩ := key a b hab
  rcases hK2 a b (g • a) (g • b) hab T1 E1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [h1]
  · rw [h1, h2] at T1 E1
    obtain ⟨T2, E2⟩ := key b (third a b) T1
    rw [h2] at T2 E2
    have E3 : e (third a b) * e (g • third a b) = e a * e b := E2.trans E1
    rcases hK2 a b (third a b) (g • third a b) hab T2 E3 with ⟨h3, -⟩ | ⟨h3, -⟩ | ⟨-, h3⟩
    · exact absurd h3 hc1
    · exact absurd h3 hc2
    · rw [h1, h2, h3]
  · rw [h1, h2] at T1 E1
    obtain ⟨T2, E2⟩ := key (third a b) a T1
    rw [h1] at T2 E2
    have E3 : e (g • third a b) * e (third a b) = e a * e b := E2.trans E1
    rcases hK2 a b (g • third a b) (third a b) hab T2 E3 with ⟨-, h3⟩ | ⟨h3, -⟩ | ⟨-, h3⟩
    · exact absurd h3 hc2
    · rw [h1, h3, h2]
    · exact absurd h3 hc1

theorem cube_smul_eq {r : S} (hrx : r * x = x * r) (hx3 : x * x * x = 1) (z : ι)
    (h : r • z = z ∨ r • z = x • z ∨ r • z = x • x • z) : r • r • r • z = z := by
  have comm : ∀ y : ι, r • x • y = x • r • y := fun y => (smul_comm_of_comm hrx y).symm
  have hx : ∀ y : ι, x • x • x • y = y := fun y => by
    rw [← mul_smul, ← mul_smul, hx3, one_smul]
  rcases h with h | h | h
  · simp only [h]
  · simp only [h, comm, hx]
  · simp only [h, comm, hx]

theorem pow_three_eq_one_of_fix (hconj : ∀ (g : S) (i : ι), e (g • i) = g * e i * g⁻¹)
    (hx3 : x * x * x = 1) {κ : Type*} (c : κ → ι)
    (hsep : ∀ s : S, (∀ t, s • c t = c t) → s = 1)
    (hK4 : ∀ (t : κ) (c' : ι), (∀ a : ι, x • a = a →
      (e c' * e a = e a * e c' ↔ e (c t) * e a = e a * e (c t))) →
      c' = c t ∨ c' = x • c t ∨ c' = x • x • c t)
    {r : S} (hrx : r * x = x * r) (hrF : ∀ a : ι, x • a = a → r • a = a) : r * r * r = 1 := by
  apply hsep
  intro t
  have hprof : ∀ a : ι, x • a = a →
      (e (r • c t) * e a = e a * e (r • c t) ↔ e (c t) * e a = e a * e (c t)) := by
    intro a ha
    have h1 : e (r • c t) = r * e (c t) * r⁻¹ := hconj r (c t)
    have h2 : e a = r * e a * r⁻¹ := by
      have := hconj r a
      rwa [hrF a ha] at this
    have := twin_conj_comm_iff r (e (c t)) (e a)
    rw [← h1, ← h2] at this
    exact this
  have hc := cube_smul_eq hrx hx3 (c t) (hK4 t (r • c t) hprof)
  rw [mul_smul, mul_smul]
  exact hc

theorem pConstrained_of_twins (hconj : ∀ (g : S) (i : ι), e (g • i) = g * e i * g⁻¹)
    (hx3 : x * x * x = 1) (third : ι → ι → ι)
    (hK1 : ∀ a : ι, x • a = a → ∃ b, Twin e x a b)
    (hK2 : ∀ a b a' b', Twin e x a b → Twin e x a' b' → e a' * e b' = e a * e b →
      (a' = a ∧ b' = b) ∨ (a' = b ∧ b' = third a b) ∨ (a' = third a b ∧ b' = a))
    (hK2b : ∀ a b, Twin e x a b → third a b ≠ a ∧ third a b ≠ b)
    (hK3 : ∀ a b a' b', Twin e x a b → Twin e x a' b' →
      e a * e b * (e a' * e b') = e a' * e b' * (e a * e b))
    {κ : Type*} (c : κ → ι) (hsep : ∀ s : S, (∀ t, s • c t = c t) → s = 1)
    (hK4 : ∀ (t : κ) (c' : ι), (∀ a : ι, x • a = a →
      (e c' * e a = e a * e c' ↔ e (c t) * e a = e a * e (c t))) →
      c' = c t ∨ c' = x • c t ∨ c' = x • x • c t) :
    ∃ Q : Subgroup S, Q ≤ Subgroup.centralizer ({x} : Set S) ∧
      (∀ g ∈ Subgroup.centralizer ({x} : Set S), ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) ∧ IsPGroup 3 Q ∧
      Subgroup.centralizer ({x} : Set S) ⊓ Subgroup.centralizer (Q : Set S) ≤ Q := by
  set C : Subgroup S := Subgroup.centralizer ({x} : Set S) with hC
  set Q0 : Subgroup S := twinSub e x with hQ0
  have hQ0C : Q0 ≤ C := twinSub_le_cent hconj
  have hab : ∀ q ∈ Q0, ∀ q' ∈ Q0, q * q' = q' * q := by
    have h1 : ∀ a b, Twin e x a b → Q0 ≤ Subgroup.centralizer ({e a * e b} : Set S) := by
      intro a b hab
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨a', b', hab', rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (hK3 a b a' b' hab hab').symm
    have h2 : Q0 ≤ Subgroup.centralizer (Q0 : Set S) := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨a, b, hab, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro q hq
      exact (Subgroup.mem_centralizer_singleton_iff.1 (h1 a b hab hq))
    intro q hq q' hq'
    exact (Subgroup.mem_centralizer_iff.1 (h2 hq) q' hq').symm
  have hQ0Y : ∀ q ∈ Q0, q ∈ C ⊓ Subgroup.centralizer (Q0 : Set S) := fun q hq =>
    ⟨hQ0C hq, Subgroup.mem_centralizer_iff.2 fun q' hq' => hab q' hq' q hq⟩
  refine ⟨C ⊓ Subgroup.centralizer (Q0 : Set S), inf_le_left, ?_, ?_, ?_⟩
  ·
    intro g hg y hy
    refine ⟨C.mul_mem (C.mul_mem hg hy.1) (C.inv_mem hg), Subgroup.mem_centralizer_iff.2 ?_⟩
    intro q hq
    have hq' : g⁻¹ * q * g ∈ Q0 := by
      simpa using twinSub_conj_mem hconj (C.inv_mem hg) hq
    have h1 := Subgroup.mem_centralizer_iff.1 hy.2 (g⁻¹ * q * g) hq'
    calc q * (g * y * g⁻¹) = g * ((g⁻¹ * q * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * q * g)) * g⁻¹ := by rw [h1]
      _ = (g * y * g⁻¹) * q := by group
  ·
    intro g
    refine ⟨2, ?_⟩
    have hyC : (g : S) ∈ C := g.2.1
    have hyQ : (g : S) ∈ Subgroup.centralizer (Q0 : Set S) := g.2.2
    have hyx : (g : S) * x = x * (g : S) := Subgroup.mem_centralizer_singleton_iff.1 hyC
    have hycube : ((g : S) * g * g) * x = x * ((g : S) * g * g) := by
      calc (g : S) * g * g * x = (g : S) * g * ((g : S) * x) := by group
        _ = (g : S) * g * (x * g) := by rw [hyx]
        _ = (g : S) * ((g : S) * x) * g := by group
        _ = (g : S) * (x * g) * g := by rw [hyx]
        _ = ((g : S) * x) * g * g := by group
        _ = x * g * g * g := by rw [hyx]
        _ = x * ((g : S) * g * g) := by group
    have hyF : ∀ a : ι, x • a = a → ((g : S) * g * g) • a = a := by
      intro a ha
      obtain ⟨b, hb⟩ := hK1 a ha
      have h := smul_cube_of_cent hconj third hK2 hK2b hyx (fun u v huv =>
        (Subgroup.mem_centralizer_iff.1 hyQ (e u * e v)
          (Subgroup.subset_closure ⟨u, v, huv, rfl⟩)).symm) hb
      rw [mul_smul, mul_smul]
      exact h
    have h3 := pow_three_eq_one_of_fix hconj hx3 c hsep hK4 hycube hyF
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    calc (g : S) ^ 3 ^ 2 = ((g : S) * g * g) * ((g : S) * g * g) * ((g : S) * g * g) := by
          rw [show (3 : ℕ) ^ 2 = 9 from rfl]
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := h3
  ·
    intro z hz
    refine ⟨hz.1, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
    exact Subgroup.mem_centralizer_iff.1 hz.2 q (hQ0Y q hq)

end Twin

end CFSG.HardMathSupport.Dickson.I271.TabFi23
