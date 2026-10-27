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

namespace CFSG.QuasithinUnique.Id2519.Tab.A2

structure A2Data {X A : Type*} [Group X] [Group A] (π : X →* A) (c : X) (τ : X →* X) (r : A)
    (K : Subgroup X) (P U : Set A) (a₀ z : A) : Prop where
  cc : c * c = 1
  c1 : c ≠ 1
  cz : ∀ x, x * c = c * x
  πc : π c = 1
  ker : ∀ x, π x = 1 → x = 1 ∨ x = c
  τ2 : ∀ x, τ (τ x) = x
  τπ : ∀ x, π (τ x) = r * π x * r⁻¹
  Kτ : ∀ k ∈ K, τ k = k
  Kker : ∀ k ∈ K, π k = 1 → k = 1
  U1 : (1 : A) ∈ U
  Um : ∀ a ∈ U, ∀ b ∈ U, a * b ∈ U
  Usq : ∀ a ∈ U, a * a = 1
  PU : ∀ p ∈ P, ∀ a ∈ U, p * a * p⁻¹ ∈ U
  rU : ∀ a ∈ U, r * a * r⁻¹ ∈ U
  lift : ∀ p ∈ P, ∃ x, π x = p
  UP : U ⊆ P
  a₀U : a₀ ∈ U
  a₀1 : a₀ ≠ 1
  a₀K : a₀ ∈ K.map π
  trans : ∀ a ∈ U, a ≠ 1 → ∃ p ∈ P, a = p * a₀ * p⁻¹
  zP : z ∈ P
  zK : z ∈ K.map π
  z3 : z * z * z = 1
  zfpf : ∀ a ∈ U, z * a = a * z → a = 1
  red : ∀ k ∈ K, k * k = 1 → ∃ k' ∈ K, π (k' * k * k'⁻¹) ∈ U
  wit : ∀ a ∈ U, r * a = a * r → ∃ x ∈ U, r * x * r⁻¹ * x = a

theorem inv_eq_self_of_sq {M : Type*} [Group M] {v : M} (hv : v * v = 1) : v⁻¹ = v :=
  inv_eq_of_mul_eq_one_right hv

@[expose] def conjBy {M : Type*} [Group M] (g v : M) : M := g * v * g⁻¹

theorem conjBy_mul {M : Type*} [Group M] (g a b : M) :
    conjBy g (a * b) = conjBy g a * conjBy g b := by
  unfold conjBy
  group

theorem conjBy_cube {M : Type*} [Group M] {g : M} (h3 : g * g * g = 1) (v : M) :
    conjBy g (conjBy g (conjBy g v)) = v := by
  have : conjBy g (conjBy g (conjBy g v)) = (g * g * g) * v * (g * g * g)⁻¹ := by
    unfold conjBy
    group
  rw [this, h3]
  group

theorem six_comm {M : Type*} [Group M] {a b c d e f : M} (hbc : b * c = c * b)
    (hbe : b * e = e * b) (hde : d * e = e * d) :
    a * b * (c * d) * (e * f) = a * c * e * (b * d * f) := by
  calc a * b * (c * d) * (e * f) = a * (b * c) * d * e * f := by simp only [mul_assoc]
    _ = a * (c * b) * d * e * f := by rw [hbc]
    _ = a * c * (b * (d * e)) * f := by simp only [mul_assoc]
    _ = a * c * (b * (e * d)) * f := by rw [hde]
    _ = a * c * ((b * e) * d) * f := by simp only [mul_assoc]
    _ = a * c * ((e * b) * d) * f := by rw [hbe]
    _ = a * c * e * (b * d * f) := by simp only [mul_assoc]

namespace A2Data

variable {X A : Type*} [Group X] [Group A] {π : X →* A} {c : X} {τ : X →* X} {r : A}
  {K : Subgroup X} {P U : Set A} {a₀ z : A} (h : A2Data π c τ r K P U a₀ z)

include h

theorem τ_c : τ c = c := by
  rcases h.ker (τ c) (by rw [h.τπ, h.πc]; simp) with h1 | h1
  · exfalso
    apply h.c1
    have := h.τ2 c
    rw [h1, map_one] at this
    exact this.symm
  · exact h1

theorem cz' (x : X) : c * x = x * c := (h.cz x).symm

theorem sq_of_mem {v : X} (hv : π v ∈ U) : v * v = 1 := by
  by_cases h1 : π v = 1
  · rcases h.ker v h1 with rfl | rfl
    · simp
    · exact h.cc
  · obtain ⟨p, hp, hpa⟩ := h.trans (π v) hv h1
    obtain ⟨p', hp'⟩ := h.lift p hp
    obtain ⟨k₀, hk₀K, hk₀⟩ := Subgroup.mem_map.mp h.a₀K
    have hk₀sq : k₀ * k₀ = 1 := by
      have h2 : π (k₀ * k₀) = 1 := by rw [map_mul, hk₀]; exact h.Usq _ h.a₀U
      rcases h.ker _ h2 with h3 | h3
      · exact h3
      · exfalso
        apply h.c1
        apply h.Kker c _ h.πc
        rw [← h3]
        exact K.mul_mem hk₀K hk₀K
    set v' := p' * k₀ * p'⁻¹ with hv'
    have hv'π : π v' = π v := by
      rw [hv', map_mul, map_mul, map_inv, hp', hk₀, ← hpa]
    have hv'sq : v' * v' = 1 := by
      calc v' * v' = p' * (k₀ * k₀) * p'⁻¹ := by rw [hv']; group
        _ = 1 := by rw [hk₀sq]; group
    have h2 : π (v'⁻¹ * v) = 1 := by rw [map_mul, map_inv, hv'π, inv_mul_cancel]
    rcases h.ker _ h2 with h3 | h3
    · have : v = v' := by
        calc v = v' * (v'⁻¹ * v) := by group
          _ = v' := by rw [h3, mul_one]
      rw [this]
      exact hv'sq
    · have hv : v = v' * c := by rw [← h3]; group
      rw [hv]
      calc v' * c * (v' * c) = v' * (c * v') * c := by simp only [mul_assoc]
        _ = v' * (v' * c) * c := by rw [h.cz' v']
        _ = (v' * v') * (c * c) := by simp only [mul_assoc]
        _ = 1 := by rw [hv'sq, h.cc, one_mul]

theorem comm_of_mem {v w : X} (hv : π v ∈ U) (hw : π w ∈ U) : v * w = w * v := by
  have hvw : π (v * w) ∈ U := by rw [map_mul]; exact h.Um _ hv _ hw
  have h1 := h.sq_of_mem hvw
  have hv' := inv_eq_self_of_sq (h.sq_of_mem hv)
  have hw' := inv_eq_self_of_sq (h.sq_of_mem hw)
  have h2 : v * w = (v * w)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
  rw [h2, mul_inv_rev, hv', hw']

theorem mul_c3 (a b d : X) : a * c * (b * c) * (d * c) = a * b * d * (c * c * c) := by
  have e1 : ∀ x : X, c * x = x * c := fun x => (h.cz x).symm
  calc a * c * (b * c) * (d * c) = a * (c * b) * c * (d * c) := by simp only [mul_assoc]
    _ = a * (b * c) * c * (d * c) := by rw [e1 b]
    _ = a * b * (c * c) * (d * c) := by simp only [mul_assoc]
    _ = a * b * c * (c * d) * c := by simp only [mul_assoc]
    _ = a * b * c * (d * c) * c := by rw [e1 d]
    _ = a * b * (c * d) * c * c := by simp only [mul_assoc]
    _ = a * b * (d * c) * c * c := by rw [e1 d]
    _ = a * b * d * (c * c * c) := by simp only [mul_assoc]

theorem main : ∀ u ∈ K, u * u = 1 → ∃ x : X, (τ x)⁻¹ * x = u := by
  intro u huK hu2
  obtain ⟨zt, hztK, hzt⟩ := Subgroup.mem_map.mp h.zK
  have hzt3 : zt * zt * zt = 1 := by
    apply h.Kker _ (K.mul_mem (K.mul_mem hztK hztK) hztK)
    rw [map_mul, map_mul, hzt]
    exact h.z3
  have hztτ : τ zt = zt := h.Kτ zt hztK
  have hcc3 : c * c * c = c := by rw [h.cc, one_mul]
  have hTmem : ∀ v, π v ∈ U → π (conjBy zt v) ∈ U := by
    intro v hv
    unfold conjBy
    rw [map_mul, map_mul, map_inv, hzt]
    exact h.PU z h.zP _ hv
  have hTτ : ∀ v, τ (conjBy zt v) = conjBy zt (τ v) := by
    intro v
    unfold conjBy
    rw [map_mul, map_mul, map_inv, hztτ]
  have hTc : conjBy zt c = c := by
    unfold conjBy
    rw [h.cz zt]
    group
  have hTfix : ∀ v, π v ∈ U → conjBy zt v = v → v = 1 ∨ v = c := by
    intro v hv hT
    have h1 : z * π v = π v * z := by
      have := congrArg π hT
      unfold conjBy at this
      rw [map_mul, map_mul, map_inv, hzt] at this
      calc z * π v = (z * π v * z⁻¹) * z := by group
        _ = π v * z := by rw [this]
    exact h.ker v (h.zfpf _ hv h1)
  have hn_mem : ∀ v, π v ∈ U → π (v * conjBy zt v * conjBy zt (conjBy zt v)) ∈ U := by
    intro v hv
    rw [map_mul, map_mul]
    exact h.Um _ (h.Um _ hv _ (hTmem v hv)) _ (hTmem _ (hTmem v hv))
  have hn_fix : ∀ v, π v ∈ U →
      conjBy zt (v * conjBy zt v * conjBy zt (conjBy zt v)) =
        v * conjBy zt v * conjBy zt (conjBy zt v) := by
    intro v hv
    have h1 := hTmem v hv
    have h2 := hTmem _ h1
    have e : conjBy zt (v * conjBy zt v * conjBy zt (conjBy zt v)) =
        conjBy zt v * conjBy zt (conjBy zt v) * v := by
      rw [conjBy_mul, conjBy_mul, conjBy_cube hzt3]
    rw [e]
    calc conjBy zt v * conjBy zt (conjBy zt v) * v =
        conjBy zt v * (conjBy zt (conjBy zt v) * v) := by simp only [mul_assoc]
      _ = conjBy zt v * (v * conjBy zt (conjBy zt v)) := by rw [h.comm_of_mem h2 hv]
      _ = (conjBy zt v * v) * conjBy zt (conjBy zt v) := by simp only [mul_assoc]
      _ = (v * conjBy zt v) * conjBy zt (conjBy zt v) := by rw [h.comm_of_mem h1 hv]
  have hn_cases : ∀ v, π v ∈ U →
      v * conjBy zt v * conjBy zt (conjBy zt v) = 1 ∨
        v * conjBy zt v * conjBy zt (conjBy zt v) = c :=
    fun v hv => hTfix _ (hn_mem v hv) (hn_fix v hv)
  obtain ⟨k', hk'K, hk'U⟩ := h.red u huK hu2
  obtain ⟨u', hu'def⟩ : ∃ u' : X, u' = k' * u * k'⁻¹ := ⟨_, rfl⟩
  rw [← hu'def] at hk'U
  have hu'K : u' ∈ K := by
    rw [hu'def]
    exact K.mul_mem (K.mul_mem hk'K huK) (K.inv_mem hk'K)
  have hn_u' : u' * conjBy zt u' * conjBy zt (conjBy zt u') = 1 := by
    rcases hn_cases _ hk'U with h1 | h1
    · exact h1
    · exfalso
      apply h.c1
      apply h.Kker c _ h.πc
      rw [← h1]
      have h2 : conjBy zt u' ∈ K := by
        unfold conjBy
        exact K.mul_mem (K.mul_mem hztK hu'K) (K.inv_mem hztK)
      have h3 : conjBy zt (conjBy zt u') ∈ K := by
        unfold conjBy
        exact K.mul_mem (K.mul_mem hztK h2) (K.inv_mem hztK)
      exact K.mul_mem (K.mul_mem hu'K h2) h3
  have hr : r * π u' = π u' * r := by
    have := h.τπ u'
    rw [h.Kτ _ hu'K] at this
    calc r * π u' = (r * π u' * r⁻¹) * r := by group
      _ = π u' * r := by rw [← this]
  obtain ⟨xb, hxbU, hxb⟩ := h.wit _ hk'U hr
  obtain ⟨x, hx⟩ := h.lift xb (h.UP hxbU)
  have hxU : π x ∈ U := by rw [hx]; exact hxbU
  have hτxU : π (τ x) ∈ U := by rw [h.τπ, hx]; exact h.rU _ hxbU
  have hπs : π (τ x * x) = π u' := by
    rw [map_mul, h.τπ, hx]
    exact hxb
  have hns : (τ x * x) * conjBy zt (τ x * x) * conjBy zt (conjBy zt (τ x * x)) = 1 := by
    have hτ1 : τ (conjBy zt x) = conjBy zt (τ x) := hTτ x
    have hτ2 : τ (conjBy zt (conjBy zt x)) = conjBy zt (conjBy zt (τ x)) := by
      rw [hTτ, hTτ]
    have e1 : conjBy zt (τ x * x) = τ (conjBy zt x) * conjBy zt x := by
      rw [conjBy_mul, hτ1]
    have e2 : conjBy zt (conjBy zt (τ x * x)) =
        τ (conjBy zt (conjBy zt x)) * conjBy zt (conjBy zt x) := by
      rw [conjBy_mul, conjBy_mul, hτ2]
    rw [e2, e1]
    have h1 := hTmem x hxU
    have h2 := hTmem _ h1
    have hτ1U : π (τ (conjBy zt x)) ∈ U := by rw [hτ1]; exact hTmem _ hτxU
    have hτ2U : π (τ (conjBy zt (conjBy zt x))) ∈ U := by
      rw [hτ2]; exact hTmem _ (hTmem _ hτxU)
    rw [six_comm (h.comm_of_mem hxU hτ1U) (h.comm_of_mem hxU hτ2U) (h.comm_of_mem h1 hτ2U)]
    have e4 : τ x * τ (conjBy zt x) * τ (conjBy zt (conjBy zt x)) =
        τ (x * conjBy zt x * conjBy zt (conjBy zt x)) := by
      rw [map_mul, map_mul]
    rw [e4]
    rcases hn_cases x hxU with h3 | h3
    · rw [h3, map_one, one_mul]
    · rw [h3, h.τ_c, h.cc]
  have hsu : τ x * x = u' := by
    have h2 : π (u'⁻¹ * (τ x * x)) = 1 := by
      rw [map_mul, map_inv, hπs, inv_mul_cancel]
    rcases h.ker _ h2 with h3 | h3
    · calc τ x * x = u' * (u'⁻¹ * (τ x * x)) := by group
        _ = u' := by rw [h3, mul_one]
    · exfalso
      have hs : τ x * x = u' * c := by
        calc τ x * x = u' * (u'⁻¹ * (τ x * x)) := by group
          _ = u' * c := by rw [h3]
      rw [hs, conjBy_mul, hTc, conjBy_mul, hTc] at hns
      rw [h.mul_c3, hn_u', one_mul, hcc3] at hns
      exact h.c1 hns
  refine ⟨k'⁻¹ * x * k', ?_⟩
  have hτx2 : (τ x)⁻¹ = τ x := inv_eq_self_of_sq (h.sq_of_mem hτxU)
  have hτk : τ k' = k' := h.Kτ k' hk'K
  calc (τ (k'⁻¹ * x * k'))⁻¹ * (k'⁻¹ * x * k') =
      k'⁻¹ * ((τ x)⁻¹ * x) * k' := by
        rw [map_mul, map_mul, map_inv, hτk]
        group
    _ = k'⁻¹ * (τ x * x) * k' := by rw [hτx2]
    _ = u := by rw [hsu, hu'def]; group

end A2Data

end CFSG.QuasithinUnique.Id2519.Tab.A2
