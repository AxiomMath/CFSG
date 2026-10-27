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

namespace CFSG.ClassicalInvolution.Nobq

variable {X : Type*} [Group X]

structure UniqueInvNormal (t : X) (N : Subgroup X) : Prop where
  le_centralizer : N ≤ Subgroup.centralizer ({t} : Set X)
  conj_mem : ∀ g ∈ Subgroup.centralizer ({t} : Set X), ∀ n ∈ N, g * n * g⁻¹ ∈ N
  mem : t ∈ N
  eq_of_orderOf_eq_two : ∀ u ∈ N, orderOf u = 2 → u = t
  exists_orderOf_eq_four : ∃ s ∈ N, orderOf s = 4

@[expose] def NoUniqueInvNormal (X : Type*) [Group X] : Prop :=
  ∀ (t : X) (N : Subgroup X), orderOf t = 2 → ¬ UniqueInvNormal t N

theorem UniqueInvNormal.map {Y : Type*} [Group Y] (e : X ≃* Y) {t : X} {N : Subgroup X}
    (h : UniqueInvNormal t N) : UniqueInvNormal (e t) (N.map e.toMonoidHom) := by
  refine ⟨?_, ?_, ⟨t, h.mem, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨n, hn, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show e n * e t = e t * e n
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hn)]
  · intro g hg _ ⟨n, hn, hne⟩
    subst hne
    have hg' : e.symm g ∈ Subgroup.centralizer ({t} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hg
    refine ⟨e.symm g * n * (e.symm g)⁻¹, h.conj_mem _ hg' n hn, ?_⟩
    simp
  · rintro _ ⟨u, hu, rfl⟩ ho
    have : orderOf u = 2 := by
      rw [← ho]
      exact (MulEquiv.orderOf_eq e u).symm
    exact congrArg e (h.eq_of_orderOf_eq_two u hu this)
  · obtain ⟨s, hs, hs4⟩ := h.exists_orderOf_eq_four
    exact ⟨e s, ⟨s, hs, rfl⟩, by rw [MulEquiv.orderOf_eq]; exact hs4⟩

theorem UniqueInvNormal.conj {t : X} {N : Subgroup X} (h : UniqueInvNormal t N) (g : X) :
    UniqueInvNormal (g * t * g⁻¹) (N.map (MulAut.conj g).toMonoidHom) :=
  h.map (MulAut.conj g)

theorem NoUniqueInvNormal.of_mulEquiv {Y : Type*} [Group Y] (e : X ≃* Y)
    (h : NoUniqueInvNormal Y) : NoUniqueInvNormal X := by
  intro t N ht hN
  refine h (e t) (N.map e.toMonoidHom) ?_ (hN.map e)
  rw [MulEquiv.orderOf_eq]
  exact ht

theorem NoUniqueInvNormal.of_conj_reps (reps : Set X)
    (hcov : ∀ u : X, orderOf u = 2 → ∃ r ∈ reps, ∃ g : X, u = g * r * g⁻¹)
    (hreps : ∀ r ∈ reps, orderOf r = 2 → ∀ N : Subgroup X, ¬ UniqueInvNormal r N) :
    NoUniqueInvNormal X := by
  intro t N ht hN
  obtain ⟨r, hr, g, rfl⟩ := hcov t ht
  have hr2 : orderOf r = 2 := by
    rw [← ht]
    exact (MulEquiv.orderOf_eq (MulAut.conj g) r).symm
  refine hreps r hr hr2 (N.map (MulAut.conj g⁻¹).toMonoidHom) ?_
  have := hN.conj g⁻¹
  rwa [inv_inv, show g⁻¹ * (g * r * g⁻¹) * g = r by group] at this

section Criteria

variable {t : X} {N : Subgroup X}

theorem UniqueInvNormal.exists_sq_eq (h : UniqueInvNormal t N) :
    ∃ s ∈ N, s * s = t ∧ orderOf s = 4 := by
  obtain ⟨s, hs, hs4⟩ := h.exists_orderOf_eq_four
  refine ⟨s, hs, ?_, hs4⟩
  have h2 : orderOf (s ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd (by omega) (by omega), hs4]
  rw [← pow_two]
  exact h.eq_of_orderOf_eq_two _ (N.pow_mem hs 2) h2

theorem not_uniqueInvNormal_of_no_square
    (hsq : ∀ c ∈ Subgroup.centralizer ({t} : Set X), c * c ≠ t) : ¬ UniqueInvNormal t N := by
  intro h
  obtain ⟨s, hs, hst, -⟩ := h.exists_sq_eq
  exact hsq s (h.le_centralizer hs) hst

theorem not_uniqueInvNormal_of_index_two (N₀ : Subgroup X)
    (hidx : (N₀.subgroupOf (Subgroup.centralizer ({t} : Set X))).index = 2) (htN : t ∉ N₀) :
    ¬ UniqueInvNormal t N :=
  not_uniqueInvNormal_of_no_square fun c hc hct => htN (by
    have := Subgroup.mul_self_mem_of_index_two hidx (⟨c, hc⟩ : Subgroup.centralizer ({t} : Set X))
    rwa [Subgroup.mem_subgroupOf, Subgroup.coe_mul, hct] at this)

theorem not_uniqueInvNormal_of_witness
    (hw : ∀ c ∈ Subgroup.centralizer ({t} : Set X), c * c = t →
      ∃ g ∈ Subgroup.centralizer ({t} : Set X),
        (c * (g * c * g⁻¹)) * (c * (g * c * g⁻¹)) = 1 ∧ c * (g * c * g⁻¹) ≠ 1 ∧
          c * (g * c * g⁻¹) ≠ t) :
    ¬ UniqueInvNormal t N := by
  intro h
  obtain ⟨s, hs, hst, -⟩ := h.exists_sq_eq
  obtain ⟨g, hg, hx2, hx1, hxt⟩ := hw s (h.le_centralizer hs) hst
  have hx : s * (g * s * g⁻¹) ∈ N := N.mul_mem hs (h.conj_mem g hg s hs)
  have hord : orderOf (s * (g * s * g⁻¹)) = 2 := orderOf_eq_prime (by rwa [pow_two]) hx1
  exact hxt (h.eq_of_orderOf_eq_two _ hx hord)

theorem exists_conj_mem_of_twoPow {C : Type*} [Group C] [Finite C] (T : Subgroup C)
    (hT : IsPGroup 2 T) (hidx : ¬ 2 ∣ T.index) {u : C} {k : ℕ} (hu : u ^ (2 ^ k) = 1) :
    ∃ c : C, c * u * c⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Sylow 2 C := hT.toSylow hidx
  have hz : IsPGroup 2 (Subgroup.zpowers u) := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hu)
    refine IsPGroup.of_card (n := m) ?_
    rw [Nat.card_zpowers, hm]
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C Q S'
  refine ⟨g, ?_⟩
  have h1 : u ∈ (Q : Subgroup C) := hQ (Subgroup.mem_zpowers u)
  have h2 : g * u * g⁻¹ ∈ ((g • Q : Sylow 2 C) : Subgroup C) := by
    rw [Sylow.coe_subgroup_smul]
    exact ⟨u, h1, rfl⟩
  rw [hg] at h2
  exact h2

theorem not_uniqueInvNormal_of_witness_sylow [Finite X] (T : Subgroup X) (hT : IsPGroup 2 T)
    (hidx : ¬ 2 ∣ (T.subgroupOf (Subgroup.centralizer ({t} : Set X))).index)
    (hw : ∀ c ∈ T, c * c = t →
      ∃ g ∈ Subgroup.centralizer ({t} : Set X),
        (c * (g * c * g⁻¹)) * (c * (g * c * g⁻¹)) = 1 ∧ c * (g * c * g⁻¹) ≠ 1 ∧
          c * (g * c * g⁻¹) ≠ t) :
    ¬ UniqueInvNormal t N := by
  intro h
  obtain ⟨s, hs, hst, hs4⟩ := h.exists_sq_eq
  set C := Subgroup.centralizer ({t} : Set X) with hC
  have hTp : IsPGroup 2 (T.subgroupOf C) := hT.comap_of_injective C.subtype C.subtype_injective
  have hsC : s ∈ C := h.le_centralizer hs
  have hu : (⟨s, hsC⟩ : C) ^ (2 ^ 2) = 1 := by
    apply Subtype.ext
    simp [← hs4, pow_orderOf_eq_one]
  obtain ⟨c₀, hc₀⟩ := exists_conj_mem_of_twoPow (T.subgroupOf C) hTp hidx hu
  have hcT : (c₀ : X) * s * (c₀ : X)⁻¹ ∈ T := by
    have := Subgroup.mem_subgroupOf.1 hc₀
    simpa using this
  have hcN : (c₀ : X) * s * (c₀ : X)⁻¹ ∈ N := h.conj_mem c₀ c₀.2 s hs
  have hc2 : ((c₀ : X) * s * (c₀ : X)⁻¹) * ((c₀ : X) * s * (c₀ : X)⁻¹) = t := by
    have hct : (c₀ : X) * t * (c₀ : X)⁻¹ = t := by
      have := Subgroup.mem_centralizer_singleton_iff.mp c₀.2
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    calc ((c₀ : X) * s * (c₀ : X)⁻¹) * ((c₀ : X) * s * (c₀ : X)⁻¹)
        = (c₀ : X) * (s * s) * (c₀ : X)⁻¹ := by group
      _ = t := by rw [hst, hct]
  obtain ⟨g, hg, hx2, hx1, hxt⟩ := hw _ hcT hc2
  have hx : ((c₀ : X) * s * (c₀ : X)⁻¹) * (g * ((c₀ : X) * s * (c₀ : X)⁻¹) * g⁻¹) ∈ N :=
    N.mul_mem hcN (h.conj_mem g hg _ hcN)
  have hord : orderOf (((c₀ : X) * s * (c₀ : X)⁻¹) *
      (g * ((c₀ : X) * s * (c₀ : X)⁻¹) * g⁻¹)) = 2 :=
    orderOf_eq_prime (by rwa [pow_two]) hx1
  exact hxt (h.eq_of_orderOf_eq_two _ hx hord)

end Criteria

end CFSG.ClassicalInvolution.Nobq
