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

namespace CFSG.LargeExtraspecial.S7

open Equiv

theorem perm_three_cases : ∀ σ : Perm (Fin 3), σ = 1 ∨ σ = swap 0 1 ∨ σ = swap 1 2 ∨
    σ = swap 0 1 * swap 1 2 ∨ σ = swap 1 2 * swap 0 1 ∨ σ = swap 0 1 * swap 1 2 * swap 0 1 := by
  decide

theorem perm_three_exists_conj (f : Perm (Fin 3) →* Perm (Fin 3)) (hf : Function.Injective f) :
    ∃ τ : Perm (Fin 3), ∀ σ, f σ = τ * σ * τ⁻¹ := by
  have key : ∀ a b : Perm (Fin 3), (a * a = 1 ∧ a ≠ 1 ∧ b * b = 1 ∧ b ≠ 1 ∧ a ≠ b) →
      ∃ τ : Perm (Fin 3), a = τ * swap 0 1 * τ⁻¹ ∧ b = τ * swap 1 2 * τ⁻¹ := by
    decide
  obtain ⟨τ, ha, hb⟩ := key (f (swap 0 1)) (f (swap 1 2))
    ⟨by rw [← map_mul, swap_mul_self, map_one], (map_ne_one_iff f hf).mpr (by decide),
      by rw [← map_mul, swap_mul_self, map_one], (map_ne_one_iff f hf).mpr (by decide),
      hf.ne (by decide)⟩
  refine ⟨τ, fun σ => ?_⟩
  rcases perm_three_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · exact ha
  · exact hb
  · rw [map_mul, ha, hb]
    group
  · rw [map_mul, ha, hb]
    group
  · rw [map_mul, map_mul, ha, hb]
    group

theorem perm_three_eq_one_of_comm :
    ∀ σ : Perm (Fin 3), (∀ τ : Perm (Fin 3), σ * τ = τ * σ) → σ = 1 := by
  decide

theorem perm_three_eq_of_comm_inv :
    ∀ σ τ : Perm (Fin 3), τ * τ = 1 → τ ≠ 1 → σ * τ = τ * σ → σ = 1 ∨ σ = τ := by
  decide

theorem nonempty_mulEquiv_perm_three {X : Type*} [Group X] [Finite X] (hX : Nat.card X = 6)
    {T : Subgroup X} (hT : Nat.card T = 2) (hTn : ¬ T.Normal) :
    Nonempty (X ≃* Perm (Fin 3)) := by
  have hcore : T.normalCore = ⊥ := by
    have hdvd : Nat.card T.normalCore ∣ 2 := hT ▸ Subgroup.card_dvd_of_le (Subgroup.normalCore_le T)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      apply hTn
      have heq : T.normalCore = T :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.normalCore_le T) (by rw [h, hT])
      rw [← heq]
      exact Subgroup.normalCore_normal T
  have hindex : T.index = 3 := by
    have h := Subgroup.card_mul_index T
    rw [hT, hX] at h
    omega
  have hcardQ : Nat.card (X ⧸ T) = 3 := by
    rw [← Subgroup.index_eq_card, hindex]
  have hinj : Function.Injective (MulAction.toPermHom X (X ⧸ T)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, hcore]
  have hbij : Function.Bijective (MulAction.toPermHom X (X ⧸ T)) :=
    hinj.bijective_of_nat_card_le (by rw [Nat.card_perm, hcardQ, hX]; decide)
  exact ⟨(MulEquiv.ofBijective _ hbij).trans
    (Equiv.permCongrHom (Finite.equivFinOfCardEq hcardQ))⟩

theorem nonempty_mulEquiv_prod {X : Type*} [Group X] {M A B : Subgroup X} (hAM : A ≤ M)
    (hBM : B ≤ M) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hdisj : A ⊓ B = ⊥)
    (hgen : ∀ m ∈ M, ∃ a ∈ A, ∃ b ∈ B, m = a * b) : Nonempty (M ≃* A × B) := by
  let f : A × B →* M :=
    { toFun := fun p => ⟨(p.1 : X) * p.2, M.mul_mem (hAM p.1.2) (hBM p.2.2)⟩
      map_one' := by ext; simp
      map_mul' := fun p q => by
        ext
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, MulMemClass.mk_mul_mk]
        calc (p.1 : X) * q.1 * (p.2 * q.2) = p.1 * ((q.1 : X) * p.2) * q.2 := by group
          _ = p.1 * ((p.2 : X) * q.1) * q.2 := by rw [hcomm _ q.1.2 _ p.2.2]
          _ = p.1 * p.2 * (q.1 * q.2) := by group }
  have hinj : Function.Injective f := by
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
    have h1 : (a₁ : X) * b₁ = a₂ * b₂ := congrArg Subtype.val h
    have h2 : (a₂ : X)⁻¹ * a₁ = b₂ * (b₁ : X)⁻¹ := by
      calc (a₂ : X)⁻¹ * a₁ = (a₂ : X)⁻¹ * (a₁ * b₁) * (b₁ : X)⁻¹ := by group
        _ = (a₂ : X)⁻¹ * (a₂ * b₂) * (b₁ : X)⁻¹ := by rw [h1]
        _ = b₂ * (b₁ : X)⁻¹ := by group
    have hmem : (a₂ : X)⁻¹ * a₁ ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem a₂.2) a₁.2, h2 ▸ B.mul_mem b₂.2 (B.inv_mem b₁.2)⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    have ha : a₁ = a₂ := Subtype.ext (by
      have := congrArg ((a₂ : X) * ·) hmem
      simpa using this)
    have hb : b₁ = b₂ := Subtype.ext (by
      rw [ha] at h1
      exact mul_left_cancel h1)
    rw [ha, hb]
  have hsurj : Function.Surjective f := by
    rintro ⟨m, hm⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := hgen m hm
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  exact ⟨(MulEquiv.ofBijective f ⟨hinj, hsurj⟩).symm⟩

end CFSG.LargeExtraspecial.S7
