module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

theorem normal_isPGroup_perm_eq_bot {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 5 ≤ Fintype.card α) (Q : Subgroup (Perm α)) [Q.Normal] (hQ : IsPGroup 2 Q) :
    Q = ⊥ := by
  by_contra hne
  have hnt : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hne
  have hle := alternatingGroup_le_of_normal (α := α) (by rwa [Nat.card_eq_fintype_card]) hnt
  have hdvd : Nat.card (alternatingGroup α) ∣ Nat.card Q := Subgroup.card_dvd_of_le hle
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hα2 : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have h2 := two_mul_nat_card_alternatingGroup (α := α)
  rw [Nat.card_eq_fintype_card (α := Perm α), Fintype.card_perm] at h2
  have h3 : 3 ∣ Nat.factorial (Fintype.card α) := Nat.dvd_factorial (by norm_num) (by omega)
  have h4 : 3 ∣ Nat.card (alternatingGroup α) := by
    have : 3 ∣ 2 * Nat.card (alternatingGroup α) := by rwa [h2]
    exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this
  have h5 : 3 ∣ 2 ^ k := hk ▸ h4.trans hdvd
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h5
  omega

theorem normal_isPGroup_perm_three_eq_bot (Q : Subgroup (Perm (Fin 3))) [hQn : Q.Normal]
    (hQ : IsPGroup 2 Q) : Q = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro q hq
  have hord : ∀ g : Perm (Fin 3), g ∈ Q → g ^ 2 = 1 := by
    intro g hg
    obtain ⟨k, hk⟩ := hQ ⟨g, hg⟩
    have hk' : g ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hcase : ∀ g : Perm (Fin 3), g ^ 2 = 1 ∨ g ^ 3 = 1 := by decide
    have key : ∀ (g : Perm (Fin 3)) (k : ℕ), g ^ (2 ^ k) = 1 → g ^ 2 = 1 := by
      intro g k hk
      rcases hcase g with h | h
      · exact h
      · have h3 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h
        have h2k : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
        have hco : Nat.Coprime (orderOf g) (2 ^ k) :=
          Nat.Coprime.coprime_dvd_left h3 (Nat.Coprime.pow_right k (by norm_num))
        have h1 : orderOf g = 1 := Nat.Coprime.eq_one_of_dvd hco h2k
        have : g = 1 := orderOf_eq_one_iff.1 h1
        rw [this]; simp
    exact key g k hk'
  by_contra hq1
  have hq2 := hord q hq
  have hconj : ∀ g : Perm (Fin 3), g * q * g⁻¹ ∈ Q := fun g => hQn.conj_mem q hq g
  have hall : ∀ q : Perm (Fin 3), q ≠ 1 → q ^ 2 = 1 →
      (∃ g : Perm (Fin 3), q * (g * q * g⁻¹) ≠ 1 ∧ (q * (g * q * g⁻¹)) ^ 2 ≠ 1) := by
    decide
  obtain ⟨g, hg1, hg2⟩ := hall q hq1 hq2
  exact hg2 (hord _ (Q.mul_mem hq (hconj g)))

theorem normal_isPGroup_perm_fin_eq_bot {m : ℕ} (hm : m = 3 ∨ 5 ≤ m) (Q : Subgroup (Perm (Fin m)))
    [Q.Normal] (hQ : IsPGroup 2 Q) : Q = ⊥ := by
  rcases hm with rfl | hm
  · exact normal_isPGroup_perm_three_eq_bot Q hQ
  · exact normal_isPGroup_perm_eq_bot (by simpa using hm) Q hQ

theorem pCore_eq_ker_of_perm {N : Type*} [Group N] [Finite N] {m : ℕ} (hm : m = 3 ∨ 5 ≤ m)
    (ρ : N →* Perm (Fin m)) (hρ : Function.Surjective ρ) (hker : IsPGroup 2 ρ.ker) :
    CFSG.pCore 2 N = ρ.ker := by
  apply le_antisymm
  · intro x hx
    have hnorm : ((CFSG.pCore 2 N).map ρ).Normal :=
      Subgroup.Normal.map inferInstance ρ hρ
    have hp : IsPGroup 2 ((CFSG.pCore 2 N).map ρ) := CFSG.pCore_isPGroup.map ρ
    have hbot := normal_isPGroup_perm_fin_eq_bot hm _ hp
    have : ρ x ∈ (CFSG.pCore 2 N).map ρ := ⟨x, hx, rfl⟩
    rw [hbot] at this
    simpa using this
  · exact le_sSup ⟨inferInstance, hker⟩

noncomputable def quotientPCorePerm {N : Type*} [Group N] [Finite N] {m : ℕ}
    (hm : m = 3 ∨ 5 ≤ m) (ρ : N →* Perm (Fin m)) (hρ : Function.Surjective ρ)
    (hker : IsPGroup 2 ρ.ker) : N ⧸ CFSG.pCore 2 N ≃* Perm (Fin m) :=
  (QuotientGroup.quotientMulEquivOfEq (pCore_eq_ker_of_perm hm ρ hρ hker)).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)

theorem pCore_eq_ker_of_pCore_eq_bot {N M : Type*} [Group N] [Group M]
    (hM : CFSG.pCore 2 M = ⊥) (ρ : N →* M) (hρ : Function.Surjective ρ)
    (hker : IsPGroup 2 ρ.ker) : CFSG.pCore 2 N = ρ.ker := by
  apply le_antisymm
  · intro x hx
    have hnorm : ((CFSG.pCore 2 N).map ρ).Normal :=
      Subgroup.Normal.map inferInstance ρ hρ
    have hp : IsPGroup 2 ((CFSG.pCore 2 N).map ρ) := CFSG.pCore_isPGroup.map ρ
    have hle : (CFSG.pCore 2 N).map ρ ≤ CFSG.pCore 2 M := le_sSup ⟨hnorm, hp⟩
    rw [hM] at hle
    have : ρ x ∈ (CFSG.pCore 2 N).map ρ := ⟨x, hx, rfl⟩
    simpa using hle this
  · exact le_sSup ⟨inferInstance, hker⟩

theorem pCore_perm_eq_bot {m : ℕ} (hm : m = 1 ∨ m = 3 ∨ 5 ≤ m) :
    CFSG.pCore 2 (Perm (Fin m)) = ⊥ := by
  rcases hm with rfl | hm
  · exact Subsingleton.elim _ _
  · exact normal_isPGroup_perm_fin_eq_bot hm _ CFSG.pCore_isPGroup

theorem pCore_prod_eq_bot {A B : Type*} [Group A] [Group B] (hA : CFSG.pCore 2 A = ⊥)
    (hB : CFSG.pCore 2 B = ⊥) : CFSG.pCore 2 (A × B) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hfs : Function.Surjective (MonoidHom.fst A B) := fun a => ⟨(a, 1), rfl⟩
  have hss : Function.Surjective (MonoidHom.snd A B) := fun b => ⟨(1, b), rfl⟩
  have h1 : (CFSG.pCore 2 (A × B)).map (MonoidHom.fst A B) ≤ CFSG.pCore 2 A :=
    le_sSup ⟨Subgroup.Normal.map inferInstance _ hfs, CFSG.pCore_isPGroup.map _⟩
  have h2 : (CFSG.pCore 2 (A × B)).map (MonoidHom.snd A B) ≤ CFSG.pCore 2 B :=
    le_sSup ⟨Subgroup.Normal.map inferInstance _ hss, CFSG.pCore_isPGroup.map _⟩
  rw [hA] at h1
  rw [hB] at h2
  have e1 : x.1 = 1 := by
    have : x.1 ∈ (CFSG.pCore 2 (A × B)).map (MonoidHom.fst A B) := ⟨x, hx, rfl⟩
    simpa using h1 this
  have e2 : x.2 = 1 := by
    have : x.2 ∈ (CFSG.pCore 2 (A × B)).map (MonoidHom.snd A B) := ⟨x, hx, rfl⟩
    simpa using h2 this
  exact Prod.ext e1 e2

@[expose] noncomputable def quotientPCoreOfKer {N M : Type*} [Group N] [Group M]
    (hM : CFSG.pCore 2 M = ⊥) (ρ : N →* M) (hρ : Function.Surjective ρ)
    (hker : IsPGroup 2 ρ.ker) : N ⧸ CFSG.pCore 2 N ≃* M :=
  (QuotientGroup.quotientMulEquivOfEq (pCore_eq_ker_of_pCore_eq_bot hM ρ hρ hker)).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
