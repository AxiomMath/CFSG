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
public import Mathlib.GroupTheory.IsPerfect
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

namespace CFSG.ComponentClassification.SolMax.SwapP2.ExactAbs

open Subgroup

variable {Γ : Type*} [Group Γ]

@[expose] def conjSub (μ : Γ) (H : Subgroup Γ) : Subgroup Γ :=
  H.map (MulAut.conj μ).toMonoidHom

theorem mem_conjSub {μ x : Γ} {H : Subgroup Γ} : x ∈ conjSub μ H ↔ μ⁻¹ * x * μ ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨μ⁻¹ * x * μ, h, by simp [mul_assoc]⟩

theorem orderOf_conj_eq (μ x : Γ) : orderOf (μ * x * μ⁻¹) = orderOf x :=
  MulEquiv.orderOf_eq (MulAut.conj μ) x

@[expose] def Normalizes (μ : Γ) (P : Subgroup Γ) : Prop := ∀ x, x ∈ P ↔ μ * x * μ⁻¹ ∈ P

theorem Normalizes.inv_conj {μ : Γ} {P : Subgroup Γ} (h : Normalizes μ P) (x : Γ) :
    x ∈ P ↔ μ⁻¹ * x * μ ∈ P := by
  rw [h (μ⁻¹ * x * μ)]
  simp [mul_assoc]

theorem normalizes_of_mem {c : Γ} {P : Subgroup Γ} (hc : c ∈ P) : Normalizes c P := fun x =>
  ⟨fun hx => P.mul_mem (P.mul_mem hc hx) (P.inv_mem hc), fun hx => by
    have := P.mul_mem (P.mul_mem (P.inv_mem hc) hx) hc
    simpa [mul_assoc] using this⟩

theorem eq_of_forall_odd_mem [Finite Γ] {P G : Subgroup Γ} (hP : ⁅P, P⁆ = P) (hG : G ≤ P)
    (h : ∀ g ∈ P, Odd (orderOf g) → g ∈ G) : G = P := by
  classical
  let S : Set P := {g | Odd (orderOf g)}
  let N : Subgroup P := normalClosure S
  have hSG : S ⊆ G.subgroupOf P := by
    intro g hg
    exact h g g.2 (by simpa [Subgroup.orderOf_coe] using (show Odd (orderOf g) from hg))
  have hN : N ≤ G.subgroupOf P := by
    refine (closure_le _).2 ?_
    intro x hx
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    obtain ⟨c, hc⟩ := isConj_iff.1 hax
    have hx' : x = c * a * c⁻¹ := hc.symm
    have : x ∈ S := by
      show Odd (orderOf x)
      rw [hx', orderOf_conj_eq]
      exact ha
    exact hSG this
  have hQ : IsPGroup 2 (P ⧸ N) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, m, hm, hgm⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf g)
      (orderOf_pos g).ne'
    refine ⟨a, ?_⟩
    have hodd : Odd (orderOf (g ^ 2 ^ a)) := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hgm⟩, hgm,
        Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
      exact hm
    have hmem : g ^ 2 ^ a ∈ N := subset_normalClosure hodd
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hmem
  haveI : Group.IsNilpotent (P ⧸ N) := hQ.isNilpotent
  haveI : Group.IsSolvable (P ⧸ N) := inferInstance
  have hperf : commutator (P ⧸ N) = ⊤ := by
    haveI : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hP
    haveI : Group.IsPerfect (P ⧸ N) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    exact Group.IsPerfect.commutator_eq_top
  have htriv : Subsingleton (P ⧸ N) := by
    by_contra hns
    haveI : Nontrivial (P ⧸ N) := not_subsingleton_iff_nontrivial.1 hns
    have := IsSolvable.commutator_lt_top_of_nontrivial (P ⧸ N)
    rw [hperf] at this
    exact lt_irrefl _ this
  have hNtop : N = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    have : (x : P ⧸ N) = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff x).1 this
  refine le_antisymm hG fun x hx => ?_
  have hx' : (⟨x, hx⟩ : P) ∈ G.subgroupOf P := hN (hNtop ▸ Subgroup.mem_top _)
  exact hx'




structure CoreHyp (P : Subgroup Γ) (ν ε : Γ) (E G : Subgroup Γ) : Prop where
  nu2 : ν * ν = 1
  epsP : ε ∈ P
  eps2 : ε * ε = 1
  eps1 : ε ≠ 1
  EP : E ≤ P
  Eperf : ⁅E, E⁆ = E
  Efix : ∀ e ∈ E, ν * e = e * ν
  epsE : ε ∈ E
  GP : G ≤ P
  g1 : ∀ g ∈ P, ν * g = g * ν → Odd (orderOf g) → g ∈ G
  g2 : ∀ g ∈ P, (ε * ν) * g = g * (ε * ν) → Odd (orderOf g) → g ∈ G

theorem conj_comm_iff (μ ν g : Γ) : (μ * ν * μ⁻¹) * (μ * g * μ⁻¹) = (μ * g * μ⁻¹) * (μ * ν * μ⁻¹) ↔
    ν * g = g * ν := by
  have e1 : (μ * ν * μ⁻¹) * (μ * g * μ⁻¹) = μ * (ν * g) * μ⁻¹ := by group
  have e2 : (μ * g * μ⁻¹) * (μ * ν * μ⁻¹) = μ * (g * ν) * μ⁻¹ := by group
  rw [e1, e2]
  constructor
  · intro h
    have := mul_left_cancel (mul_right_cancel h)
    exact this
  · intro h; rw [h]

theorem CoreHyp.conj {P : Subgroup Γ} {ν ε : Γ} {E G : Subgroup Γ} (h : CoreHyp P ν ε E G)
    {μ : Γ} (hμ : Normalizes μ P) :
    CoreHyp P (μ * ν * μ⁻¹) (μ * ε * μ⁻¹) (conjSub μ E) (conjSub μ G) := by
  have hmemP : ∀ {K : Subgroup Γ}, K ≤ P → ∀ x ∈ conjSub μ K, x ∈ P := by
    intro K hK x hx
    rw [mem_conjSub] at hx
    exact (hμ.inv_conj x).2 (hK hx)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc μ * ν * μ⁻¹ * (μ * ν * μ⁻¹) = μ * (ν * ν) * μ⁻¹ := by group
      _ = 1 := by rw [h.nu2]; group
  · exact (hμ ε).1 h.epsP
  · calc μ * ε * μ⁻¹ * (μ * ε * μ⁻¹) = μ * (ε * ε) * μ⁻¹ := by group
      _ = 1 := by rw [h.eps2]; group
  · intro h1
    apply h.eps1
    have : μ * ε * μ⁻¹ = μ * 1 * μ⁻¹ := by rw [h1]; group
    simpa using this
  · exact fun x hx => hmemP h.EP x hx
  · unfold conjSub
    rw [← Subgroup.map_commutator, h.Eperf]
  · intro e he
    rw [mem_conjSub] at he
    have := h.Efix _ he
    have h3 : (μ * ν * μ⁻¹) * e = e * (μ * ν * μ⁻¹) := by
      have e1 : μ * ν * μ⁻¹ * e = μ * (ν * (μ⁻¹ * e * μ)) * μ⁻¹ := by group
      have e2 : e * (μ * ν * μ⁻¹) = μ * ((μ⁻¹ * e * μ) * ν) * μ⁻¹ := by group
      rw [e1, e2, this]
    exact h3
  · exact ⟨ε, h.epsE, by simp⟩
  · exact fun x hx => hmemP h.GP x hx
  · intro g hg hcomm hodd
    rw [mem_conjSub]
    have hg' : μ⁻¹ * g * μ ∈ P := (hμ.inv_conj g).1 hg
    have hg1 : μ * (μ⁻¹ * g * μ) * μ⁻¹ = g := by group
    have hcomm' : ν * (μ⁻¹ * g * μ) = (μ⁻¹ * g * μ) * ν := by
      rw [← conj_comm_iff μ, hg1]; exact hcomm
    refine h.g1 _ hg' hcomm' ?_
    have := orderOf_conj_eq μ⁻¹ g
    rw [inv_inv] at this
    rw [this]; exact hodd
  · intro g hg hcomm hodd
    rw [mem_conjSub]
    have hg' : μ⁻¹ * g * μ ∈ P := (hμ.inv_conj g).1 hg
    have hg1 : μ * (μ⁻¹ * g * μ) * μ⁻¹ = g := by group
    have e : (μ * ε * μ⁻¹) * (μ * ν * μ⁻¹) = μ * (ε * ν) * μ⁻¹ := by group
    rw [e] at hcomm
    have hcomm' : (ε * ν) * (μ⁻¹ * g * μ) = (μ⁻¹ * g * μ) * (ε * ν) := by
      rw [← conj_comm_iff μ, hg1]; exact hcomm
    refine h.g2 _ hg' hcomm' ?_
    have := orderOf_conj_eq μ⁻¹ g
    rw [inv_inv] at this
    rw [this]; exact hodd

theorem eq_of_conjSub_eq {P G : Subgroup Γ} {μ : Γ} (hμ : Normalizes μ P) (hG : G ≤ P)
    (h : conjSub μ G = P) : G = P := by
  refine le_antisymm hG fun x hx => ?_
  have h1 : μ * x * μ⁻¹ ∈ P := (hμ x).1 hx
  rw [← h, mem_conjSub] at h1
  simpa [mul_assoc] using h1


@[expose] def RepGood (P : Subgroup Γ) (ν : Γ) : Prop :=
  ∃ (C X : Subgroup Γ) (εs : Set Γ), C ≤ P ∧ (∀ g ∈ C, ν * g = g * ν) ∧
    (∀ g ∈ P, ν * g = g * ν → g ∈ C) ∧ X ≤ C ∧ ⁅C, C⁆ ≤ X ∧
    (∀ e ∈ X, e * e = 1 → e ≠ 1 → ∃ c ∈ C, ∃ ε ∈ εs, c * e * c⁻¹ = ε) ∧
    ∀ ε ∈ εs, P ≤ Subgroup.closure ({g | g ∈ P ∧ ν * g = g * ν ∧ Odd (orderOf g)} ∪
      {g | g ∈ P ∧ (ε * ν) * g = g * (ε * ν) ∧ Odd (orderOf g)})

@[expose] def FCHyp (P N : Subgroup Γ) : Prop :=
  ∃ R : Set Γ, (∀ ρ ∈ R, ρ ∈ N ∧ ρ * ρ = 1 ∧ RepGood P ρ) ∧
    ∀ x ∈ N, x * x = 1 → x = 1 ∨ ∃ μ ∈ N, ∃ ρ ∈ R, μ * x * μ⁻¹ = ρ

theorem fc_of_hyp [Finite Γ] {P N : Subgroup Γ} (hPN : P ≤ N) (hnorm : ∀ μ ∈ N, Normalizes μ P)
    (hPperf : ⁅P, P⁆ = P) (hF : FCHyp P N) {ν : Γ} (hν : ν ∈ N) {ε : Γ} {E G : Subgroup Γ}
    (h : CoreHyp P ν ε E G) : G = P := by
  obtain ⟨R, hR, hcover⟩ := hF
  rcases hcover ν hν h.nu2 with rfl | ⟨μ, hμ, ρ, hρ, hconj⟩
  · exact eq_of_forall_odd_mem hPperf h.GP (fun g hg ho => h.g1 g hg (by simp) ho)
  · obtain ⟨-, -, C, X, εs, hCP, hCν, hCmax, hXC, hCC, hεcov, hgen⟩ := hR ρ hρ
    have h1 := h.conj (hnorm μ hμ)
    rw [hconj] at h1
    have hEX : conjSub μ E ≤ X := by
      have hEC : conjSub μ E ≤ C := fun e he => hCmax e (h1.EP he) (h1.Efix e he)
      calc conjSub μ E = ⁅conjSub μ E, conjSub μ E⁆ := h1.Eperf.symm
        _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hEC hEC
        _ ≤ X := hCC
    obtain ⟨c, hcC, ε2, hε2, hce⟩ := hεcov _ (hEX h1.epsE) h1.eps2 h1.eps1
    have hcP : c ∈ P := hCP hcC
    have h2 := h1.conj (normalizes_of_mem hcP)
    have hcρ : c * ρ * c⁻¹ = ρ := by
      have := hCν c hcC
      calc c * ρ * c⁻¹ = (ρ * c) * c⁻¹ := by rw [this]
        _ = ρ := by group
    rw [hcρ, hce] at h2
    have hsub : ({g | g ∈ P ∧ ρ * g = g * ρ ∧ Odd (orderOf g)} ∪
        {g | g ∈ P ∧ (ε2 * ρ) * g = g * (ε2 * ρ) ∧ Odd (orderOf g)} : Set Γ) ⊆
        conjSub c (conjSub μ G) := by
      rintro g (⟨hgP, hgc, hgo⟩ | ⟨hgP, hgc, hgo⟩)
      · exact h2.g1 g hgP hgc hgo
      · exact h2.g2 g hgP hgc hgo
    have hPle : P ≤ conjSub c (conjSub μ G) :=
      (hgen ε2 hε2).trans ((Subgroup.closure_le _).2 hsub)
    have h3 : conjSub c (conjSub μ G) = P := le_antisymm h2.GP hPle
    have h4 : conjSub μ G = P := eq_of_conjSub_eq (normalizes_of_mem hcP) h1.GP h3
    exact eq_of_conjSub_eq (hnorm μ hμ) h.GP h4


theorem commutator_eq_of_equiv {S : Type*} [Group S] (P : Subgroup Γ) (e : S ≃* P)
    (h : commutator S = ⊤) : ⁅P, P⁆ = P := by
  let φ : S →* Γ := P.subtype.comp e.toMonoidHom
  have hr : (⊤ : Subgroup S).map φ = P := by
    ext x
    constructor
    · rintro ⟨s, -, rfl⟩
      exact (e s).2
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, trivial, by simp [φ]⟩
  have h' : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = (⊤ : Subgroup S) := h
  calc ⁅P, P⁆ = ⁅(⊤ : Subgroup S).map φ, (⊤ : Subgroup S).map φ⁆ := by rw [hr]
    _ = (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆).map φ := (Subgroup.map_commutator _ _ _).symm
    _ = P := by rw [h', hr]

@[expose] def CoreAt (S : Type*) [Group S] (τ : MulAut S) : Prop :=
  ∀ ε : S, ε * ε = 1 → ε ≠ 1 → ∀ E : Subgroup S, ⁅E, E⁆ = E →
    (∀ e ∈ E, τ e = e) → ε ∈ E → ∀ Ĝ : Subgroup S,
    (∀ g : S, τ g = g → Odd (orderOf g) → g ∈ Ĝ) →
    (∀ g : S, (MulAut.conj ε * τ) g = g → Odd (orderOf g) → g ∈ Ĝ) → Ĝ = ⊤

@[expose] def CoreStmt (S : Type*) [Group S] : Prop :=
  ∀ (τ : MulAut S), τ * τ = 1 → CoreAt S τ

theorem coreAt_of_conj {S : Type*} [Group S] (τ σ : MulAut S) (h : CoreAt S (σ * τ * σ⁻¹)) :
    CoreAt S τ := by
  intro ε hε2 hε1 E hEperf hEfix hεE G hG1 hG2
  have hσ : ∀ x : S, σ⁻¹ (σ x) = x := fun x => by simp
  have hσ' : ∀ x : S, σ (σ⁻¹ x) = x := fun x => by simp
  have hconj : ∀ g : S, (MulAut.conj (σ ε) * (σ * τ * σ⁻¹)) (σ g) = σ ((MulAut.conj ε * τ) g) := by
    intro g
    simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, hσ]
  have hG' : G.map σ.toMonoidHom = ⊤ := by
    refine h (σ ε) ?_ ?_ (E.map σ.toMonoidHom) ?_ ?_ ?_ (G.map σ.toMonoidHom) ?_ ?_
    · rw [← map_mul, hε2, map_one]
    · intro h1
      apply hε1
      exact σ.injective (by rw [h1, map_one])
    · rw [← Subgroup.map_commutator, hEperf]
    · rintro _ ⟨x, hx, rfl⟩
      simp [MulAut.mul_apply, hEfix x hx]
    · exact ⟨ε, hεE, rfl⟩
    · intro g' hg' hodd
      refine ⟨σ⁻¹ g', hG1 _ ?_ ?_, by simp⟩
      · have h1 : σ (τ (σ⁻¹ g')) = g' := by simpa [MulAut.mul_apply] using hg'
        have h2 := congrArg (fun y => σ⁻¹ y) h1
        simp only [hσ] at h2
        exact h2
      · rw [show orderOf (σ⁻¹ g') = orderOf g' from MulEquiv.orderOf_eq σ⁻¹ g']
        exact hodd
    · intro g' hg' hodd
      refine ⟨σ⁻¹ g', hG2 _ ?_ ?_, by simp⟩
      · have h1 := hconj (σ⁻¹ g')
        rw [hσ'] at h1
        rw [h1] at hg'
        exact σ.injective (by simpa using hg')
      · rw [show orderOf (σ⁻¹ g') = orderOf g' from MulEquiv.orderOf_eq σ⁻¹ g']
        exact hodd
  refine eq_top_iff.2 fun x _ => ?_
  have : σ x ∈ G.map σ.toMonoidHom := hG' ▸ Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := this
  have : y = x := σ.injective hyx
  rwa [this] at hy

theorem coreAt_of_induced {S : Type*} [Group S] {Γ : Type*} [Group Γ] [Finite Γ]
    (P N : Subgroup Γ) (e : S ≃* P) (hPN : P ≤ N) (hnorm : ∀ μ ∈ N, Normalizes μ P)
    (hPperf : ⁅P, P⁆ = P) (hcent : ∀ x ∈ N, (∀ p ∈ P, x * p = p * x) → x = 1)
    (τ : MulAut S) (hτ : τ * τ = 1)
    (hAut : ∃ ν ∈ N, ∀ s : S, ((e (τ s) : P) : Γ) = ν * (e s : Γ) * ν⁻¹)
    (hF : FCHyp P N) : CoreAt S τ := by
  intro ε hε2 hε1 E hEperf hEfix hεE G hG1 hG2
  obtain ⟨ν, hνN, hν⟩ := hAut
  let φ : S →* Γ := P.subtype.comp e.toMonoidHom
  have hφ : Function.Injective φ := by
    intro a b hab
    have : e a = e b := Subtype.ext hab
    exact e.injective this
  have hφP : ∀ s, φ s ∈ P := fun s => (e s).2
  have hφapp : ∀ s, φ s = ((e s : P) : Γ) := fun s => rfl
  have hν' : ∀ s, φ (τ s) = ν * φ s * ν⁻¹ := fun s => hν s
  have hnu2 : ν * ν = 1 := by
    have hcomm : ∀ p ∈ P, (ν * ν) * p = p * (ν * ν) := by
      intro p hp
      obtain ⟨s, rfl⟩ : ∃ s, φ s = p := ⟨e.symm ⟨p, hp⟩, by simp [φ]⟩
      have h1 : φ (τ (τ s)) = ν * (ν * φ s * ν⁻¹) * ν⁻¹ := by rw [hν', hν']
      have h2 : τ (τ s) = s := by
        have := congrArg (fun f : MulAut S => f s) hτ
        simpa using this
      rw [h2] at h1
      have : (ν * ν) * φ s * (ν * ν)⁻¹ = φ s := by
        have e1 : ν * (ν * φ s * ν⁻¹) * ν⁻¹ = (ν * ν) * φ s * (ν * ν)⁻¹ := by group
        rw [← e1, ← h1]
      calc (ν * ν) * φ s = ((ν * ν) * φ s * (ν * ν)⁻¹) * (ν * ν) := by group
        _ = φ s * (ν * ν) := by rw [this]
    exact hcent _ (N.mul_mem hνN hνN) hcomm
  have hexists : ∀ g ∈ P, ∃ s, φ s = g := fun g hg => ⟨e.symm ⟨g, hg⟩, by simp [φ]⟩
  have hodd : ∀ s : S, orderOf (φ s) = orderOf s := fun s => orderOf_injective φ hφ s
  have hcore : CoreHyp P ν (φ ε) (E.map φ) (G.map φ) := by
    refine ⟨hnu2, hφP ε, by rw [← map_mul, hε2, map_one], fun h => hε1 (hφ (by rw [h, map_one])),
      ?_, by rw [← Subgroup.map_commutator, hEperf], ?_, ⟨ε, hεE, rfl⟩, ?_, ?_, ?_⟩
    · rintro x ⟨s, hs, rfl⟩; exact hφP s
    · rintro x ⟨s, hs, rfl⟩
      have h1 := hν' s
      rw [hEfix s hs] at h1
      calc ν * φ s = (ν * φ s * ν⁻¹) * ν := by group
        _ = φ s * ν := by rw [← h1]
    · rintro x ⟨s, hs, rfl⟩; exact hφP s
    · intro g hg hcomm ho
      obtain ⟨s, rfl⟩ := hexists g hg
      have hτs : τ s = s := by
        apply hφ
        rw [hν']
        calc ν * φ s * ν⁻¹ = (φ s * ν) * ν⁻¹ := by rw [hcomm]
          _ = φ s := by group
      exact ⟨s, hG1 s hτs (by rwa [← hodd s]), rfl⟩
    · intro g hg hcomm ho
      obtain ⟨s, rfl⟩ := hexists g hg
      have hs' : (MulAut.conj ε * τ) s = s := by
        apply hφ
        have e1 : φ ((MulAut.conj ε * τ) s) = φ ε * (ν * φ s * ν⁻¹) * (φ ε)⁻¹ := by
          simp [MulAut.mul_apply, MulAut.conj_apply, hν']
        rw [e1]
        calc φ ε * (ν * φ s * ν⁻¹) * (φ ε)⁻¹ = ((φ ε * ν) * φ s) * (φ ε * ν)⁻¹ := by group
          _ = (φ s * (φ ε * ν)) * (φ ε * ν)⁻¹ := by rw [hcomm]
          _ = φ s := by group
      exact ⟨s, hG2 s hs' (by rwa [← hodd s]), rfl⟩
  have hGP : G.map φ = P := fc_of_hyp hPN hnorm hPperf hF hνN hcore
  have hrange : (⊤ : Subgroup S).map φ = P := by
    ext x
    constructor
    · rintro ⟨s, -, rfl⟩; exact hφP s
    · intro hx
      obtain ⟨s, rfl⟩ := hexists x hx
      exact ⟨s, trivial, rfl⟩
  exact Subgroup.map_injective hφ (hGP.trans hrange.symm)

theorem coreStmt_of_perm {S : Type*} [Group S] {Γ : Type*} [Group Γ] [Finite Γ]
    (P N : Subgroup Γ) (e : S ≃* P) (hPN : P ≤ N) (hnorm : ∀ μ ∈ N, Normalizes μ P)
    (hPperf : ⁅P, P⁆ = P) (hcent : ∀ x ∈ N, (∀ p ∈ P, x * p = p * x) → x = 1)
    (hAut : ∀ τ : MulAut S, τ * τ = 1 → ∃ σ : MulAut S, ∃ ν ∈ N,
      ∀ s : S, ((e ((σ * τ * σ⁻¹) s) : P) : Γ) = ν * (e s : Γ) * ν⁻¹)
    (hF : FCHyp P N) : CoreStmt S := by
  intro τ hτ
  obtain ⟨σ, hσ⟩ := hAut τ hτ
  refine coreAt_of_conj τ σ (coreAt_of_induced P N e hPN hnorm hPperf hcent (σ * τ * σ⁻¹) ?_ hσ hF)
  calc σ * τ * σ⁻¹ * (σ * τ * σ⁻¹) = σ * (τ * τ) * σ⁻¹ := by group
    _ = 1 := by rw [hτ]; group

end CFSG.ComponentClassification.SolMax.SwapP2.ExactAbs
