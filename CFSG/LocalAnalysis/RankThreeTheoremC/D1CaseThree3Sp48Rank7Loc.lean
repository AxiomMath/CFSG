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
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open scoped commutatorElement

variable {X : Type*} [Group X]

theorem le_sup_of_perfect_of_commute {P Q U A₁ A₂ : Subgroup X}
    (hPQ : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) (hU : U ≤ P ⊔ Q) (hperf : ⁅U, U⁆ = U)
    (hA₂ : A₂ ≤ Q) (h1 : ∀ u ∈ U, ∀ p ∈ P, ⁅u, p⁆ ∈ A₁)
    (h2 : ∀ u ∈ U, ∀ q ∈ Q, ⁅u, q⁆ ∈ A₂) : U ≤ A₁ ⊔ A₂ := by
  have hPN : P ≤ Subgroup.normalizer (Q : Set X) := fun p hp =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun q hq =>
      (hPQ p hp q hq).symm)
  refine hperf.symm.le.trans (Subgroup.commutator_le.mpr fun u hu u' hu' => ?_)
  have hu'PQ : u' ∈ P ⊔ Q := hU hu'
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right P Q hPN] at hu'PQ
  obtain ⟨p, hp, q, hq, rfl⟩ := hu'PQ
  have hcomm : p * ⁅u, q⁆ = ⁅u, q⁆ * p := hPQ p hp _ (hA₂ (h2 u hu q hq))
  have e : ⁅u, p * q⁆ = ⁅u, p⁆ * (p * ⁅u, q⁆ * p⁻¹) := by
    simp only [commutatorElement_def]
    group
  have e' : p * ⁅u, q⁆ * p⁻¹ = ⁅u, q⁆ := by rw [hcomm]; group
  rw [e, e']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (h1 u hu p hp))
    (Subgroup.mem_sup_right (h2 u hu q hq))

theorem exists_le_of_commuting_family {ι : Type*} (P : ι → Subgroup X)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, x * y = y * x) {B : Subgroup X}
    (hBD : B ≤ ⨆ i, P i) (hDB : ⨆ i, P i ≤ Subgroup.normalizer (B : Set X)) (hBp : ⁅B, B⁆ = B)
    {W : Subgroup X} (hWB : W ≤ B) (hBW : B ≤ Subgroup.normalizer (W : Set X))
    (hWp : ⁅W, W⁆ = W) (hWs : IsSimpleGroup W) (hWn : ∃ a b : W, a * b ≠ b * a) :
    ∃ i, W ≤ P i := by
  classical
  set D : Subgroup X := ⨆ i, P i with hD
  set Q : ι → Subgroup X := fun i => ⨆ (j : ι) (_ : j ≠ i), P j with hQ
  have hPQ : ∀ i, ∀ p ∈ P i, ∀ q ∈ Q i, p * q = q * p := by
    intro i p hp q hq
    have hQc : Q i ≤ Subgroup.centralizer (P i : Set X) := by
      refine iSup₂_le fun j hj y hy => ?_
      exact Subgroup.mem_centralizer_iff.mpr fun h hh => hcomm i j (Ne.symm hj) h hh y hy
    exact Subgroup.mem_centralizer_iff.mp (hQc hq) p hp
  have hDeq : ∀ i, D = P i ⊔ Q i := by
    intro i
    refine le_antisymm (iSup_le fun j => ?_)
      (sup_le (le_iSup P i) (iSup₂_le fun j _ => le_iSup P j))
    by_cases hji : j = i
    · subst hji
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂ (f := fun (j' : ι) (_ : j' ≠ i) => P j') j hji)
  have hDP : ∀ i, D ≤ Subgroup.normalizer (P i : Set X) := by
    intro i
    refine iSup_le fun j => ?_
    by_cases hji : j = i
    · subst hji
      exact Subgroup.le_normalizer
    · exact fun x hx => Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
        fun h hh => (hcomm i j (Ne.symm hji) h hh x hx))
  have hQle : ∀ i, Q i ≤ D := fun i => iSup₂_le fun j _ => le_iSup P j
  have hDQ : ∀ i, D ≤ Subgroup.normalizer (Q i : Set X) := by
    intro i
    refine iSup_le fun j => ?_
    by_cases hji : j = i
    · subst hji
      exact fun x hx => Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
        fun h hh => (hPQ j x hx h hh).symm)
    · exact (le_iSup₂ (f := fun (j' : ι) (_ : j' ≠ i) => P j') j hji).trans
        Subgroup.le_normalizer
  obtain ⟨i, hi⟩ : ∃ i, ¬ W ≤ Q i := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, b, hab⟩ := hWn
    have haC : D ≤ Subgroup.centralizer ({(a : X)} : Set X) := by
      refine iSup_le fun i x hx => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hPQ i x hx a (hcon i a.2)
    have hbD : (b : X) ∈ D := hBD (hWB b.2)
    have := Subgroup.mem_centralizer_singleton_iff.mp (haC hbD)
    exact hab (Subtype.ext this.symm)
  have hBsplit : B ≤ (B ⊓ P i) ⊔ (B ⊓ Q i) := by
    refine le_sup_of_perfect_of_commute (P := P i) (Q := Q i) (hPQ i) (hBD.trans (hDeq i).le)
      hBp inf_le_right ?_ ?_
    · intro u hu p hp
      refine ⟨?_, ?_⟩
      · have hp' : p ∈ Subgroup.normalizer (B : Set X) := hDB (le_iSup P i hp)
        have h1 : p * u⁻¹ * p⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hp' u⁻¹).mp (B.inv_mem hu)
        have e : ⁅u, p⁆ = u * (p * u⁻¹ * p⁻¹) := by simp only [commutatorElement_def]; group
        rw [e]
        exact B.mul_mem hu h1
      · have hu' : u ∈ Subgroup.normalizer (P i : Set X) := hDP i (hBD hu)
        have h1 : u * p * u⁻¹ ∈ P i := (Subgroup.mem_normalizer_iff.mp hu' p).mp hp
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ h1 ((P i).inv_mem hp)
    · intro u hu q hq
      refine ⟨?_, ?_⟩
      · have hq' : q ∈ Subgroup.normalizer (B : Set X) := hDB (hQle i hq)
        have h1 : q * u⁻¹ * q⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hq' u⁻¹).mp (B.inv_mem hu)
        have e : ⁅u, q⁆ = u * (q * u⁻¹ * q⁻¹) := by simp only [commutatorElement_def]; group
        rw [e]
        exact B.mul_mem hu h1
      · have hu' : u ∈ Subgroup.normalizer (Q i : Set X) := hDQ i (hBD hu)
        have h1 : u * q * u⁻¹ ∈ Q i := (Subgroup.mem_normalizer_iff.mp hu' q).mp hq
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ h1 ((Q i).inv_mem hq)
  have hWsplit : W ≤ (W ⊓ P i) ⊔ (W ⊓ Q i) := by
    refine le_sup_of_perfect_of_commute (P := B ⊓ P i) (Q := B ⊓ Q i)
      (fun p hp q hq => hPQ i p hp.2 q hq.2) (hWB.trans hBsplit) hWp
      (inf_le_inf_right _ hWB) ?_ ?_
    · intro u hu p hp
      refine ⟨?_, ?_⟩
      · have hp' : p ∈ Subgroup.normalizer (W : Set X) := hBW hp.1
        have h1 : p * u⁻¹ * p⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hp' u⁻¹).mp (W.inv_mem hu)
        have e : ⁅u, p⁆ = u * (p * u⁻¹ * p⁻¹) := by simp only [commutatorElement_def]; group
        rw [e]
        exact W.mul_mem hu h1
      · have hu' : u ∈ Subgroup.normalizer (P i : Set X) := hDP i (hBD (hWB hu))
        have h1 : u * p * u⁻¹ ∈ P i := (Subgroup.mem_normalizer_iff.mp hu' p).mp hp.2
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ h1 ((P i).inv_mem hp.2)
    · intro u hu q hq
      refine ⟨?_, ?_⟩
      · have hq' : q ∈ Subgroup.normalizer (W : Set X) := hBW hq.1
        have h1 : q * u⁻¹ * q⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hq' u⁻¹).mp (W.inv_mem hu)
        have e : ⁅u, q⁆ = u * (q * u⁻¹ * q⁻¹) := by simp only [commutatorElement_def]; group
        rw [e]
        exact W.mul_mem hu h1
      · have hu' : u ∈ Subgroup.normalizer (Q i : Set X) := hDQ i (hBD (hWB hu))
        have h1 : u * q * u⁻¹ ∈ Q i := (Subgroup.mem_normalizer_iff.mp hu' q).mp hq.2
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ h1 ((Q i).inv_mem hq.2)
  refine ⟨i, ?_⟩
  have : IsSimpleGroup W := hWs
  have hnorm : ((P i).subgroupOf W).Normal := ⟨fun n hn g => by
    have hg : (g : X) ∈ Subgroup.normalizer (P i : Set X) := hDP i (hBD (hWB g.2))
    have h1 := (Subgroup.mem_normalizer_iff.mp hg (n : X)).mp (Subgroup.mem_subgroupOf.mp hn)
    exact Subgroup.mem_subgroupOf.mpr h1⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((P i).subgroupOf W) with h | h
  · exfalso
    apply hi
    have hbot : W ⊓ P i = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx.1⟩ : W) ∈ (P i).subgroupOf W := Subgroup.mem_subgroupOf.mpr hx.2
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    rw [hbot, bot_sup_eq] at hWsplit
    exact hWsplit.trans inf_le_right
  · intro w hw
    have : (⟨w, hw⟩ : W) ∈ (P i).subgroupOf W := by rw [h]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

theorem le_normalizer_of_commute_blocks {P₁ P₂ V₁ V₂ : Subgroup X}
    (hP : ∀ x ∈ P₁, ∀ y ∈ P₂, x * y = y * x) (hV₁ : V₁ ≤ P₁) (hV₂ : V₂ ≤ P₂)
    (hVc : ∀ a ∈ V₁, ∀ b ∈ V₂, a * b = b * a)
    (hn : P₁ ≤ Subgroup.normalizer ((V₁ ⊔ V₂ : Subgroup X) : Set X))
    (hs : IsSimpleGroup V₂) (hnab : ∃ a b : V₂, a * b ≠ b * a) :
    P₁ ≤ Subgroup.normalizer (V₁ : Set X) := by
  have hcenter : ∀ z ∈ V₂, (∀ y ∈ V₂, y * z = z * y) → z = 1 := by
    intro z hz hzc
    have : IsSimpleGroup V₂ := hs
    have hnorm : (Subgroup.center V₂).Normal := inferInstance
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center V₂) with h | h
    · have hmem : (⟨z, hz⟩ : V₂) ∈ Subgroup.center V₂ :=
        Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hzc g g.2)
      rw [h, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    · obtain ⟨a, b, hab⟩ := hnab
      exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a) hab
  have hV₁N : V₁ ≤ Subgroup.normalizer (V₂ : Set X) := fun a ha =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun b hb =>
      (hVc a ha b hb).symm)
  have key : ∀ g ∈ P₁, ∀ v ∈ V₁, g * v * g⁻¹ ∈ V₁ := by
    intro g hg v hv
    have hw : g * v * g⁻¹ ∈ V₁ ⊔ V₂ :=
      (Subgroup.mem_normalizer_iff.mp (hn hg) v).mp (Subgroup.mem_sup_left hv)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right V₁ V₂ hV₁N] at hw
    obtain ⟨a, ha, b, hb, hab⟩ := hw
    have hab' : a * b = g * v * g⁻¹ := hab
    have hbP : b ∈ P₁ := by
      have e : b = a⁻¹ * (g * v * g⁻¹) := by rw [← hab']; group
      rw [e]
      exact P₁.mul_mem (P₁.inv_mem (hV₁ ha))
        (P₁.mul_mem (P₁.mul_mem hg (hV₁ hv)) (P₁.inv_mem hg))
    have hb1 : b = 1 := hcenter b hb fun y hy => (hP b hbP y (hV₂ hy)).symm
    rw [← hab', hb1, mul_one]
    exact ha
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key g hg h, fun hh => ?_⟩
  have := key g⁻¹ (P₁.inv_mem hg) _ hh
  simpa [mul_assoc] using this

end CFSG.LocalAnalysis.RankThreeTheoremC
