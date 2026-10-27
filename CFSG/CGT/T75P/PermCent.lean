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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.CGT.T75P

open Equiv Equiv.Perm

private theorem card_fix_conj (x t : Perm (Fin 9)) :
    (Finset.univ.filter (fun i : Fin 9 => (x * t * x⁻¹) i = i)).card =
      (Finset.univ.filter (fun i : Fin 9 => t i = i)).card := by
  refine Finset.card_bij (fun i _ => x⁻¹ i) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have := congrArg (fun j => x⁻¹ j) hi
    simpa [Perm.mul_apply] using this
  · intro a _ b _ h
    simpa using h
  · intro j hj
    refine ⟨x j, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    simp [Perm.mul_apply, hj]

private theorem eight_dvd_sum_fix (T' : Subgroup (Perm (Fin 9))) [Fintype T']
    (hcard : Nat.card T' = 8) :
    8 ∣ ∑ g : T', (Finset.univ.filter (fun i : Fin 9 => (g : Perm (Fin 9)) i = i)).card := by
  classical
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group T' (Fin 9)
  have hc : Fintype.card T' = 8 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have hfix : ∀ g : T', Fintype.card (MulAction.fixedBy (Fin 9) g) =
      (Finset.univ.filter (fun i : Fin 9 => (g : Perm (Fin 9)) i = i)).card := by
    intro g
    exact Fintype.card_of_subtype _ (fun i => by
      simp [MulAction.mem_fixedBy, Subgroup.smul_def, Perm.smul_def])
  simp only [hfix, hc] at hB
  exact Dvd.intro_left _ hB.symm

theorem perm_centralizer_trivial (X T' : Subgroup (Perm (Fin 9))) (hTX : T' ≤ X)
    (hcard : Nat.card T' = 8) (hab : ∀ a ∈ T', ∀ b ∈ T', a * b = b * a)
    (htrans : ∀ a ∈ T', a ≠ 1 → ∀ b ∈ T', b ≠ 1 → ∃ x ∈ X, x * a * x⁻¹ = b)
    {π : Perm (Fin 9)} (hπ : ∀ x ∈ X, π * x = x * π) : π = 1 := by
  classical
  have : Fintype T' := Fintype.ofFinite _
  have hcardF : Fintype.card T' = 8 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have hne : T' ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  obtain ⟨⟨t₀, ht₀⟩, ht₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have ht₀1' : t₀ ≠ 1 := fun h => ht₀1 (Subtype.ext h)
  set φ := (Finset.univ.filter (fun i : Fin 9 => t₀ i = i)).card with hφ
  have hφconst : ∀ g : T', (g : Perm (Fin 9)) ≠ 1 →
      (Finset.univ.filter (fun i : Fin 9 => (g : Perm (Fin 9)) i = i)).card = φ := by
    intro g hg
    obtain ⟨x, hx, hxg⟩ := htrans t₀ ht₀ ht₀1' (g : Perm (Fin 9)) g.2 hg
    rw [← hxg, card_fix_conj]
  have hsum : ∑ g : T', (Finset.univ.filter (fun i : Fin 9 => (g : Perm (Fin 9)) i = i)).card =
      9 + 7 * φ := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : T'))]
    have h1 : (Finset.univ.filter
        (fun i : Fin 9 => ((1 : T') : Perm (Fin 9)) i = i)).card = 9 := by
      simp
    have h2 : ∑ g ∈ Finset.univ.erase (1 : T'),
        (Finset.univ.filter (fun i : Fin 9 => (g : Perm (Fin 9)) i = i)).card = 7 * φ := by
      rw [Finset.sum_congr rfl (fun g hg => hφconst g (by
        intro h
        exact (Finset.ne_of_mem_erase hg) (Subtype.ext h)))]
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        hcardF, smul_eq_mul]
    rw [h1, h2]
  have hdvd := eight_dvd_sum_fix T' hcard
  rw [hsum] at hdvd
  have hφ9 : φ < 9 := by
    have hle : φ ≤ 9 := by
      calc φ ≤ (Finset.univ : Finset (Fin 9)).card := Finset.card_le_univ _
        _ = 9 := by simp
    rcases Nat.lt_or_ge φ 9 with h | h
    · exact h
    · exfalso
      have heq : Finset.univ.filter (fun i : Fin 9 => t₀ i = i) = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [← hφ]
        simp only [Fintype.card_fin]
        omega
      apply ht₀1'
      refine Equiv.ext fun i => ?_
      have : i ∈ Finset.univ.filter (fun i : Fin 9 => t₀ i = i) := by
        rw [heq]; exact Finset.mem_univ i
      exact (Finset.mem_filter.1 this).2
  have hφ1 : φ = 1 := by
    obtain ⟨k, hk⟩ := hdvd
    omega
  obtain ⟨p₀, hp₀⟩ := Finset.card_eq_one.1 (hφ.symm.trans hφ1)
  have hp₀fix : t₀ p₀ = p₀ := by
    have : p₀ ∈ Finset.univ.filter (fun i : Fin 9 => t₀ i = i) := by rw [hp₀]; simp
    exact (Finset.mem_filter.1 this).2
  have hfix₀ : ∀ i, t₀ i = i → i = p₀ := by
    intro i hi
    have : i ∈ Finset.univ.filter (fun i : Fin 9 => t₀ i = i) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩
    rw [hp₀] at this
    exact Finset.mem_singleton.1 this
  have hTp₀ : ∀ t ∈ T', t p₀ = p₀ := by
    intro t ht
    apply hfix₀
    have := congrArg (fun f : Perm (Fin 9) => f p₀) (hab t ht t₀ ht₀)
    simp only [Perm.mul_apply, hp₀fix] at this
    exact this.symm
  have hfree : ∀ t ∈ T', ∀ i, i ≠ p₀ → t i = i → t = 1 := by
    intro t ht i hi hti
    by_contra ht1
    have hcnt : (Finset.univ.filter (fun i : Fin 9 => t i = i)).card = φ :=
      hφconst ⟨t, ht⟩ ht1
    rw [hφ1] at hcnt
    obtain ⟨q, hq⟩ := Finset.card_eq_one.1 hcnt
    have h1 : i ∈ Finset.univ.filter (fun i : Fin 9 => t i = i) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hti⟩
    have h2 : p₀ ∈ Finset.univ.filter (fun i : Fin 9 => t i = i) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hTp₀ t ht⟩
    rw [hq] at h1 h2
    exact hi ((Finset.mem_singleton.1 h1).trans (Finset.mem_singleton.1 h2).symm)
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin 9, i₀ ≠ p₀ := by
    by_cases h : p₀ = 0
    · exact ⟨1, by rw [h]; decide⟩
    · exact ⟨0, fun h' => h h'.symm⟩
  have hne_p : ∀ g ∈ T', g i₀ ≠ p₀ := fun g hg h =>
    hi₀ (Equiv.injective g (h.trans (hTp₀ g hg).symm))
  have hreg : ∀ j : Fin 9, j ≠ p₀ → ∃ g : Perm (Fin 9), g ∈ T' ∧ g i₀ = j := by
    let f : T' → {i : Fin 9 // i ≠ p₀} := fun g => ⟨(g : Perm (Fin 9)) i₀, hne_p g g.2⟩
    have hinj : Function.Injective f := by
      intro g g' h
      have h1 : (g : Perm (Fin 9)) i₀ = (g' : Perm (Fin 9)) i₀ := congrArg Subtype.val h
      have h2 : ((g⁻¹ * g' : T') : Perm (Fin 9)) i₀ = i₀ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply]
        rw [← h1]
        simp
      have h3 := hfree _ (g⁻¹ * g').2 i₀ hi₀ h2
      have : g⁻¹ * g' = 1 := Subtype.ext h3
      exact inv_mul_eq_one.1 this
    have hcardsub : Fintype.card {i : Fin 9 // i ≠ p₀} = 8 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
      simp
    have hbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, by rw [hcardF, hcardsub]⟩
    intro j hj
    obtain ⟨g, hg⟩ := hbij.2 ⟨j, hj⟩
    exact ⟨(g : Perm (Fin 9)), g.2, congrArg Subtype.val hg⟩
  have hπp₀ : π p₀ = p₀ := by
    apply hfix₀
    have := congrArg (fun f : Perm (Fin 9) => f p₀) (hπ t₀ (hTX ht₀))
    simp only [Perm.mul_apply, hp₀fix] at this
    exact this.symm
  have hπi₀ : π i₀ ≠ p₀ := fun h => hi₀ (Equiv.injective π (h.trans hπp₀.symm))
  obtain ⟨τ, hτ, hτi₀⟩ := hreg (π i₀) hπi₀
  have hπτ : π = τ := by
    refine Equiv.ext fun i => ?_
    by_cases hi : i = p₀
    · rw [hi, hπp₀, hTp₀ τ hτ]
    · obtain ⟨g, hg, hgi⟩ := hreg i hi
      have h1 : π (g i₀) = g (π i₀) := by
        have := congrArg (fun f : Perm (Fin 9) => f i₀) (hπ g (hTX hg))
        simpa [Perm.mul_apply] using this
      calc π i = π (g i₀) := by rw [hgi]
        _ = g (π i₀) := h1
        _ = g (τ i₀) := by rw [hτi₀]
        _ = τ (g i₀) := by
          have := congrArg (fun f : Perm (Fin 9) => f i₀) (hab g hg τ hτ)
          simpa [Perm.mul_apply] using this
        _ = τ i := by rw [hgi]
  by_contra hπ1
  have hπT : π ∈ T' := hπτ ▸ hτ
  obtain ⟨b, hb, hb1, hbπ⟩ : ∃ b ∈ T', b ≠ 1 ∧ b ≠ π := by
    by_contra hcon
    push Not at hcon
    have hsub : (T' : Set (Perm (Fin 9))) ⊆ {1, π} := by
      intro b hb
      by_cases hb1 : b = 1
      · simp [hb1]
      · simp [hcon b hb hb1]
    have h2 : (T' : Set (Perm (Fin 9))).ncard ≤ 2 := by
      calc (T' : Set (Perm (Fin 9))).ncard ≤ ({1, π} : Set (Perm (Fin 9))).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 2 := by
            refine (Set.ncard_insert_le 1 ({π} : Set (Perm (Fin 9)))).trans ?_
            rw [Set.ncard_singleton]
    have h3 : (T' : Set (Perm (Fin 9))).ncard = 8 := by
      rw [← Nat.card_coe_set_eq]
      exact hcard
    omega
  obtain ⟨x, hx, hxπ⟩ := htrans π hπT hπ1 b hb hb1
  have hcomm := hπ x hx
  apply hbπ
  rw [← hxπ, ← hcomm]
  group

end CFSG.CGT.T75P
