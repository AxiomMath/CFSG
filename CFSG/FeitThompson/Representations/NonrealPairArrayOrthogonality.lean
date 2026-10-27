module

public import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing
import CFSG.FeitThompson.Representations.NormOneVirtualCharacters
import CFSG.FeitThompson.Representations.DisjointCoherentRowColumnContradiction
import CFSG.FeitThompson.Representations.SmallIntegralNormOrthogonalArray
public import CFSG.FeitThompson.Representations.UnitInnerProductSignedPair

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate ComplexOrder

theorem ne_conj_conj_of_ne_conj {α : Type*} {ρ : α → ℂ} (hρ : ρ ≠ fun x => conj (ρ x)) :
    (fun x => conj (ρ x)) ≠ fun x => conj (conj (ρ x)) := by
  intro h
  refine hρ (funext fun x => ?_)
  have hx := congrFun h x
  simp only [Complex.conj_conj] at hx
  exact hx.symm

variable {G : Type*} [Group G] [Fintype G]

theorem cfInner_self_sub_conj_of_mem_signedIrr {ρ : G → ℂ} (hρ : ρ ∈ signedIrr G)
    (hρr : ρ ≠ fun x => conj (ρ x)) :
    cfInner (ρ - fun x => conj (ρ x)) (ρ - fun x => conj (ρ x)) = 2 := by
  have hcmem : (fun x => conj (ρ x)) ∈ signedIrr G := conj_mem_signedIrr hρ
  have h0 : cfInner ρ (fun x => conj (ρ x)) = 0 := cfInner_conj_eq_zero_of_ne hρ hρr
  have h0' : cfInner (fun x => conj (ρ x)) ρ = 0 := by rw [← conj_cfInner, h0, map_zero]
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right,
    cfInner_self_of_mem_signedIrr hρ, cfInner_self_of_mem_signedIrr hcmem, h0, h0']
  ring

theorem conj_sub_conj_conj_eq_neg (ρ : G → ℂ) :
    ((fun x => conj (ρ x)) - fun x => conj (conj (ρ x))) = -(ρ - fun x => conj (ρ x)) := by
  funext x
  simp

theorem cfInner_eq_zero_of_cfInner_sub_conj_eq_zero {ρ ψ : G → ℂ}
    (hρ : ρ ∈ signedIrr G) (hρr : ρ ≠ fun x => conj (ρ x)) (hψ : ψ ∈ signedIrr G)
    (hsub : cfInner (ρ - fun x => conj (ρ x)) ψ = 0) : cfInner ρ ψ = 0 := by
  have h0 : cfInner ρ (fun x => conj (ρ x)) = 0 := cfInner_conj_eq_zero_of_ne hρ hρr
  have h0' : cfInner (fun x => conj (ρ x)) ρ = 0 := by rw [← conj_cfInner, h0, map_zero]
  rw [cfInner_sub_left, sub_eq_zero] at hsub
  by_contra hne
  have hcψ : cfInner (fun x => conj (ρ x)) ψ = 0 := by
    rcases cfInner_eq_zero_or_one_or_neg_one_of_mem_signedIrr hρ hψ with h | h | h
    · exact absurd h hne
    · rw [← eq_of_cfInner_eq_one hρ hψ h]; exact h0'
    · have h1 : cfInner (-ρ) ψ = 1 := by rw [cfInner_neg_left, h, neg_neg]
      rw [← eq_of_cfInner_eq_one (neg_mem_signedIrr_iff.2 hρ) hψ h1, cfInner_neg_right, h0',
        neg_zero]
  exact hne (hsub.trans hcψ)

theorem isOrthogonal_of_ne_conj_of_add_swap {m n : ℕ} {η : Fin m → Fin n → G → ℂ}
    (hηmem : ∀ i j, η i j ∈ Submodule.span ℤ (Irr G))
    (hη : IsOrthonormalFamily fun p : Fin m × Fin n => η p.1 p.2)
    (hmn : 3 ≤ min m n) {ρ : G → ℂ} (hρ : ρ ∈ signedIrr G) (hρr : ρ ≠ fun x => conj (ρ x))
    (hrect : ∀ i k : Fin m, ∀ j l : Fin n,
      cfInner (ρ - fun x => conj (ρ x)) (η i j) + cfInner (ρ - fun x => conj (ρ x)) (η k l)
        = cfInner (ρ - fun x => conj (ρ x)) (η i l)
          + cfInner (ρ - fun x => conj (ρ x)) (η k j)) :
    ∀ i j, IsOrthogonal ρ (η i j) ∧ IsOrthogonal (fun x => conj (ρ x)) (η i j) := by
  have hcmem : (fun x => conj (ρ x)) ∈ signedIrr G := conj_mem_signedIrr hρ
  set d : G → ℂ := ρ - fun x => conj (ρ x) with hd
  have hdmem : d ∈ Submodule.span ℤ (Irr G) :=
    Submodule.sub_mem _ (signedIrr_subset_span_Irr hρ) (signedIrr_subset_span_Irr hcmem)
  have hlt : cfInner d d < ((min m n : ℕ) : ℂ) := by
    have h3 : (3 : ℝ) ≤ ((min m n : ℕ) : ℝ) := by exact_mod_cast hmn
    rw [cfInner_self_sub_conj_of_mem_signedIrr hρ hρr, Complex.lt_def]
    refine ⟨?_, ?_⟩
    · simp only [Complex.re_ofNat, Complex.natCast_re]
      linarith
    · simp
  have hzero : ∀ i j, cfInner d (η i j) = 0 := fun i j =>
    isOrthogonal_iff.1 (isOrthogonal_of_cfInner_self_lt_min hηmem hη hdmem hrect hlt i j)
  intro i j
  have hηsigned : η i j ∈ signedIrr G :=
    mem_signedIrr_of_mem_span_Irr_of_cfInner_self_eq_one (hηmem i j) (hη.cfInner_self (i, j))
  refine ⟨isOrthogonal_iff.2 ?_, isOrthogonal_iff.2 ?_⟩
  · exact cfInner_eq_zero_of_cfInner_sub_conj_eq_zero hρ hρr hηsigned (hzero i j)
  · refine cfInner_eq_zero_of_cfInner_sub_conj_eq_zero hcmem (ne_conj_conj_of_ne_conj hρr)
      hηsigned ?_
    rw [conj_sub_conj_conj_eq_neg, ← hd, cfInner_neg_left, hzero i j, neg_zero]

end CFSG.FeitThompson
