module

public import CFSG.FeitThompson.Representations.RealBridgeRemainderProjectionBound
import CFSG.FeitThompson.Representations.BridgeCrossedCoefficientsOppositeParity

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

variable {G : Type*} [Group G] [Fintype G]

theorem exists_odd_int_cfInner_of_bridge (hodd : Odd (Nat.card G)) {α θ Γ Δ : G → ℂ}
    (hα : α ∈ signedIrr G) (hθ : θ ∈ signedIrr G)
    (hα1 : IsOrthogonal α (1 : G → ℂ)) (hθ1 : IsOrthogonal θ (1 : G → ℂ))
    (hαθ : IsOrthogonal α θ)
    (hΓ : Γ ∈ Submodule.span ℤ (Irr G)) (hΓreal : ∀ g, (Γ g).im = 0)
    (hΓ1 : IsOrthogonal Γ (1 : G → ℂ))
    (hΔ : Δ ∈ Submodule.span ℤ (Irr G)) (hΔreal : ∀ g, (Δ g).im = 0)
    (hΔ1 : IsOrthogonal Δ (1 : G → ℂ))
    (hβB : IsOrthogonal ((1 : G → ℂ) - α + Δ) ((1 : G → ℂ) - θ + Γ))
    (hβθ : IsOrthogonal ((1 : G → ℂ) - α + Δ) θ) :
    ∃ c : ℤ, Odd c ∧ cfInner Γ α = (c : ℂ) := by
  obtain ⟨c, hc⟩ := exists_int_cfInner_bridge hα hθ hΓ
  have hb : cfInner ((1 : G → ℂ) - α + Δ) θ = ((0 : ℤ) : ℂ) := by
    rw [isOrthogonal_iff.1 hβθ]; norm_num
  have hpar := odd_add_and_xor_odd_of_bridge hodd (isOrthogonal_iff.1 hα1)
    (isOrthogonal_iff.1 hθ1) (isOrthogonal_iff.1 hαθ) hΓ hΓreal (isOrthogonal_iff.1 hΓ1)
    hΔ hΔreal (isOrthogonal_iff.1 hΔ1) (isOrthogonal_iff.1 hβB) hc hb
  refine ⟨c, by simpa using hpar.1, ?_⟩
  have h1α : cfInner (1 : G → ℂ) α = 0 := by
    rw [← conj_cfInner, isOrthogonal_iff.1 hα1, map_zero]
  have hθα : cfInner θ α = 0 := by rw [← conj_cfInner, isOrthogonal_iff.1 hαθ, map_zero]
  rw [cfInner_add_left, cfInner_sub_left, h1α, hθα] at hc
  simpa using hc

section Family

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {θ Γ : G → ℂ} {r : ℝ} {v : ι → G → ℂ}

theorem forall_exists_odd_int_cfInner (hodd : Odd (Nat.card G))
    (hθ : θ ∈ signedIrr G) (hθ1 : IsOrthogonal θ (1 : G → ℂ))
    (hΓ : Γ ∈ Submodule.span ℤ (Irr G)) (hΓreal : ∀ g, (Γ g).im = 0)
    (hΓ1 : IsOrthogonal Γ (1 : G → ℂ)) (hvmem : ∀ i, v i ∈ signedIrr G)
    (hv1 : ∀ i, IsOrthogonal (v i) (1 : G → ℂ)) (hvθ : ∀ i, IsOrthogonal (v i) θ)
    (hbridge : ∀ i, ∃ Δ : G → ℂ, Δ ∈ Submodule.span ℤ (Irr G) ∧ (∀ g, (Δ g).im = 0) ∧
      IsOrthogonal Δ (1 : G → ℂ) ∧
      IsOrthogonal ((1 : G → ℂ) - v i + Δ) ((1 : G → ℂ) - θ + Γ) ∧
      IsOrthogonal ((1 : G → ℂ) - v i + Δ) θ) (i : ι) :
    ∃ c : ℤ, Odd c ∧ cfInner Γ (v i) = (c : ℂ) := by
  obtain ⟨Δ, hΔ, hΔreal, hΔ1, hβB, hβθ⟩ := hbridge i
  exact exists_odd_int_cfInner_of_bridge hodd (hvmem i) hθ (hv1 i) hθ1 (hvθ i) hΓ hΓreal hΓ1
    hΔ hΔreal hΔ1 hβB hβθ

theorem card_le_of_bridge_family (hodd : Odd (Nat.card G))
    (hθ : θ ∈ signedIrr G) (hθnr : θ ≠ fun x => conj (θ x))
    (hθ1 : IsOrthogonal θ (1 : G → ℂ))
    (hΓ : Γ ∈ Submodule.span ℤ (Irr G)) (hΓreal : ∀ g, (Γ g).im = 0)
    (hΓ1 : IsOrthogonal Γ (1 : G → ℂ)) (hr : 0 ≤ r)
    (hB : cfInner ((1 : G → ℂ) - θ + Γ) ((1 : G → ℂ) - θ + Γ) = (r : ℂ) + 2)
    (hv : IsOrthonormalFamily v) (hvmem : ∀ i, v i ∈ signedIrr G)
    (hv1 : ∀ i, IsOrthogonal (v i) (1 : G → ℂ)) (hvθ : ∀ i, IsOrthogonal (v i) θ)
    (hvθbar : ∀ i, IsOrthogonal (v i) fun x => conj (θ x))
    (hbridge : ∀ i, ∃ Δ : G → ℂ, Δ ∈ Submodule.span ℤ (Irr G) ∧ (∀ g, (Δ g).im = 0) ∧
      IsOrthogonal Δ (1 : G → ℂ) ∧
      IsOrthogonal ((1 : G → ℂ) - v i + Δ) ((1 : G → ℂ) - θ + Γ) ∧
      IsOrthogonal ((1 : G → ℂ) - v i + Δ) θ) :
    (Fintype.card ι : ℝ) ≤ r := by
  have hbound := sum_norm_sq_cfInner_le_of_real_bridge hθ hθnr (isOrthogonal_iff.1 hθ1) hΓ
    (fun x => Complex.conj_eq_iff_im.2 (hΓreal x)) (isOrthogonal_iff.1 hΓ1) hr hB hv
    (fun i => signedIrr_subset_classFun (hvmem i)) hvθ hvθbar
  have hlow : ∀ i, (1 : ℝ) ≤ ‖cfInner Γ (v i)‖ ^ 2 := by
    intro i
    obtain ⟨c, hcodd, hcv⟩ := forall_exists_odd_int_cfInner hodd hθ hθ1 hΓ hΓreal hΓ1 hvmem
      hv1 hvθ hbridge i
    have hc0 : c ≠ 0 := by rintro rfl; simp at hcodd
    have hsq : (1 : ℤ) ≤ c ^ 2 := by
      rcases lt_or_gt_of_ne hc0 with h | h <;> nlinarith
    rw [hcv, Complex.norm_intCast, sq_abs]
    exact_mod_cast hsq
  calc (Fintype.card ι : ℝ) = ∑ _i : ι, (1 : ℝ) := by simp
    _ ≤ ∑ i, ‖cfInner Γ (v i)‖ ^ 2 := Finset.sum_le_sum fun i _ => hlow i
    _ ≤ r := hbound

theorem real_bridge_odd_family_bound (hodd : Odd (Nat.card G))
    (hθ : θ ∈ signedIrr G) (hθnr : θ ≠ fun x => conj (θ x))
    (hθ1 : IsOrthogonal θ (1 : G → ℂ))
    (hΓ : Γ ∈ Submodule.span ℤ (Irr G)) (hΓreal : ∀ g, (Γ g).im = 0)
    (hΓ1 : IsOrthogonal Γ (1 : G → ℂ)) (hr : 0 ≤ r)
    (hB : cfInner ((1 : G → ℂ) - θ + Γ) ((1 : G → ℂ) - θ + Γ) = (r : ℂ) + 2)
    (hv : IsOrthonormalFamily v) (hvmem : ∀ i, v i ∈ signedIrr G)
    (hv1 : ∀ i, IsOrthogonal (v i) (1 : G → ℂ)) (hvθ : ∀ i, IsOrthogonal (v i) θ)
    (hvθbar : ∀ i, IsOrthogonal (v i) fun x => conj (θ x))
    (hbridge : ∀ i, ∃ Δ : G → ℂ, Δ ∈ Submodule.span ℤ (Irr G) ∧ (∀ g, (Δ g).im = 0) ∧
      IsOrthogonal Δ (1 : G → ℂ) ∧
      IsOrthogonal ((1 : G → ℂ) - v i + Δ) ((1 : G → ℂ) - θ + Γ) ∧
      IsOrthogonal ((1 : G → ℂ) - v i + Δ) θ) :
    (∀ i, ∃ c : ℤ, Odd c ∧ cfInner Γ (v i) = (c : ℂ)) ∧ (Fintype.card ι : ℝ) ≤ r :=
  ⟨forall_exists_odd_int_cfInner hodd hθ hθ1 hΓ hΓreal hΓ1 hvmem hv1 hvθ hbridge,
    card_le_of_bridge_family hodd hθ hθnr hθ1 hΓ hΓreal hΓ1 hr hB hv hvmem hv1 hvθ hvθbar
      hbridge⟩

end Family

end CFSG.FeitThompson
