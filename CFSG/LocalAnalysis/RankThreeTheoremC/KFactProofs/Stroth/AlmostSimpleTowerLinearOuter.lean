module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerOuter
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

section Structure

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem linear_pElement_inner (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K - 1)
    {w : MulAut (projectiveSL n K)} (hw : w ∈ linearAutGroup n K) {k : ℕ} (hk : w ^ (p ^ k) = 1) :
    w ∈ inner (projectiveSL n K) := by
  haveI : (inner (projectiveSL n K)).Normal := inner_normal _
  have hIDle : inner (projectiveSL n K) ≤ linearAutGroup n K :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.standard_outer_quotients
      (n := n) (K := K)).1
  refine mem_of_pPow_eq_one_of_not_dvd_relIndex hp hIDle ?_ hw hk
  intro hd
  have h := UnitaryHigher.relIndex_inner_linearAutGroup_dvd (k := K) (n := n) (by omega)
  exact hpK ((hd.trans h).trans ((Nat.gcd_dvd_right _ _)))

theorem linear_pElements_inner_of_two_indep (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : ¬ p ∣ Nat.card K - 1)
    (hTwo : ∃ x₁ x₂ : projectiveSL n K, Commute x₁ x₂ ∧ x₁ ^ p = 1 ∧ x₂ ^ p = 1 ∧
      (∀ i j : ℤ, x₁ ^ i * x₂ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) ∧
      ∀ σ : K ≃+* K, fieldAut n K σ x₁ = x₁ ∧ fieldAut n K σ x₂ = x₂)
    {X : Type} [Group X] [Finite X] (hrk : CFSG.LieType.SeitzGeneration.RankLE2 p X)
    (ψ : X →* MulAut (projectiveSL n K)) (hψ : Function.Injective ψ) (L : Subgroup X)
    (hL : ∀ y : projectiveSL n K, ∃ l ∈ L, ψ l = MulAut.conj y)
    {x : X} (hx : ∃ k : ℕ, x ^ (p ^ k) = 1) : ψ x ∈ inner (projectiveSL n K) := by
  haveI hDn : (linearAutGroup n K).Normal := linearAutGroup_normal_of_three_le hn
  obtain ⟨x₁, x₂, hc, h1, h2, hi, hfix⟩ := hTwo
  refine pElements_inner_of_two_indep (fieldAut n K) (linearAutGroup n K) hp
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.standard_outer_quotients
      (n := n) (K := K)).1
    (fun w hw ⟨k, hk⟩ => linear_pElement_inner hn hp hpK hw hk)
    (fun σ h => (CFSG.RankThree.PartTwo.KFacts.fieldAut_mem_linearAutGroup_iff hn).1 h)
    (fun z ⟨k, hk⟩ => ?_)
    (CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL hn)
    (fun τ _ => ⟨x₁, x₂, hc, h1, h2, hi, (hfix τ).1, (hfix τ).2⟩) hrk ψ hψ L hL hx
  obtain ⟨A, σ, hz⟩ := mem_semilinearAutGroup_iff.1
    (mem_semilinearAutGroup_of_pow_odd hn (Odd.pow (hp.odd_of_ne_two hp2)) hk)
  exact ⟨conjAut n K A, conjAut_mem_linearAutGroup A, σ, hz⟩

end Structure

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
