module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSporAlt
public import CFSG.LocalAnalysis.SectionRank.OddCover.CubicKernel

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThree.PartOne.StrongP
open scoped commutatorElement

theorem kernelTrivialAt_of_odd {X : Type} [Group X] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* X),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
      π.ker = ⊥) : KernelTrivialAt X p := by
  intro E _ _ _ π hπ hC hker
  refine h E π hπ hC ?_
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hker
  rw [hn]
  exact (Fact.out : p.Prime).odd_of_ne_two hp2 |>.pow

theorem kernelTrivialAt_of_cubic {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {x y h : X} (hxp : x ^ p = 1) (hyp : y ^ p = 1) (hz1 : ⁅x, y⁆ ≠ 1)
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (hQ : Nat.card (Subgroup.closure ({x, y} : Set X)) = p ^ 3) (hS : ¬ p ^ 4 ∣ Nat.card X)
    {a b c d k l μ : ℕ} (hhx : h * x * h⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ k)
    (hhy : h * y * h⁻¹ = x ^ c * y ^ d * ⁅x, y⁆ ^ l) (hhz : h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ μ)
    (hdet : ((μ : ZMod p) * a - 1) * ((μ : ZMod p) * d - 1) - (μ : ZMod p) ^ 2 * b * c ≠ 0) :
    KernelTrivialAt X p := by
  intro E _ _ _ π hπ hC hker
  refine CFSG.SectionRank.OddCover.eq_bot_of_forall_sylow_eq_bot π.ker ?_
  intro r hr _ P
  by_cases hrp : r = p
  · subst hrp
    exact CFSG.SectionRank.OddCover.cubic_extraspecial_sylow_central_kernel π hπ hC hxp hyp hz1
      hzx hzy hQ hS hhx hhy hhz hdet P
  · have hP : IsPGroup p (⊤ : Subgroup ↥π.ker) := hker.of_equiv Subgroup.topEquiv.symm
    exact disjoint_top.1 (IsPGroup.disjoint_of_ne r p hrp _ _ P.isPGroup' hP)

theorem sporCaseThreePrimeData_of_noncomm {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (h4 : ¬ p ^ 4 ∣ Nat.card X) (hn : HasNoncommPair p X) (hk : KernelTrivialAt X p) :
    SporCaseThreePrimeData X p :=
  Or.inr (Or.inl ⟨h4, hn, hk⟩)

theorem sporCaseThreePrimeData_of_not_dvd {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (h : ¬ p ^ 3 ∣ Nat.card X) : SporCaseThreePrimeData X p :=
  Or.inl h

theorem sporadicCaseThreeData_of_card {X : Type} [Group X] {n : ℕ} (hX : Nat.card X = n)
    (hn : n ≠ 0)
    (h : ∀ p ∈ n.primeFactors, p ≠ 2 → ∀ [Finite X] [Fact p.Prime], SporCaseThreePrimeData X p) :
    SporadicCaseThreeData X := by
  refine ⟨hX ▸ hn, fun {_} p _ hp2 => ?_⟩
  have hp : p.Prime := Fact.out
  by_cases hd : p ∣ n
  · exact h p (Nat.mem_primeFactors.2 ⟨hp, hd, hn⟩) hp2
  · refine sporCaseThreePrimeData_of_not_dvd ?_
    rw [hX]
    exact fun h3 => hd ((dvd_pow_self p three_ne_zero).trans h3)

end CFSG.AGLEmbedding
