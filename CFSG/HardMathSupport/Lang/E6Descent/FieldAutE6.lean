module

public import CFSG.RankThree.PartOne.KE.OddE6NoninnerCore
public import CFSG.RankThree.Chevalley.SteinbergBTEvenE6Noninner
public import CFSG.RankThree.PartOne.CTP.SeitzField
public import CFSG.RankThree.PartOne.CTP.StrongPClassification

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne.CTP

section Main

theorem exists_conj_entrywise_E6 {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (α : MulAut (adjointGroup Tag.E6 K)) (hα : IsOuterOfOrder p α) :
    ∃ (ψ : MulAut (adjointGroup Tag.E6 K)) (σ : K ≃+* K), orderOf σ = p ∧
      ψ * α * ψ⁻¹ = entrywiseAdjointAut Tag.E6 σ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  obtain ⟨hord, hout⟩ := hα
  let α' : (⊤ : Subgroup (MulAut (adjointGroup Tag.E6 K))) := ⟨α, Subgroup.mem_top _⟩
  have hα' : (α' : MulAut (adjointGroup Tag.E6 K)) ∉
      (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)).range :=
    fun ⟨g, hg⟩ => hout g hg.symm
  have hαp : orderOf α' = p := by rw [Subgroup.orderOf_mk]; exact hord
  by_cases h2 : ringChar K = 2
  · have hK2 : Nat.card K = 2 ^ (n : ℕ) := by rw [hK, h2]
    obtain ⟨Θ, -, hΘ, -⟩ := ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
    obtain ⟨⟨σ, -, hσord, ψ, hψ⟩, -, -⟩ :=
      CFSG.RankThree.Chevalley.even_E6_noninner_large_prime_field_descent_and_local_core_trivial n.pos K hK2 Θ hΘ hp hp3
        ⊤ le_top α' hα' hαp
    exact ⟨ψ, σ, hσord, hψ⟩
  · obtain ⟨-, ⟨σ, δ, hσ, hδ⟩, -⟩ :=
      CFSG.RankThree.PartOne.KE.odd_E6_noninner_large_prime_field_descent_and_local_core_trivial
        hℓ h2 n.pos K hK hp hp3 ⊤ le_top α' hα' hαp
    exact ⟨δ, σ, hσ, hδ⟩

end Main

end CFSG.HardMathSupport.Lang.E6Descent
