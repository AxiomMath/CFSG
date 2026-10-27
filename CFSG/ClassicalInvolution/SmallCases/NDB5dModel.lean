module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Small

public section

namespace CFSG.ClassicalInvolution.NDB.WC

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD

theorem conjSub_commutes {K : Type*} [Group K] {R S : Subgroup K} (h : Commutes R S) (g : K) :
    Commutes (conjSub g R) (conjSub g S) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  show g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹)
  calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
    _ = g * (b * a) * g⁻¹ := by rw [h a ha b hb]
    _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group

variable {p : ℕ} [Fact p.Prime]

theorem exists_commuting_partner {t : StatedLieTag} {n e : ℕ} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (hA1 : ¬ (t = .PSL ∧ n = 2))
    (hA2 : ¬ (t = .PSL ∧ n = 3)) (h2A2 : ¬ (t = .PSU ∧ n = 3)) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) {R : Subgroup (modelUniv t n p e Fact.out).K}
    (hR : R ∈ ModelFund p t n e) : ∃ S ∈ ModelFund p t n e, S ≠ R ∧ Commutes R S := by
  rcases Asc77.ih8_tag_cases hp2 hq hfund hadm hG2 hD4 with hconn | hsmall
  · exact Asc77.ih8_exists_edge_of_connected hp2 hq hfund hadm hA1 hconn hR
  · have hedge : ∃ R₀ ∈ ModelFund p t n e, ∃ S₀ ∈ ModelFund p t n e, R₀ ≠ S₀ ∧
        Commutes R₀ S₀ := by
      refine Asc77.ih8SmallEdge p t n e hadm hp2 hq ?_
      rcases hsmall with ⟨ht, hn⟩ | ⟨ht, hn⟩ | h | h | h | h
      · subst ht
        have h2 : 2 ≤ n := hadm.2.2.1
        have h2' : n ≠ 2 := fun h => hA1 ⟨rfl, h⟩
        have h3' : n ≠ 3 := fun h => hA2 ⟨rfl, h⟩
        exact Or.inl ⟨rfl, by omega⟩
      · subst ht
        have h3 : 3 ≤ n := hadm.2.2.1
        have h3' : n ≠ 3 := fun h => h2A2 ⟨rfl, h⟩
        exact Or.inr (Or.inl ⟨rfl, by omega⟩)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    obtain ⟨R₀, hR₀, S₀, hS₀, hne, hc⟩ := hedge
    obtain ⟨g, rfl⟩ :=
      ModelFacts.fundamentalSingleClass t n p e Fact.out hfund hadm hG2 hD4 R₀ hR₀ R hR
    refine ⟨conjSub g S₀, conjSub_mem_fundamentalSubgroups hS₀ g, fun h => hne ?_,
      conjSub_commutes hc g⟩
    exact (conjSub_injective g h).symm

end CFSG.ClassicalInvolution.NDB.WC
