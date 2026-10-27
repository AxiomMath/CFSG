module

public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality

public section

namespace CFSG.ComponentClassification.GSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {X : Type} [Group X] [Finite X] [IsSimpleGroup X]

omit [Finite X] in
theorem not_mem_center_of_orderOf_eq_two (hnonab : ∃ a b : X, a * b ≠ b * a) {z : X}
    (hz : orderOf z = 2) : z ∉ center X := by
  intro hzc
  rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with h | h
  · rw [h, mem_bot] at hzc
    rw [hzc, orderOf_one] at hz
    exact absurd hz (by norm_num)
  · obtain ⟨a, b, hab⟩ := hnonab
    have ha : a ∈ center X := h ▸ mem_top a
    exact hab ((mem_center_iff.mp ha b).symm)

theorem exists_maximal_unbalancing_triple_bounded (hTB : ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput) (hGF : GloballyFirstRankTwoInput)
    (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X)
    (htriple : ∃ (a x : X) (J : Subgroup X), GSUnbalancingTriple a x J) :
    ∃ (a x : X) (J : Subgroup X), GSMaximalUnbalancingTriple a x J ∧
      ∀ (c v : X) (K : Subgroup X), GSUnbalancingTriple c v K →
        (pPrimeCore 2 K).index ≤ (pPrimeCore 2 J).index := by
  classical
  have : Finite (Subgroup X) :=
    Finite.of_injective (fun H : Subgroup X => (H : Set X)) SetLike.coe_injective
  let T := {p : X × X × Subgroup X // GSUnbalancingTriple p.1 p.2.1 p.2.2}
  obtain ⟨a₀, x₀, J₀, h₀⟩ := htriple
  have : Nonempty T := ⟨⟨(a₀, x₀, J₀), h₀⟩⟩
  obtain ⟨⟨⟨a, x, J⟩, hJ⟩, hmax⟩ := Finite.exists_max (fun p : T => gsMeasure p.1.1 p.1.2.2)
  dsimp only at hJ hmax
  have hle : ∀ (c v : X) (K : Subgroup X), GSUnbalancingTriple c v K →
      gsMeasure c K ≤ gsMeasure a J := fun c v K hK' => hmax ⟨(c, v, K), hK'⟩
  have hparts : ∀ (c v : X) (K : Subgroup X), GSUnbalancingTriple c v K →
      (pPrimeCore 2 K).index ≤ (pPrimeCore 2 J).index ∧
        ((pPrimeCore 2 K).index = (pPrimeCore 2 J).index →
          pRank 2 ↥(centralizer ({c} : Set X) ⊓ normalizer (K : Set X) ⊓ coreActionKernel K) ≤
            pRank 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X) ⊓
              coreActionKernel J) ∧
          (pRank 2 ↥(centralizer ({c} : Set X) ⊓ normalizer (K : Set X) ⊓ coreActionKernel K) =
              pRank 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X) ⊓
                coreActionKernel J) →
            2 ^ (Nat.card ↥(centralizer ({c} : Set X) ⊓ normalizer (K : Set X))).factorization 2 ≤
              2 ^ (Nat.card ↥(centralizer ({a} : Set X) ⊓
                normalizer (J : Set X))).factorization 2)) := by
    intro c v K hK'
    have h := hle c v K hK'
    unfold gsMeasure at h
    obtain ⟨h1, h2⟩ := Prod.Lex.toLex_le_toLex'.mp h
    refine ⟨h1, fun heq => ?_⟩
    obtain ⟨h3, h4⟩ := Prod.Lex.toLex_le_toLex'.mp (h2 heq)
    exact ⟨h3, h4⟩
  refine ⟨a, x, J, hGF X hK (fun z hz' => not_mem_center_of_orderOf_eq_two hnonab hz') a x J hJ
    (two_le_pRank_of_gsUnbalancingTriple hTB hSA hnonab hK hz hU hJ)
    (fun c v K hK' => (hparts c v K hK').1)
    (fun c v K hK' _ heq => ((hparts c v K hK').2 heq).1)
    (fun c v K hK' _ heq hrk => ((hparts c v K hK').2 heq).2 hrk),
    fun c v K hK' => (hparts c v K hK').1⟩

theorem exists_maximal_unbalancing_triple (hTB : ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput) (hGF : GloballyFirstRankTwoInput)
    (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X)
    (htriple : ∃ (a x : X) (J : Subgroup X), GSUnbalancingTriple a x J) :
    ∃ (a x : X) (J : Subgroup X), GSMaximalUnbalancingTriple a x J := by
  obtain ⟨a, x, J, hJ, -⟩ :=
    exists_maximal_unbalancing_triple_bounded hTB hSA hGF hnonab hK hz hU htriple
  exact ⟨a, x, J, hJ⟩

end CFSG.ComponentClassification.GSLit
