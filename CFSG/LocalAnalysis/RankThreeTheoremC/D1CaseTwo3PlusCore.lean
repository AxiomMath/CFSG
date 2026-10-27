module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CentralU
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

section CaseTwo

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoData3.pRank_plusCore_le_one (hd : D1CaseTwoData3 p P M H R Rbar)
    {Kb : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKb : IsComponentOf Kb ⊤)
    (hKX : ¬ Kb ≤ d1X0 p M H) : Open.pRank p (d1PlusCore p H Kb) ≤ 1 :=
  D1CaseTwoDataU.pRank_plusCore_le_one hd.toU hKb hKX

theorem D1CaseTwoData3.perfect_le_plusCore (hOut : KFactOutCyclic) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hSch : KFactCatalogSchreier)
    (hd : D1CaseTwoData3 p P M H R Rbar)
    {Kb : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKb : IsComponentOf Kb ⊤)
    (hKX : ¬ Kb ≤ d1X0 p M H) {U : Subgroup G} (hU : U ≤ H ⊓ M) (hUp : ⁅U, U⁆ = U) :
    U ≤ d1PlusCore p H Kb :=
  D1CaseTwoDataU.perfect_le_plusCore hOut hS hKL hSch hd.toU hKb hKX hU hUp

end CaseTwo

theorem two_blocks_pRank_ge {M A : Subgroup G} (hAM : A ≤ M)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {L₁ L₂ : Subgroup G}
    (h₁ : IsTwoPrimeComponent M L₁) (h₂ : IsTwoPrimeComponent M L₂) (hne : L₁ ≠ L₂)
    {y₁ y₂ : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hy₁A : y₁ ∈ barM M A) (hy₂A : y₂ ∈ barM M A) (hy₁L : y₁ ∈ barM M L₁)
    (hy₂L : y₂ ∈ barM M L₂) (hy₁q : IsPGroup q (Subgroup.zpowers y₁))
    (hy₂q : IsPGroup q (Subgroup.zpowers y₂))
    (hnc₁ : ∃ l ∈ barM M L₁, y₁ * l ≠ l * y₁) (hnc₂ : ∃ l ∈ barM M L₂, y₂ * l ≠ l * y₂) :
    2 ≤ Open.pRank q A := by
  classical
  have hb : barM M L₁ ≠ barM M L₂ := fun he => hne (h₁.eq_of_barM_eq h₂ he)
  let L : Fin 2 → Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := ![barM M L₁, barM M L₂]
  have hinj : Function.Injective L := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij hb
    · exact absurd hij.symm hb
    · rfl
  have hcomp : ∀ i, IsComponentOf (L i) ⊤ := by
    intro i
    fin_cases i
    · exact h₁.component
    · exact h₂.component
  have h := stmtComponentRank hq L hcomp hinj (barM M A) ![y₁, y₂]
    (by intro i; fin_cases i; exacts [hy₁A, hy₂A])
    (by intro i; fin_cases i; exacts [hy₁L, hy₂L])
    (by intro i; fin_cases i; exacts [hy₁q, hy₂q])
    (by intro i; fin_cases i; exacts [hnc₁, hnc₂])
  have h2 : Nat.card (Fin 2) = 2 := by simp
  rw [h2] at h
  exact h.trans (stmtBarPRankLift hq hq2 M A hAM)

end CFSG.LocalAnalysis.RankThreeTheoremC
