module

public import CFSG.LieType.OutStructureFiveDispatch
public import CFSG.LieType.OutStructureThreeRankLarge
public import CFSG.LieType.OutStructureSevenOneThreeSecond

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms

theorem sevenOneThree_third_five
    {X : Type} [Group X] [Finite X] (hK : CFSG.Open.IsKGroup X) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {L : Subgroup X} (hL : CFSG.IsComponent L) (hLn : L.Normal)
    (hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3) :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
      (L ⊔ Subgroup.centralizer (L : Set X)) := by
  have := hLn
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsPerfect ↥L := hL.1.1
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.1.2.1
  have hq : CFSG.Open.IsQuasisimple ↥L := ⟨Group.isPerfect_def.mp hL.1.1, hL.1.2.1⟩
  have hnab : ∃ a b : ↥L ⧸ Subgroup.center ↥L, a * b ≠ b * a :=
    CFSG.LocalAnalysis.RankThreeUC.S15.K7145Proof.quotient_center_nonabelian hq
  have hcat : CFSG.Open.IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) :=
    CFSG.LocalAnalysis.RankThreeUC.S15.K7145Proof.isCatalogGroup_quotient_center hK L hq
  rcases sylow_normal_outer_five_or_exceptional hL.1.2.1 hnab hcat hp hp5 with hOut | hex
  · have hOutL : ∀ S : Sylow p (Outer ↥L), (S : Subgroup (Outer ↥L)).Normal :=
      CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo.sylow_normal_of_injective
        (centerQuotient_outer_injective ↥L) hOut
    obtain ⟨R⟩ : Nonempty (Sylow p X) := inferInstance
    exact CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo.isPClosedMod_of_normal_sup_sylow R
      (CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.normal_sup_sup_centralizer_of_outer L R hOutL)
  · exfalso
    have hLX : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) ≤ 3 := by
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
      exact (CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans hX3
    have hGA := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    rcases hex with ⟨N, r, f, hcl, hN, -⟩ | ⟨N, r, f, hcl, hN, -⟩
    · have := four_le_pRank_three_of_classical_large hGA hq hcl (Or.inl rfl) (by omega)
      omega
    · have := four_le_pRank_three_of_classical_large hGA hq hcl (Or.inr rfl) (by omega)
      omega

theorem sevenOneThree_holds_of_hInput
    (hInput : ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
      ∀ p : ℕ, p.Prime → p ≠ 2 → 5 ≤ p →
      ∀ L : Subgroup X, L.Normal → CFSG.IsComponent L →
      CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 →
      ¬ CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
          (L ⊔ Subgroup.centralizer (L : Set X)) →
        (∃ c : X, c ∈ Subgroup.centralizer (L : Set X) ∧ orderOf c = p) ∨
        ∃ x : X, orderOf x = p ∧ x ∉ L ⊔ Subgroup.centralizer (L : Set X) ∧
          ∃ E : Subgroup X, E ≤ L ∧ CFSG.Open.IsElemAbelian p E ∧
            Nat.card E = p ^ CFSG.Open.pRank p L ∧ ∀ a ∈ E, a * x = x * a) :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneThree :=
  sevenOneThree_holds_of_maximalTorus hInput
    fun _ _ _ hK _ hp _ hp5 _ hLn hL hX3 => sevenOneThree_third_five hK hp hp5 hL hLn hX3

end CFSG.LieType.OutStructure
