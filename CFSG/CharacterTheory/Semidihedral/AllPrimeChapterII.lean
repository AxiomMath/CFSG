module

public import CFSG.CharacterTheory.Semidihedral.AllPrimeWorkingI
public import CFSG.CharacterTheory.Semidihedral.AllPrimeCover
public import CFSG.CharacterTheory.Semidihedral.AllPrimeDGroups
public import CFSG.CharacterTheory.Semidihedral.AllPrimeLocalQD
public import CFSG.LocalAnalysis.ABGTheoremB.ChapterIIDerived

public section

namespace CFSG.Semidihedral.AllPrime

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ABGTheoremB CFSG.ABGLocalTools CFSG.QuasiDihedralFusion CFSG.ABGQGroups
open scoped Pointwise

theorem frontier_chapterIIFacts_of
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrec : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hlocal : ∀ H : Subgroup G, (∃ r : ℕ, r.Prime ∧ IsPLocal r H) → IsQDGroup H →
      ∀ r : ℕ, HasQDCharPower H r → r = 3 ∨ r = 5 ∨
        (r ∣ (frontierSetting S fS t p f).q ∧ r ≠ (frontierSetting S fS t p f).q))
    (hnotqd : ∀ H : Subgroup G, (frontierSetting S fS t p f).T ≤ H → oddCoreIn H ≠ ⊥ →
      (((frontierSetting S fS t p f).C ⊓ (frontierSetting S fS t p f).L : Subgroup G) : Set G) ⊆
        (H : Set G) * (((frontierSetting S fS t p f).C ⊓ (frontierSetting S fS t p f).ON :
          Subgroup G) : Set G) → ¬ IsQDGroup H) :
    (frontierSetting S fS t p f).ChapterIIFacts := by
  have hN := frontier_nStructure hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
    hmodel
  have hcover := frontier_cover_qgroup hGnonab hrec n hn S fS t ht hnonab hcentral hnc p f hp
    hpodd hf hq hmodel
  have hσ := frontierSetting_isValid hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
    hmodel
  have hrad := (frontierSetting S fS t p f).qgroup_solvRad_of hσ hN hcover
  exact
  { hN with
    localQD_charPower := hlocal
    workingI := semidihedral_workingHypothesisI hrec n hn S fS
    cover_qgroup := hcover
    not_qd_of_cover := hnotqd
    qd_or_d_of_three := frontier_qd_or_d_of_three hGnonab n hn S fS t ht hnonab hcentral hnc p f hp
      hpodd hf hq hmodel (fun K hK T₁ hT₁K hT₁ => qgroup_no_three K hK T₁ hT₁K hT₁)
    fusion_cases := frontier_fusion_cases hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
      hq hmodel
    fusion_disjoint := frontier_fusion_disjoint hGnonab n hn S fS t ht hnonab hcentral hnc p f hp
      hpodd hf hq hmodel
    qgroup_constraint_criterion := (frontierSetting S fS t p f).qgroup_constraint_criterion_of hσ hN
      hrad
    qgroup_solvRad := hrad
    automizer_T := frontier_automizer_T hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
      hq hmodel
    qgroup_no_three := fun K hK T₁ hT₁K hT₁ => qgroup_no_three K hK T₁ hT₁K hT₁
    normal_contains_three := frontier_normal_contains_three hGnonab n hn S fS t ht hnonab hcentral
      hnc p f hp hpodd hf hq hmodel
    solvable_dgroup_signalizer := frontier_solvable_dgroup_signalizer hGnonab n hn S fS t ht hnonab
      hcentral hnc p f hp hpodd hf hq hmodel }

theorem frontier_chapterIIFacts
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrec : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    (frontierSetting S fS t p f).ChapterIIFacts :=
  frontier_chapterIIFacts_of hGnonab hrec n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
    hmodel
    (frontier_localQD_charPower hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
      hmodel hrec)
    (frontier_not_qd_of_cover hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
      hmodel hrec)

end CFSG.Semidihedral.AllPrime
