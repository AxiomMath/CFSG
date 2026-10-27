module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeChapterIICover
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeChapterIIFusion
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeNFacts
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeWorkingI
import CFSG.CharacterTheory.Semidihedral.AllPrimeWorkingI
import CFSG.LocalAnalysis.ABGTheoremB.ChapterIIDerived

public section

namespace CFSG.Wreathed.OriginalAllPrime

open CFSG.ABGTheoremB CFSG.QuasiDihedralFusion CFSG.ABGLocalTools CFSG.ABGQGroups
open SmallerRecognitionOriginalField
open scoped Pointwise

theorem wreathedSetting_chapterIIFacts
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G)
    (hsd : CFSG.Semidihedral.ProperSubgroupRegularity.SmallerSimpleRecognition G)
    (hLQD : ∀ H : Subgroup G, (∃ r : ℕ, r.Prime ∧ IsPLocal r H) → IsQDGroup H →
      ∀ r : ℕ, HasQDCharPower H r →
        r = 3 ∨ r = 5 ∨ (r ∣ (wreathedSetting n S e p f).q ∧ r ≠ (wreathedSetting n S e p f).q))
    (hNQD : ∀ H : Subgroup G, (wreathedSetting n S e p f).T ≤ H → oddCoreIn H ≠ ⊥ →
      (((wreathedSetting n S e p f).C ⊓ (wreathedSetting n S e p f).L : Subgroup G) : Set G) ⊆
        (H : Set G) * (((wreathedSetting n S e p f).C ⊓ (wreathedSetting n S e p f).ON :
          Subgroup G) : Set G) → ¬ IsQDGroup H) :
    (wreathedSetting n S e p f).ChapterIIFacts := by
  have hσ := wreathedSetting_isValid hnonab n hn S e hfour p f hp hpodd hf hq hlocal
  have hN := wreathedSetting_nStructure hnonab n hn S e hfour p f hp hpodd hf hq hlocal
  have hcover :=
    wreathedSetting_cover_qgroup hnonab n hn S e hfour p f hp hpodd hf hq hlocal hrec
  have hrad := (wreathedSetting n S e p f).qgroup_solvRad_of hσ hN hcover
  exact {
    toNStructure := hN
    localQD_charPower := hLQD
    workingI := wreathedSetting_workingHypothesisI hrec hsd
    cover_qgroup := hcover
    not_qd_of_cover := hNQD
    qd_or_d_of_three := wreathedSetting_qd_or_d_of_three n hn S e p f
    fusion_cases := wreathedSetting_fusion_cases n hn S e p f
    fusion_disjoint := fun H => fusion_classes_disjoint (H := H)
    qgroup_constraint_criterion :=
      (wreathedSetting n S e p f).qgroup_constraint_criterion_of hσ hN hrad
    qgroup_solvRad := hrad
    automizer_T := wreathedSetting_automizer_T hnonab n hn S e hfour p f hp hpodd hf hq hlocal
    qgroup_no_three := CFSG.Semidihedral.AllPrime.qgroup_no_three
    normal_contains_three := wreathedSetting_normal_contains_three n hn S e p f
    solvable_dgroup_signalizer := wreathedSetting_solvable_dgroup_signalizer n hn S e p f }

end CFSG.Wreathed.OriginalAllPrime
