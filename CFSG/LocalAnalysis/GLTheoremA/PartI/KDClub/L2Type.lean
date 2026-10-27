module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.ExcBridge
import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.RankThree.PartTwo.Sec4.LThreePiKind
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.RankThree.PartTwo.Sec4

theorem nonempty_psl_two_equiv_alternating_five {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4 ∨ Nat.card F = 5) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) F ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ≃* alternatingGroup (Fin 5)) := by
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  have hcard : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) = 60 := by
    rcases hF with h | h
    · exact CFSG.ClassicalModels.projectiveSpecialLinear_two_card_of_card_four F h
    · exact CFSG.ClassicalModels.projectiveSpecialLinear_two_card_of_card_five F h
  exact CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty hcard

theorem catalogIs_psl_two_club {F : Type} [Field F] [Finite F]
    (h4 : 4 ≤ Nat.card F) (h3 : Nat.card F % 3 ≠ 0) (h1 : Nat.card F % 9 ≠ 1)
    (h8 : Nat.card F % 9 ≠ 8) :
    catalogIs (Matrix.SpecialLinearGroup (Fin 2) F ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) clubIndex := by
  by_cases h45 : Nat.card F = 4 ∨ Nat.card F = 5
  · obtain ⟨e5⟩ := nonempty_psl_two_equiv_alternating_five h45
    exact ⟨.alternating 5 le_rfl, Or.inr rfl, ⟨e5⟩⟩
  · obtain ⟨Q, _, hQc, ⟨φ⟩⟩ := exists_primePower_card_eq F
    have hv : (TauCeti.LieTypeIndex.A 1 Q).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      simp only [hQc]
      omega
    refine ⟨.lie ⟨.A 1 Q, hv⟩, Or.inr ?_, ⟨?_⟩⟩
    · show Q.card % 3 ≠ 0 ∧ Q.card % 9 ≠ 1 ∧ Q.card % 9 ≠ 8
      rw [hQc]
      exact ⟨h3, h1, h8⟩
    · exact (CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 2) φ).trans
        (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 Q hv).symm

theorem sl2_center_sq {F : Type} [Field F] {z : Matrix.SpecialLinearGroup (Fin 2) F}
    (hz : z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) : z ^ 2 = 1 := by
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  have hr2 : r ^ 2 = 1 := by simpa using hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrz, ← map_pow, hr2, map_one]
  rfl

theorem exists_sl2_model {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (slPi π 2 (p ^ f) K ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  have := hK.finite
  cases π
  · have hcard : Nat.card K = (p ^ f) ^ 2 := by rw [hK.card, piCard, Bool.cond_false]
    have := hK.charP
    have : Fact p.Prime := ⟨hK.prime⟩
    obtain ⟨e⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two
      (K := K) (r := p) (f := f) hcard
    exact ⟨CFSG.LieType.Steinberg.fixedSubfield K p f, inferInstance, inferInstance,
      CFSG.LieType.Steinberg.card_fixedSubfield hcard, ⟨e.symm⟩⟩
  · exact ⟨K, inferInstance, hK.finite, by rw [hK.card, piCard, Bool.cond_true],
      ⟨statedSLEquiv 2 K⟩⟩

end CFSG.LocalAnalysis.GLTheoremA
