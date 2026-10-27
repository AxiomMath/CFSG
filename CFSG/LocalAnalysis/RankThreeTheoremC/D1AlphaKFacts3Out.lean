module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaList3
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaKFacts3OutLin
import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaKFacts3OutUni
public import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

theorem kFactSL3OutNormalSylow : KFactSL3OutNormalSylow := by
  intro K _ _ hK d hd ⟨e⟩
  have : Group.IsPerfect K := ⟨hK.1⟩
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  rcases hd with ⟨q, hqd, -⟩ | ⟨q, hqd, -⟩
  · simp only at hqd
    subst hqd
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have hm : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 3 q.p q.exponent := by
      refine ⟨⟨q.prime_p, q.exponent_pos, by norm_num, ?_, ?_⟩, GaloisField q.p q.exponent,
        inferInstance, inferInstance, GaloisField.card q.p q.exponent q.exponent_pos.ne',
        ⟨(e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans
          (projectiveSpecialLinearGroupEquivStatedProj 3 (GaloisField q.p q.exponent))⟩⟩
      · intro h
        simp only [Prod.mk.injEq] at h
        omega
      · intro h
        simp only [Prod.mk.injEq] at h
        omega
    obtain ⟨-, k, _, _, -, ⟨e'⟩⟩ := hm
    exact kOutNormalSylow_three_of_filter
      ((e'.trans (projectiveSpecialLinearGroupEquivStatedProj 3 k).symm).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 k))
      (threeFilter_projectiveSL_three k)
  · simp only at hqd
    subst hqd
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    obtain ⟨⟨-, hf1, hadm⟩, k, _, _, hk, ⟨e'⟩⟩ := hm
    have hq : ¬(3 = 3 ∧ q.p ^ q.exponent = 2) := fun ⟨h1, h2⟩ => hadm.2 (by rw [h1, h2])
    have hU : UnitaryFieldData q.p q.exponent k :=
      ⟨q.prime_p, hf1, by rw [hk, ← pow_mul, mul_comm]⟩
    obtain ⟨⟨ζ⟩, -⟩ := UnitaryHigher.unitary_full_diagonal_outer_order hU (le_refl 3) hq
    exact kOutNormalSylow_three_of_filter
      ((e'.trans (ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by norm_num)).symm).trans ζ.symm)
      (threeFilter_primeFormP_three hU hq)

end CFSG.LocalAnalysis.RankThreeTheoremC
