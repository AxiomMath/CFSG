module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.EndDataDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.NotExc
public import CFSG.Milestones.CT_catalog_nonabelian_type_partition

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

theorem false_of_even_cyclic (hEven : EvenResidualStd) (hCTSS : CTSSStd)
    (hSmall : SmallLieStd) (hG2 : G2DerivedU33) {G : Type} [Group G] [Finite G] {x : G}
    {Y : Subgroup G} (hY : EndData G x Y) (hA : InSA (↥Y ⧸ center ↥Y))
    (hnotA : ¬ ∃ n : ℕ, 5 ≤ n ∧ Nonempty (↥Y ⧸ center ↥Y ≃* alternatingGroup (Fin n)))
    (S : Sylow 2 ↥(Subgroup.centralizer (Y : Set G)))
    (hS : IsCyclic ↥(S : Subgroup ↥(Subgroup.centralizer (Y : Set G)))) : False := by
  haveI := hY.setting.simple
  have hNE : ¬ Recognition.Exact.EvenStandardException (↥Y ⧸ center ↥Y) :=
    not_evenStandardException_of_inSA hG2 hA hnotA
  rcases hA with ⟨hcat, hcard, hnotChev, hnotL32, hnotHe, hnotM12, hnotJ2⟩
  have hnonab : ∃ a b : ↥Y ⧸ center ↥Y, a * b ≠ b * a := hY.isQuasisimple.2.2
  have hType : Recognition.Exact.EvenStandardType (↥Y ⧸ center ↥Y) := by
    rcases (CFSG.Milestones.ct_catalog_nonabelian_type_partition (↥Y ⧸ center ↥Y) hnonab).1
      hcat with hAlt | hOdd | hEvenLie | hSp
    · exact absurd hAlt hnotA
    · obtain ⟨t, n, p, f, hp, hp2, -, hm⟩ := hOdd
      exact absurd ⟨t, n, f, hm⟩ (hnotChev p hp hp2)
    · exact Or.inl hEvenLie
    · exact Or.inr hSp
  have hRes : Recognition.Exact.EvenStandardResidual ↥Y :=
    hEven G hY.setting.nonab hY.setting.kProper Y hY.standard hY.balanced_open S hS hType hNE
  have hout : Recognition.EvenSporadicOutcome G := by
    rcases hRes.2 with hRA | hRB | hRC | hRD
    · exact hCTSS G hY.setting.nonab hY.setting.kProper Y hY.standard hY.balanced_open S hS
        hType hNE hRes hRA.1 (fun h => (h.elim hnotM12 hnotJ2).elim)
    · exact hSmall G hY.setting.nonab hY.setting.kProper Y hY.standard hY.balanced_open S hS
        hType hNE hRes (Or.inl hRB)
    · exact hSmall G hY.setting.nonab hY.setting.kProper Y hY.standard hY.balanced_open S hS
        hType hNE hRes (Or.inr (Or.inl hRC))
    · exact hSmall G hY.setting.nonab hY.setting.kProper Y hY.standard hY.balanced_open S hS
        hType hNE hRes (Or.inr (Or.inr hRD))
  rcases hout with h | h | h | h | h | h | h <;>
    exact hY.setting.notCat (CFSG.GH74.catalog_of_isSporadic h)

end CFSG.OddStandard.SmallF3.HypA2
