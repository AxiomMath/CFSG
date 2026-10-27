module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.FourGroup
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Transfer
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Thm2Defs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardBridge

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.ComponentClassification CFSG.ComponentClassification.HarrisLit

theorem pumpUpFalse (hT1 : Harris82Theorem1KProper) (hID : IdentGenInput)
    (hT3 : Theorem3Full) (hHB : HardBranchInputBalanced)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog G) (hcat : ¬ Blueprint.Catalog G)
    (hbal : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    {L : Subgroup G} {t : G} (ht2 : orderOf t = 2) (hLt : L ≤ centralizer ({t} : Set G))
    (hLp : IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set G))))
    (h : HasClassBMember ↥L) : False := by
  obtain ⟨J, u, hJ, hs⟩ := h
  obtain ⟨W, hW2, hW4, htW, huW, htu, hu1, huJ, hJc, hM⟩ :=
    exists_fourGroup_of_classBMember ht2 hLt hLp hJ
  have hs' : ClassBShape ↥(J.map L.subtype) :=
    ClassBShape.of_mulEquiv (J.equivMapOfInjective L.subtype L.subtype_injective) hs
  obtain ⟨hu2, -, htM, hCW⟩ := L35.centralizer_eq_inf hW2 hW4 huW hu1 htW htu
  have hJ' : IsTwoComponentIn (J.map L.subtype) (centralizer {(u : G)} ⊓ centralizer {t}) := by
    rw [← hCW]
    exact hJc
  have hJt : J.map L.subtype ≤ centralizer {t} := hJ'.1.trans inf_le_right
  have huWJ : (u : G) ∈ J.map L.subtype ⊓ W := ⟨huJ, huW⟩
  have hne : J.map L.subtype ⊓ W ≠ ⊥ := fun h0 => hu1 (by
    rwa [h0, Subgroup.mem_bot] at huWJ)
  have hKc : IsTwoComponentIn (GSThmB.conjClosure (J.map L.subtype)
      (GSThmB.layerIn (centralizer {(u : G)}))) (centralizer {(u : G)}) := by
    by_cases hp : PartialCentre ↥(J.map L.subtype)
    · exact hHB G hnab hKP hcat hbal W hW2 hW4 _ hJc hM hs' hp hne (u : G) huWJ hu1
    · exact hT3 G hnab hKP hcat W hW2 hW4 _ hJc hM hs' hp hne (u : G) huWJ hu1
  have hKcomm : GSThmB.conjClosure (J.map L.subtype) (GSThmB.layerIn (centralizer {(u : G)})) =
      ⁅J.map L.subtype, GSThmB.layerIn (centralizer {(u : G)})⁆ :=
    L35.conjClosure_eq_commutator ht2 htM hJ'
  have hKt : (GSThmB.conjClosure (J.map L.subtype)
      (GSThmB.layerIn (centralizer {(u : G)}))).map (MulAut.conj t).toMonoidHom =
      GSThmB.conjClosure (J.map L.subtype) (GSThmB.layerIn (centralizer {(u : G)})) := by
    rw [hKcomm]
    exact L35.map_conj_commutator_eq htM hJt
  have hJK : J.map L.subtype ≤ GSThmB.conjClosure (J.map L.subtype)
      (GSThmB.layerIn (centralizer {(u : G)})) := GSThmB.B5a.le_conjClosure _ _
  have huK := hJK huJ
  have hKM := not_isMTypeSchur_of_kProper hT1 hnab hKP hcat hu2 hKc huK Nat.prime_three
    (by norm_num)
  exact hID G hnab hKP hcat (u : G) t hu2 (hW2 t htW) htu htM (J.map L.subtype) hJ' hM hs' huJ _
    rfl hJK hKc huK hKM hKt

end CFSG.OddStandard.HigherRank.F3
