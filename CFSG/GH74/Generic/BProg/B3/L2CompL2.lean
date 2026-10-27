module

public import CFSG.GH74.Generic.BProg.B3.L2CompL2Field
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalPSLTwoSections
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Context
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore

public section

namespace CFSG.GH74.Generic.BProg.B3.L2CompL2

open CFSG CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.AutL2Facts CFSG.GH74.Generic.S45 CFSG.LinearGroups
open CFSG.Blueprint CFSG.GH74.GLS Subgroup CFSG.LieType.Steinberg
open CFSG.Assembly.LowTwoRank CFSG.GH74.Generic
open CFSG.GH74.Generic.BProg.B3.L2CompL2Field
open scoped MatrixGroups

theorem exists_kleinFour_of_hasL2Model {L : Type} [Group L] [Finite L] (h : HasL2Model L Odd) :
    ∃ W : Subgroup L, IsKleinFour ↥W := by
  obtain ⟨p, f, hp, hf, hodd, hL⟩ := h
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, by omega⟩)
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSL hL
  have hoddF : IsOddPrimePower (Nat.card F) := isOddPrimePower_of hp hp2 hf hF
  let e' : L ≃* PSL2 F := e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have hd : HasDihedralSylowTwo L :=
    CFSG.ComponentClassification.OutcomeLocal.hasDihedralSylowTwo_of_mulEquiv e'
      (psl2_odd_hasDihedralSylowTwo_model F hoddF)
  obtain ⟨P⟩ : Nonempty (Sylow 2 L) := inferInstance
  obtain ⟨m, hm, ⟨eP⟩⟩ := hd P
  obtain ⟨V, -, hV⟩ := exists_kleinFour_le_of_dihedral_subgroup_mulEquiv (P : Subgroup L) hm eP
  exact ⟨V, hV⟩

end CFSG.GH74.Generic.BProg.B3.L2CompL2
