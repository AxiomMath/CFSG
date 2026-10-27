module

public import Certificates.Certificate17322
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzDefs
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SimpleLeaf

public section

namespace CFSG.HardMathSupport.Dickson.I271

open Subgroup CFSG.Open CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.Sporadic.SuzOddCore
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
  CFSG.HardMathSupport.Dickson.I271.TabSuzFuse CFSG.HardMathSupport.Dickson.I271.TabSuzB

@[expose] noncomputable def xBPerm : Equiv.Perm (Fin 1782) :=
  permOfArr 1782 (xBArr (levels ()))

section Check

theorem xBPerm_pow : xBPerm ^ 3 = 1 := Certificates.certificate17322.1

theorem TabSuzB.caseB_spec :
    Nat.card (closure (permsA 1782 (aGens ()))) = 729 ∧ xBPerm ∈ suzM ∧
      closure (permsA 1782 (aGens ())) ≤ centralizer {xBPerm} ⊓ suzM ∧
      (∀ g ∈ centralizer {xBPerm} ⊓ suzM, ∀ r ∈ closure (permsA 1782 (aGens ())),
        g * r * g⁻¹ ∈ closure (permsA 1782 (aGens ()))) ∧
      centralizer (closure (permsA 1782 (aGens ())) : Set (Equiv.Perm (Fin 1782))) ⊓
        (centralizer {xBPerm} ⊓ suzM) ≤ closure (permsA 1782 (aGens ())) :=
  Certificates.certificate17322.2.2

theorem splitShapeAt_xB (hx : xBPerm ∈ suzM) : SplitShapeAt 3 (⟨xBPerm, hx⟩ : ↥suzM) := by
  refine Or.inl ?_
  refine pConstrainedShape_of_map_injective suzM.subtype suzM.subtype_injective ?_
  rw [map_centralizer_subtype']
  obtain ⟨hcard, -, hle, hnorm, hcent⟩ := TabSuzB.caseB_spec
  exact pConstrainedShape_of_normal_pgroup hle (normal_subgroupOf_of_conj hnorm)
    (IsPGroup.of_card (n := 6) (by rw [hcard]; norm_num)) hcent

end Check

end CFSG.HardMathSupport.Dickson.I271
