module

public import CFSG.ClassicalInvolution.Q3.Q3P21L1
public import CFSG.ClassicalInvolution.Q3.Q3TLKSU

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3P21

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TY CFSG.ClassicalInvolution.Q3.Q3TIV
  CFSG.ClassicalInvolution.Q3.Q3TLK CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt TwinElt TwinElt.u TwinRow twinYModel
  TwinDatumOn TwinMFGenerationOn)
open CFSG.ClassicalInvolution.Generic.CoreAssembly (LinkedAtProduct)
open CFSG.ClassicalInvolution.Q3 (CompData IsClassicalMember3)
open scoped MatrixGroups


theorem twinLinked3_sl4 (h3 : OddThreeFreeInput) (hP : CommutingProductP1Input3)
    (hY2 : TwinYType3On (fun t n => t = .PSL ∧ n = 4)) : TwinLinked3At .PSL 4 := by
  intro G _ _ _ hnab K z hR hshape K₂ hK₂ hK₂K hK₂T w hw
  classical
  have hrow : TwinRow .PSL 4 := Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  have hΩ : InClass3 (conjClass3 K) := hR.inClass
  obtain ⟨hex, -⟩ := hR.setup
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  obtain ⟨c⟩ := Q3TP.nonempty_tctxS3 (Q3TIV.twinRowFacts3_sl4).1 h3 hR hshape
  obtain ⟨T, hTz, hTQ⟩ := c.exists_twin
  have hT : IsTwinAt (conjClass3 K) K T z := TCtxS3.isTwinAt3 c hTz hTQ.le
  have hclsT : IsClassicalMember3 T z :=
    Q3TIV.twinInvolution3_of_odd3 h3 G hnab K z hR .PSL 4 hrow hshape T hT
  have hKT : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hTΩ : T ∈ conjClass3 K := hT.mem.1
  obtain ⟨e⟩ := exists_twinElt3 hR.cls hclsT (hex K hKΩ) (hex T hTΩ)
  obtain ⟨hP1u, hO3u⟩ := hP G K z hR T hTΩ hKT e.u e.u_mem_sup
    (twinElt_orderOf_u3 e hR.cls (hex K hKΩ) hKT)
    (twinElt_u_not_mem_left3 e hR.cls (hex K hKΩ) hKT)
    (twinElt_u_not_mem_right3 e hclsT (hex T hTΩ) hKT)
  obtain ⟨ι, hι, D, hcard, i, hkind, -⟩ := hY2 G hnab K z hR .PSL 4 hrow ⟨rfl, rfl⟩ hshape T hT
    hclsT e hP1u hO3u
  have hmod : twinYModel 3 .PSL 4 = (.POmegaMinus, 4) := by simp [twinYModel]
  have hkind' : D.kind i = CompData.model .POmegaMinus 4 := by
    have h := hkind
    rw [hmod] at h
    exact h
  have hone : ∀ j : ι, j = i := by
    have h1 : Nat.card ι = 1 := hcard
    have : Subsingleton ι := (Nat.card_eq_one_iff_unique.mp h1).1
    exact fun j => Subsingleton.elim j i
  have hadm : StatedLieAdmissible .POmegaMinus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hnc : ∀ R ∈ (D.kind i).fund, ∀ r ∈ R, r ∈ Subgroup.center (D.kind i).G → r = 1 := by
    rw [hkind']
    exact fundNoncentral_model3 trivial hadm (by decide)
  have hmodel : SqTrichotomyC (D.kind i) := by
    rw [hkind']
    exact sqTrichotomyC_of_on sqTrichotomy3_minus4
  exact linked_of_model3 hR hT hclsT e hP1u hO3u D i hone hnc hmodel
    (exists_twin_frame3 h3 hnab hR hrow hshape hT hclsT)
    (fun hZ => false_of_layer_le_centralizer3 h3 hnab hR hrow hshape hT hclsT e
      twinMFGenerationOn3_psl4 hZ)
    (fun J t hJ hJK hJT hJiso hZt =>
      false_of_layer_le_centralizer_tz3 h3 hR hrow hshape hT e hJ hJK hJT hJiso hZt)
    hK₂ hK₂K (hK₂T T hT) hw

end CFSG.ClassicalInvolution.Q3.Q3P21
