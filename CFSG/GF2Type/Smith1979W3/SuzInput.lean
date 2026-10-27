module

public import CFSG.GF2Type.Smith1979W3.KProper
public import CFSG.GF2Type.Smith1979W3.TypeA2
public import CFSG.GF2Type.Smith1979W3.CaseD.Main
public import CFSG.Quasithin.Vol2.Asc94.He42Holds
public import CFSG.Quasithin.Vol2.Asc94.HeOrderHolds
public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.Sporadic.SuzRecog.Holds
public import CFSG.GF2Type.Smith1979W3.CaseIINonsplit

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3

open CFSG CFSG.Blueprint CFSG.Open CFSG.LargeExtraspecial CFSG.ComponentClassification

@[expose] def SuzL34DataInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → ∀ S : Setting G,
    S.width = 3 →
      (¬ ∃ U : Subgroup G, U ≤ S.QG ∧ IsElemAbelian 2 U ∧ Nat.card U = 16) →
      S.Mbar.map S.O.subtype = timmesfeldOmega S.q →
      (∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z) → AS81.SuzL34Data S.z

@[expose] def TypeA2WidthThreeK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → ∀ S : Setting G,
    S.width = 3 → ¬ S.IsReducible →
      (∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z ∧ S.HasTypeAInL g) →
        NativeSporadic.IsSporadic G .Suz

theorem typeA2K_of (h : T1216WidthThree) (hSuz : AS81.SuzRecognition')
    (hL34 : SuzL34DataInput) : TypeA2WidthThreeK := by
  intro G _ _ _ hKP S hw hirr ha
  obtain ⟨hno, q, hq, -, hM⟩ := h G S hw hirr ha
  have hmap := S.Mbar_map_eq_timmesfeldOmega (by omega) hq hM
  obtain ⟨g, hgQ, hgz, -⟩ := ha
  exact hSuz G S hw hno hmap ⟨g, hgQ, hgz⟩ (hL34 G hKP S hw hno hmap ⟨g, hgQ, hgz⟩)

section CertsK


theorem smith1979WidthThreeK_of_leavesK (hB : ReducibleWidthThreeK)
    (hC : TypeA2WidthThreeK) (hD : IrreducibleNoA2WidthThree) : Smith1979WidthThreeK := by
  intro G _ _ _ hKP hnonab z hz hext hcard
  exact widthThree_of_leaves_at aschbacherFSmith1977Statement_holds hnonab hz hext hcard
    (fun S hw hnwc hred => hB G hKP S hw hnwc hred)
    (fun S hw hirr ha => hC G hKP S hw hirr ha)
    (fun S hw hnwc hirr hno => hD G S hw hnwc hirr hno)

end CertsK

section Certs


theorem smith1979WidthThreeCharTwoKP_of_inputs'
    (hSplit : DWSplitWidthThree) (hT1216 : T1216WidthThree)
    (hL34 : SuzL34DataInput) : Smith1979WidthThreeCharTwoKP :=
  smith1979WidthThreeCharTwoKP_of_K
    CFSG.RankThree.PartOne.TCB.catalogBridgeFor_all
    (smith1979WidthThreeK_of_leavesK
      (reducibleK_of_split hSplit
        (CFSG.Quasithin.A94.asc94K_of_he_order CFSG.Quasithin.A94.he_order_holds))
      (typeA2K_of hT1216 CFSG.Sporadic.SuzRecog.suzRecognition'_holds hL34)
      (irreducibleNoA2WidthThree_of_TI
        (TI75.weaklyClosedTITransitive_of_inputs
            (CFSG.LargeExtraspecial.TI75Bridge.simpleCaseStmt_of_rest
                ⟨CFSG.CGT.A8S.a8SylowInput, CFSG.CGT.M24S.m24SylowInput⟩)
            CFSG.CGT.Timmesfeld75.lemma215)))

theorem smith1979WidthThreeCharTwoKP_of_t1216 (hT1216 : T1216WidthThree)
    (hL34 : SuzL34DataInput) : Smith1979WidthThreeCharTwoKP :=
  smith1979WidthThreeCharTwoKP_of_inputs' dwSplitWidthThree hT1216 hL34

end Certs

end CFSG.GF2Type.Smith1979W3
