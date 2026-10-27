module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137CompDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137CompChev
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137CompAlt
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137CompSpor
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137CompSporFive
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137CompSporThree
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416ROdd
import CFSG.LocalAnalysis.GLTheoremA.CatB.List93IdNot2b

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround (SporTables.SporTypes)

section ListCertificates


theorem i137ChevClosureComp_of_rows (hb : LieOrderBridge) (hA : Chev2OddAmb)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hN2 : ∀ (S : Type) [Group S] (j : TauCeti.CFSGIndex), List93.NotChev2Idx j →
      Nonempty (S ≃* j.Group) → ¬ IsChevSimple 2 S)
    (hBr : SporadicBridges) (hD3 : ∀ q, KDChevDownQ 3 q) (hD5 : ∀ q, KDChevDownQ 5 q)
    (hS3 : ∀ name, k2Spor 3 name → CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier name) →
      SporTables.SporTypes 3 (fun T _ => ¬ catalogIs T (S9.isList93 3)) name)
    (hS5 : ∀ name, SporTables.SporTypes 5 (fun T _ => ¬ catalogIs T (S9.isList93 5)) name) :
    I137ChevClosureComp := by
  unfold I137ChevClosureComp
  intro p hp hp2 S _ _ hS hnab hK hlev α hα I hI hcat
  have hcases : p = 3 ∨ p = 5 ∨ 7 ≤ p := by
    have h2 := hp.two_le
    rcases Nat.lt_or_ge p 7 with h | h
    · interval_cases p <;> first | omega | (norm_num at hp)
    · exact Or.inr (Or.inr h)
  rcases hcases with h3 | h5 | h7
  · subst h3
    rcases hlev with hchev | hcat2
    · exact isChevSimple_two_of_chev_comp hb hA (hD3 3) hS hnab hchev α hα I hI hcat
    · obtain ⟨i, hi, ⟨e⟩⟩ := hcat2
      cases i with
      | alternating n hn =>
        exact isChevSimple_two_of_alt_comp hb hp hp2 hn hi e α hα I hI hcat
      | lie d =>
        exact isChevSimple_two_of_chev_comp hb hA (hD3 d.1.characteristic) hS hnab
          (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_of_lie d rfl e)
          α hα I hI hcat
      | sporadic s =>
        have hKs : CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier s) :=
          hK.of_injective ((hBr s).some.trans e.symm).toMonoidHom
            ((hBr s).some.trans e.symm).injective
        exact absurd hcat
          (not_isList93_of_spor_comp hp hp2 hOut hN2 ⟨3, hi⟩ (hS3 s hi hKs) hS hnab
            ⟨e⟩ α hα I hI)
      | cyclic pr hpr => exact hi.elim
  · subst h5
    rcases hlev with hchev | hcat2
    · exact isChevSimple_two_of_chev_comp hb hA (hD5 5) hS hnab hchev α hα I hI hcat
    · obtain ⟨i, hi, ⟨e⟩⟩ := hcat2
      cases i with
      | alternating n hn =>
        exact isChevSimple_two_of_alt_comp hb hp hp2 hn hi e α hα I hI hcat
      | lie d =>
        exact isChevSimple_two_of_chev_comp hb hA (hD5 d.1.characteristic) hS hnab
          (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_of_lie d rfl e)
          α hα I hI hcat
      | sporadic s =>
        exact absurd hcat
          (not_isList93_of_spor_comp hp hp2 hOut hN2 ⟨5, hi⟩ (hS5 s) hS hnab
            ⟨e⟩ α hα I hI)
      | cyclic pr hpr => exact hi.elim
  · exfalso
    obtain ⟨i, hi, _⟩ := hcat
    unfold S9.isList93 at hi
    rcases hi with ⟨h5, _⟩ | ⟨h3, _⟩ <;> omega

end ListCertificates

section Holds


theorem i137ChevClosureComp_holds
    : I137ChevClosureComp :=
  i137ChevClosureComp_of_rows CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
    chev2OddAmb_holds CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    List93.notChev2_holds CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    (kdChevDownQ_three_of_lieComp lieComp_holds)
    (fun _ => GLTheoremB.MovingAround.Inputs1315.kdChevDownQ_five_le Nat.prime_five le_rfl)
    (fun name hname hK => sporTypes_notList93_three
      CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds chev2OddAmb_holds
      List93.notChev2_holds CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
      CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
      CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds name hname hK)
    (sporTypes_notList93_five CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
      CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds)

end Holds

end CFSG.LocalAnalysis.GLTheoremA
