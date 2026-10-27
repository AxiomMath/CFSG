module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCheck

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.SporAltRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.I1416Rows

theorem scompOK_three_of_card_dvd_360 {Q : Type} [Group Q]
    [Finite Q] {k : Q} (hk3 : orderOf k = 3)
    (hk : Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 360) : SCompOK 3 k := by
  intro I hI
  obtain ⟨hs, hnab⟩ := KDSpor.pSimple_simple_nonab Nat.prime_three hI
  haveI := hs
  have h3 : 3 * Nat.card (PSimple 3 I) ∣ 360 :=
    (three_mul_card_pSimple_dvd_cent hk3 hI.1).trans hk
  have hd : Nat.card (PSimple 3 I) ∣ 3000 :=
    (Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) (h3.trans (by norm_num : 360 ∣ 3 * 120))).trans
      (by norm_num)
  obtain ⟨fA⟩ := CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (KDSpor.card_eq_sixty_of_dvd_3000 hnab hd)
  exact stypeOK_A5 (Or.inl rfl) fA

theorem srow_three_of_check {s : TauCeti.SporadicName}
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (D : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.Data)
    (hD : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check D = true)
    {A B : Equiv.Perm (Fin D.n)}
    (hA : CFSG.Monster.B.Co2.Rep D.n D.A A) (hB : CFSG.Monster.B.Co2.Rep D.n D.B B)
    (b : ↥(Subgroup.closure {A, B}) ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hs : IsSimpleGroup ↥(Subgroup.closure {A, B})) (hpr : ¬ D.ord.Prime)
    (hsmall : ∀ c < D.cases.size, D.cases[c]!.card ∣ 360) : SRow s 3 := by
  obtain ⟨hcardP, hcls⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check_card_order_sound D hA hB hD
  refine srow_of_model hOut b
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hcardP]; exact hpr))
    fun x hx => ?_
  have hx3 : orderOf (x : Equiv.Perm (Fin D.n)) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨c, hc, hcc⟩ := hcls x x.2 hx3
  refine scompOK_three_of_card_dvd_360 hx ?_
  have hmapc := CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype
    (Subgroup.closure {A, B}) x
  have hcc' : Nat.card (Subgroup.centralizer ({x} : Set ↥(Subgroup.closure {A, B}))) =
      Nat.card ↥(Subgroup.centralizer ({(x : Equiv.Perm (Fin D.n))} : Set (Equiv.Perm (Fin D.n))) ⊓
        Subgroup.closure {A, B}) := by
    rw [← hmapc, Subgroup.card_map_of_injective (Subgroup.closure {A, B}).subtype_injective]
  rw [hcc', hcc]
  exact hsmall c hc

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem srow_M23_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    SRow .M23 3 :=
  srow_three_of_check hOut m23S3Data Certificates.certificate13511.2.2.2 rep_m23A rep_m23B
    (hbr .M23).some CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2
    (by rw [show m23S3Data.ord = 10200960 from rfl]; norm_num) (by decide +kernel)

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem srow_HS_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    SRow .HS 3 := by
  have h := Certificates.certificate13514
  obtain ⟨hvA, hvB⟩ := check_valid h
  have e : CFSG.Blueprint.NativeSporadic.HS ≃* ↥CFSG.Sporadic.Schreier.hsP :=
    CFSG.Sporadic.Schreier.hsPermEquiv
  exact srow_three_of_check hOut hsS3Data h (CFSG.RankThree.Native.rep_of_validA hvA)
    (CFSG.RankThree.Native.rep_of_validA hvB) (e.symm.trans (hbr .HS).some)
    (@MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.HS.isSimpleGroup_HS e.symm)
    (by rw [show hsS3Data.ord = 44352000 from rfl]; norm_num) (by decide +kernel)

end CFSG.LocalAnalysis.GLTheoremA.SporAltRows

