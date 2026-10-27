module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporRows
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Data
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporTh7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.SporAltRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.I1416Rows


theorem not_isChevSimple_of_not_lieOrder
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {T : Type} [Group T]
    [Finite T] {N : ℕ} (hT : Nat.card T = N)
    (hN : ∀ d : TauCeti.LieTypeIndex, d.Valid →
      CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula d ≠ N)
    (h60 : N ≠ 60) (h360 : N ≠ 360) (h8 : N ≠ 20160) (q : ℕ) : ¬ IsChevSimple q T := by
  rintro (⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩)
  · cases i with
    | lie d => exact hN d.1 d.2 ((hb d T ⟨e⟩).symm.trans hT)
    | _ => exact hi.elim
  · cases i with
    | lie d => exact hN d.1 d.2 ((hb d T ⟨e⟩).symm.trans hT)
    | alternating n hn5 =>
      simp only [ambiguousChev] at hi
      have hc : Nat.card T = n.factorial / 2 :=
        (Nat.card_congr e.toEquiv).trans
          (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt n (by omega))
      rw [hT] at hc
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact h60 (by rw [hc]; decide)
      · exact h360 (by rw [hc]; decide)
      · exact h8 (by rw [hc]; decide)
    | _ => exact hi.elim

theorem scompOK_three_of_card_dvd_1080
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {Q : Type} [Group Q]
    [Finite Q] {k : Q} (hk3 : orderOf k = 3)
    (hk : Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 1080) : SCompOK 3 k := by
  intro I hI
  obtain ⟨hs, hnab⟩ := KDSpor.pSimple_simple_nonab Nat.prime_three hI
  haveI := hs
  have h3 : 3 * Nat.card (PSimple 3 I) ∣ 1080 :=
    (prime_mul_card_pSimple_dvd_cent Nat.prime_three hk3 hI.1).trans hk
  exact stypeOK_three_of_card_dvd_360 hb hnab
    (Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) (h3.trans (by norm_num)))

theorem srow_three_of_check_1080 {s : TauCeti.SporadicName}
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (D : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.Data)
    (hD : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check D = true)
    {A B : Equiv.Perm (Fin D.n)}
    (hA : CFSG.Monster.B.Co2.Rep D.n D.A A) (hB : CFSG.Monster.B.Co2.Rep D.n D.B B)
    (b : ↥(Subgroup.closure {A, B}) ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hs : IsSimpleGroup ↥(Subgroup.closure {A, B})) (hpr : ¬ D.ord.Prime)
    (hsmall : ∀ c < D.cases.size, D.cases[c]!.card ∣ 1080) : SRow s 3 := by
  obtain ⟨hcardP, hcls⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check_card_order_sound D hA hB hD
  refine srow_of_model hOut b
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hcardP]; exact hpr))
    fun x hx => ?_
  have hx3 : orderOf (x : Equiv.Perm (Fin D.n)) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨c, hc, hcc⟩ := hcls x x.2 hx3
  refine scompOK_three_of_card_dvd_1080 hb hx ?_
  have hmapc := CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype
    (Subgroup.closure {A, B}) x
  have hcc' : Nat.card (Subgroup.centralizer ({x} : Set ↥(Subgroup.closure {A, B}))) =
      Nat.card ↥(Subgroup.centralizer ({(x : Equiv.Perm (Fin D.n))} : Set (Equiv.Perm (Fin D.n))) ⊓
        Subgroup.closure {A, B}) := by
    rw [← hmapc, Subgroup.card_map_of_injective (Subgroup.closure {A, B}).subtype_injective]
  rw [hcc', hcc]
  exact hsmall c hc

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem srow_J2_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    SRow .J2 3 := by
  have h := Certificates.certificate13513
  obtain ⟨hvA, hvB⟩ := check_valid h
  have e : CFSG.Blueprint.NativeSporadic.J2 ≃* ↥CFSG.Sporadic.Schreier.j2P :=
    CFSG.Sporadic.Schreier.j2PermEquiv
  exact srow_three_of_check_1080 hOut hb j2S3Data h (CFSG.RankThree.Native.rep_of_validA hvA)
    (CFSG.RankThree.Native.rep_of_validA hvB) (e.symm.trans (hbr .J2).some)
    (@MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J2.isSimpleGroup_J2 e.symm)
    (by rw [show j2S3Data.ord = 604800 from rfl]; norm_num) (by decide +kernel)

theorem scompOK_three_of_card_dvd_1080_or_504
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {Q : Type} [Group Q]
    [Finite Q] {k : Q} (hk3 : orderOf k = 3)
    (hk : Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 1080 ∨
      Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 504) : SCompOK 3 k := by
  rcases hk with hk | hk
  · exact scompOK_three_of_card_dvd_1080 hb hk3 hk
  · intro I hI
    obtain ⟨hs, hnab⟩ := KDSpor.pSimple_simple_nonab Nat.prime_three hI
    haveI := hs
    have h3 : 3 * Nat.card (PSimple 3 I) ∣ 504 :=
      (prime_mul_card_pSimple_dvd_cent Nat.prime_three hk3 hI.1).trans hk
    have hd : Nat.card (PSimple 3 I) ∣ 168 :=
      Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) (h3.trans (by norm_num))
    exact stypeOK_three_of_card_168 hnab (card_eq_168_of_dvd hnab hd)

theorem srow_three_of_check_1080_504 {s : TauCeti.SporadicName}
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (D : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.Data)
    (hD : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check D = true)
    {A B : Equiv.Perm (Fin D.n)}
    (hA : CFSG.Monster.B.Co2.Rep D.n D.A A) (hB : CFSG.Monster.B.Co2.Rep D.n D.B B)
    (b : ↥(Subgroup.closure {A, B}) ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hs : IsSimpleGroup ↥(Subgroup.closure {A, B})) (hpr : ¬ D.ord.Prime)
    (hsmall : ∀ c < D.cases.size, D.cases[c]!.card ∣ 1080 ∨ D.cases[c]!.card ∣ 504) :
    SRow s 3 := by
  obtain ⟨hcardP, hcls⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check_card_order_sound D hA hB hD
  refine srow_of_model hOut b
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hcardP]; exact hpr))
    fun x hx => ?_
  have hx3 : orderOf (x : Equiv.Perm (Fin D.n)) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨c, hc, hcc⟩ := hcls x x.2 hx3
  refine scompOK_three_of_card_dvd_1080_or_504 hb hx ?_
  have hmapc := CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype
    (Subgroup.closure {A, B}) x
  have hcc' : Nat.card (Subgroup.centralizer ({x} : Set ↥(Subgroup.closure {A, B}))) =
      Nat.card ↥(Subgroup.centralizer ({(x : Equiv.Perm (Fin D.n))} : Set (Equiv.Perm (Fin D.n))) ⊓
        Subgroup.closure {A, B}) := by
    rw [← hmapc, Subgroup.card_map_of_injective (Subgroup.closure {A, B}).subtype_injective]
  rw [hcc', hcc]
  exact hsmall c hc

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem srow_M24_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    SRow .M24 3 :=
  srow_three_of_check_1080_504 hOut hb m24S3Data Certificates.certificate13512 rep_m24A
    rep_m24B (hbr .M24).some CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
    (by rw [show m24S3Data.ord = 244823040 from rfl]; norm_num) (by decide +kernel)

end CFSG.LocalAnalysis.GLTheoremA.SporAltRows

