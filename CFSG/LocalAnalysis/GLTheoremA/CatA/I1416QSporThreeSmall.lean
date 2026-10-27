module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporOrder90
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporOrder120
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Data
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporAut168
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporTh7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I1416QRows

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

theorem qtypeOK_three_of_card_dvd_360
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {T : Type} [Group T]
    [Finite T] [IsSimpleGroup T] (hnab : ∃ a b : T, a * b ≠ b * a) (hd : Nat.card T ∣ 360) :
    QTypeOK 3 T := by
  have hns : ¬ Group.IsSolvable T := fun h => by
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.2 h) a b)
  have h60 : 60 ≤ Nat.card T := by
    by_contra h
    exact hns (CFSG.GroupTheory.groups_order_below_sixty_solvable (by omega))
  have hcases : Nat.card T = 60 ∨ Nat.card T = 72 ∨ Nat.card T = 90 ∨ Nat.card T = 120 ∨
      Nat.card T = 180 ∨ Nat.card T = 360 := by
    obtain ⟨c, hc⟩ := hd
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc
    have hc6 : c ≤ 6 := by
      by_contra h
      have : Nat.card T * 7 ≤ Nat.card T * c := Nat.mul_le_mul_left _ (by omega)
      omega
    interval_cases c <;> omega
  rcases hcases with h | h | h | h | h | h
  · obtain ⟨fA⟩ := CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h
    exact qtypeOK_A5 (Or.inl rfl) fA
  · exact qtypeOK_of_card hb h (by norm_num) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide)
  · exact qtypeOK_of_not_chev fun q _ _ _ => not_isChevSimple_of_not_lieOrder hb h
      (fun d hd => I1416Rows.Order90.lieOrderFormula_ne_90 hd) (by decide) (by decide) (by decide) q
  · exact qtypeOK_of_not_chev fun q _ _ _ => not_isChevSimple_of_not_lieOrder hb h
      (fun d hd => I1416Rows.Order120.lieOrderFormula_ne_120 hd) (by decide) (by decide) (by decide) q
  · exact qtypeOK_of_card hb h (by norm_num) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide)
  · exact qtypeOK_three_of_card_360 hb h

theorem qtypeOK_three_of_card_168 {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hnab : ∃ a b : T, a * b ≠ b * a) (hc : Nat.card T = 168) : QTypeOK 3 T :=
  qtypeOK_of_not_sq_dvd_aut Nat.prime_three (not_sq_three_dvd_card_mulAut_of_card_168 hnab hc)

theorem qcompOK_three_of_card_dvd_1080
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {Q : Type} [Group Q]
    [Finite Q] {k : Q} (hk3 : orderOf k = 3)
    (hk : Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 1080) : QCompOK 3 k := by
  intro I hI
  obtain ⟨hs, hnab⟩ := KDSpor.pSimple_simple_nonab Nat.prime_three hI
  haveI := hs
  have h3 : 3 * Nat.card (PSimple 3 I) ∣ 1080 :=
    (prime_mul_card_pSimple_dvd_cent Nat.prime_three hk3 hI.1).trans hk
  exact qtypeOK_three_of_card_dvd_360 hb hnab
    (Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) (h3.trans (by norm_num)))

theorem qrow_three_of_check_1080 {s : TauCeti.SporadicName}
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (D : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.Data)
    (hD : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check D = true)
    {A B : Equiv.Perm (Fin D.n)}
    (hA : CFSG.Monster.B.Co2.Rep D.n D.A A) (hB : CFSG.Monster.B.Co2.Rep D.n D.B B)
    (b : ↥(Subgroup.closure {A, B}) ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hs : IsSimpleGroup ↥(Subgroup.closure {A, B})) (hpr : ¬ D.ord.Prime)
    (hsmall : ∀ c < D.cases.size, D.cases[c]!.card ∣ 1080) : I1416QRow s 3 := by
  obtain ⟨hcardP, hcls⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check_card_order_sound D hA hB hD
  refine qrow_of_model hOut b
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hcardP]; exact hpr))
    fun x hx => ?_
  have hx3 : orderOf (x : Equiv.Perm (Fin D.n)) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨c, hc, hcc⟩ := hcls x x.2 hx3
  refine qcompOK_three_of_card_dvd_1080 hb hx ?_
  have hmapc := CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype
    (Subgroup.closure {A, B}) x
  have hcc' : Nat.card (Subgroup.centralizer ({x} : Set ↥(Subgroup.closure {A, B}))) =
      Nat.card ↥(Subgroup.centralizer ({(x : Equiv.Perm (Fin D.n))} : Set (Equiv.Perm (Fin D.n))) ⊓
        Subgroup.closure {A, B}) := by
    rw [← hmapc, Subgroup.card_map_of_injective (Subgroup.closure {A, B}).subtype_injective]
  rw [hcc', hcc]
  exact hsmall c hc

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem qrow_J2_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    I1416QRow .J2 3 := by
  have h := Certificates.certificate13513
  obtain ⟨hvA, hvB⟩ := check_valid h
  have e : CFSG.Blueprint.NativeSporadic.J2 ≃* ↥CFSG.Sporadic.Schreier.j2P :=
    CFSG.Sporadic.Schreier.j2PermEquiv
  exact qrow_three_of_check_1080 hOut hb j2S3Data h (CFSG.RankThree.Native.rep_of_validA hvA)
    (CFSG.RankThree.Native.rep_of_validA hvB) (e.symm.trans (hbr .J2).some)
    (@MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J2.isSimpleGroup_J2 e.symm)
    (by rw [show j2S3Data.ord = 604800 from rfl]; norm_num) (by decide +kernel)

theorem qcompOK_three_of_card_dvd_1080_or_504
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {Q : Type} [Group Q]
    [Finite Q] {k : Q} (hk3 : orderOf k = 3)
    (hk : Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 1080 ∨
      Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 504) : QCompOK 3 k := by
  rcases hk with hk | hk
  · exact qcompOK_three_of_card_dvd_1080 hb hk3 hk
  · intro I hI
    obtain ⟨hs, hnab⟩ := KDSpor.pSimple_simple_nonab Nat.prime_three hI
    haveI := hs
    have h3 : 3 * Nat.card (PSimple 3 I) ∣ 504 :=
      (prime_mul_card_pSimple_dvd_cent Nat.prime_three hk3 hI.1).trans hk
    have hd : Nat.card (PSimple 3 I) ∣ 168 :=
      Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) (h3.trans (by norm_num))
    exact qtypeOK_three_of_card_168 hnab (card_eq_168_of_dvd hnab hd)

theorem qrow_three_of_check_1080_504 {s : TauCeti.SporadicName}
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (D : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.Data)
    (hD : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check D = true)
    {A B : Equiv.Perm (Fin D.n)}
    (hA : CFSG.Monster.B.Co2.Rep D.n D.A A) (hB : CFSG.Monster.B.Co2.Rep D.n D.B B)
    (b : ↥(Subgroup.closure {A, B}) ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hs : IsSimpleGroup ↥(Subgroup.closure {A, B})) (hpr : ¬ D.ord.Prime)
    (hsmall : ∀ c < D.cases.size, D.cases[c]!.card ∣ 1080 ∨ D.cases[c]!.card ∣ 504) :
    I1416QRow s 3 := by
  obtain ⟨hcardP, hcls⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check_card_order_sound D hA hB hD
  refine qrow_of_model hOut b
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hcardP]; exact hpr))
    fun x hx => ?_
  have hx3 : orderOf (x : Equiv.Perm (Fin D.n)) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨c, hc, hcc⟩ := hcls x x.2 hx3
  refine qcompOK_three_of_card_dvd_1080_or_504 hb hx ?_
  have hmapc := CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype
    (Subgroup.closure {A, B}) x
  have hcc' : Nat.card (Subgroup.centralizer ({x} : Set ↥(Subgroup.closure {A, B}))) =
      Nat.card ↥(Subgroup.centralizer ({(x : Equiv.Perm (Fin D.n))} : Set (Equiv.Perm (Fin D.n))) ⊓
        Subgroup.closure {A, B}) := by
    rw [← hmapc, Subgroup.card_map_of_injective (Subgroup.closure {A, B}).subtype_injective]
  rw [hcc', hcc]
  exact hsmall c hc

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem qrow_M24_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    I1416QRow .M24 3 :=
  qrow_three_of_check_1080_504 hOut hb m24S3Data Certificates.certificate13512 rep_m24A
    rep_m24B (hbr .M24).some CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
    (by rw [show m24S3Data.ord = 244823040 from rfl]; norm_num) (by decide +kernel)

end CFSG.LocalAnalysis.GLTheoremA.I1416QRows

