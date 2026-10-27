module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporOrder120
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporTh7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporAut168
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Data
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I1416Rows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA

theorem typeOK_three_of_card_dvd_360
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {T : Type} [Group T]
    [Finite T] [IsSimpleGroup T] (hnab : ∃ a b : T, a * b ≠ b * a) (hd : Nat.card T ∣ 360) :
    TypeOK 3 T := by
  intro hC h9 _
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
  rcases hcases with h | h | hrest
  · exfalso
    obtain ⟨fA⟩ := CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h
    obtain ⟨e'⟩ := CFSG.GH74.KGroups.A5.equiv_of_alt fA
    rw [CFSG.GH74.KGroups.A5.card_mulAut e'] at h9
    norm_num at h9
  · exact (hns (CFSG.LocalAnalysis.GLTheoremA.KDSpor.isSolvable_of_card_eq Nat.prime_two
      Nat.prime_three (by norm_num) (a := 3) (b := 2) (by rw [h]; norm_num))).elim
  ·
    have hlie : ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 →
        Nonempty (T ≃* (TauCeti.CFSGIndex.lie d).Group) → False := by
      intro d hd2 he
      have hn := hb d T he
      obtain ⟨v, M, hv, hM⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.lie_char_part d.1 d.2
      rw [hd2] at hv hM
      rcases hrest with h | h | h | h
      · rw [h] at hn
        have hv8 : v < 8 := by
          by_contra hv8
          have : 2 ^ 8 ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) (by omega)
          have hM0 : 0 < M := by rcases Nat.eq_zero_or_pos M with h0 | h0 <;> simp_all
          nlinarith
        interval_cases v <;> omega
      · exact Order120.lieOrderFormula_ne_120 d.2 (hn.symm.trans h)
      · rw [h] at hn
        have hv8 : v < 8 := by
          by_contra hv8
          have : 2 ^ 8 ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) (by omega)
          have hM0 : 0 < M := by rcases Nat.eq_zero_or_pos M with h0 | h0 <;> simp_all
          nlinarith
        interval_cases v <;> omega
      · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieOrderFormula_ne_360 d.2
          (hn.symm.trans h)
    rcases hC with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
    · cases i with
      | lie d => exact (hlie d hi ⟨e⟩).elim
      | _ => exact hi.elim
    · cases i with
      | lie d =>
        exfalso
        have hn := hb d T ⟨e⟩
        have hval := CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.amb_lie_order 2 d.1 d.2 hi
        rcases hrest with h | h | h | h <;> rw [h] at hn <;> rcases hval with h' | h' | h' | h' <;>
          omega
      | alternating n hn5 =>
        have hcn : Nat.card T = n.factorial / 2 :=
          (Nat.card_congr e.toEquiv).trans
            (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt n (by omega))
        have hn6 : n = 6 := by
          rcases Nat.lt_or_ge n 7 with hlt | hge
          · interval_cases n <;> simp [Nat.factorial] at hcn <;> omega
          · have h7 : Nat.factorial 7 ∣ n.factorial := Nat.factorial_dvd_factorial hge
            have : 2520 ≤ n.factorial / 2 := by
              have := Nat.le_of_dvd (Nat.factorial_pos n) h7
              simp [Nat.factorial] at this
              omega
            rcases hrest with h | h | h | h <;> omega
        subst hn6
        exact ⟨rfl, TauCeti.CFSGIndex.alternating 6 hn5, Or.inl rfl, ⟨e⟩⟩
      | _ => exact hi.elim

theorem compOK_three_of_card_dvd_1080
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {Q : Type} [Group Q]
    [Finite Q] {k : Q} (hk3 : orderOf k = 3)
    (hk : Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 1080) : CompOK 3 k := by
  intro I hI
  obtain ⟨hs, hnab⟩ := KDSpor.pSimple_simple_nonab Nat.prime_three hI
  haveI := hs
  have h3 : 3 * Nat.card (PSimple 3 I) ∣ 1080 :=
    (prime_mul_card_pSimple_dvd_cent Nat.prime_three hk3 hI.1).trans hk
  exact typeOK_three_of_card_dvd_360 hb hnab
    (Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) (h3.trans (by norm_num)))

theorem row_three_of_check_1080 {s : TauCeti.SporadicName}
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (D : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.Data)
    (hD : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check D = true)
    {A B : Equiv.Perm (Fin D.n)}
    (hA : CFSG.Monster.B.Co2.Rep D.n D.A A) (hB : CFSG.Monster.B.Co2.Rep D.n D.B B)
    (b : ↥(Subgroup.closure {A, B}) ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hs : IsSimpleGroup ↥(Subgroup.closure {A, B})) (hpr : ¬ D.ord.Prime)
    (hsmall : ∀ c < D.cases.size, D.cases[c]!.card ∣ 1080) : I1416SporRow s 3 := by
  obtain ⟨hcardP, hcls⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check_card_order_sound D hA hB hD
  refine row_of_model hOut b
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hcardP]; exact hpr))
    fun x hx => ?_
  have hx3 : orderOf (x : Equiv.Perm (Fin D.n)) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨c, hc, hcc⟩ := hcls x x.2 hx3
  refine compOK_three_of_card_dvd_1080 hb hx ?_
  have hmapc := CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype
    (Subgroup.closure {A, B}) x
  have hcc' : Nat.card (Subgroup.centralizer ({x} : Set ↥(Subgroup.closure {A, B}))) =
      Nat.card ↥(Subgroup.centralizer ({(x : Equiv.Perm (Fin D.n))} : Set (Equiv.Perm (Fin D.n))) ⊓
        Subgroup.closure {A, B}) := by
    rw [← hmapc, Subgroup.card_map_of_injective (Subgroup.closure {A, B}).subtype_injective]
  rw [hcc', hcc]
  exact hsmall c hc

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem row_J2_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    I1416SporRow .J2 3 := by
  have h := Certificates.certificate13513
  obtain ⟨hvA, hvB⟩ := check_valid h
  have e : CFSG.Blueprint.NativeSporadic.J2 ≃* ↥CFSG.Sporadic.Schreier.j2P :=
    CFSG.Sporadic.Schreier.j2PermEquiv
  exact row_three_of_check_1080 hOut hb j2S3Data h (CFSG.RankThree.Native.rep_of_validA hvA)
    (CFSG.RankThree.Native.rep_of_validA hvB) (e.symm.trans (hbr .J2).some)
    (@MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J2.isSimpleGroup_J2 e.symm)
    (by rw [show j2S3Data.ord = 604800 from rfl]; norm_num) (by decide +kernel)

end CFSG.LocalAnalysis.GLTheoremA.I1416Rows

namespace CFSG.LocalAnalysis.GLTheoremA.I1416Rows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA

theorem typeOK_three_of_card_168 {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hnab : ∃ a b : T, a * b ≠ b * a) (hc : Nat.card T = 168) : TypeOK 3 T :=
  fun _ h9 _ => absurd h9 (not_sq_three_dvd_card_mulAut_of_card_168 hnab hc)

theorem compOK_three_of_card_dvd_1080_or_504
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {Q : Type} [Group Q]
    [Finite Q] {k : Q} (hk3 : orderOf k = 3)
    (hk : Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 1080 ∨
      Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 504) : CompOK 3 k := by
  rcases hk with hk | hk
  · exact compOK_three_of_card_dvd_1080 hb hk3 hk
  · intro I hI
    obtain ⟨hs, hnab⟩ := KDSpor.pSimple_simple_nonab Nat.prime_three hI
    haveI := hs
    have h3 : 3 * Nat.card (PSimple 3 I) ∣ 504 :=
      (prime_mul_card_pSimple_dvd_cent Nat.prime_three hk3 hI.1).trans hk
    have hd : Nat.card (PSimple 3 I) ∣ 168 :=
      Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) (h3.trans (by norm_num))
    exact typeOK_three_of_card_168 hnab (card_eq_168_of_dvd hnab hd)

theorem row_three_of_check_1080_504 {s : TauCeti.SporadicName}
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (D : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.Data)
    (hD : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check D = true)
    {A B : Equiv.Perm (Fin D.n)}
    (hA : CFSG.Monster.B.Co2.Rep D.n D.A A) (hB : CFSG.Monster.B.Co2.Rep D.n D.B B)
    (b : ↥(Subgroup.closure {A, B}) ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hs : IsSimpleGroup ↥(Subgroup.closure {A, B})) (hpr : ¬ D.ord.Prime)
    (hsmall : ∀ c < D.cases.size, D.cases[c]!.card ∣ 1080 ∨ D.cases[c]!.card ∣ 504) :
    I1416SporRow s 3 := by
  obtain ⟨hcardP, hcls⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check_card_order_sound D hA hB hD
  refine row_of_model hOut b
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hcardP]; exact hpr))
    fun x hx => ?_
  have hx3 : orderOf (x : Equiv.Perm (Fin D.n)) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨c, hc, hcc⟩ := hcls x x.2 hx3
  refine compOK_three_of_card_dvd_1080_or_504 hb hx ?_
  have hmapc := CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype
    (Subgroup.closure {A, B}) x
  have hcc' : Nat.card (Subgroup.centralizer ({x} : Set ↥(Subgroup.closure {A, B}))) =
      Nat.card ↥(Subgroup.centralizer ({(x : Equiv.Perm (Fin D.n))} : Set (Equiv.Perm (Fin D.n))) ⊓
        Subgroup.closure {A, B}) := by
    rw [← hmapc, Subgroup.card_map_of_injective (Subgroup.closure {A, B}).subtype_injective]
  rw [hcc', hcc]
  exact hsmall c hc

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem row_M24_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    I1416SporRow .M24 3 :=
  row_three_of_check_1080_504 hOut hb m24S3Data Certificates.certificate13512 rep_m24A
    rep_m24B (hbr .M24).some CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
    (by rw [show m24S3Data.ord = 244823040 from rfl]; norm_num) (by decide +kernel)

end CFSG.LocalAnalysis.GLTheoremA.I1416Rows
