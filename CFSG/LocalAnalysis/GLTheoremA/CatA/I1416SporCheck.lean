module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporRows
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Data

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I1416Rows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA

theorem three_mul_card_pSimple_dvd_cent {S : Type} [Group S] [Finite S] {k : S}
    (hk : orderOf k = 3) {J : Subgroup S} (hJ : J ≤ Subgroup.centralizer ({k} : Set S)) :
    3 * Nat.card (PSimple 3 J) ∣ Nat.card (Subgroup.centralizer ({k} : Set S)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hkc : ∀ g ∈ J, g * k = k * g := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.1 (hJ hg)
  by_cases hkJ : k ∈ J
  · set k' : ↥J := ⟨k, hkJ⟩
    set kb : PQuot 3 J := (QuotientGroup.mk k' : PQuot 3 J) with hkb
    have hZ : kb ∈ Subgroup.center (PQuot 3 J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
      rw [hkb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hkc g g.2)
    have hk'3 : orderOf k' = 3 := by
      rw [← Subgroup.orderOf_coe]
      exact hk
    have hkb1 : kb ≠ 1 := by
      intro h
      have hmem : k' ∈ GLAPPrimeCore 3 ↥J := (QuotientGroup.eq_one_iff k').1 h
      have h3 := Subgroup.orderOf_dvd_natCard _ hmem
      rw [hk'3] at h3
      have hcop := GL83.PiGen.coprime_card_glaPPrimeCore Nat.prime_three ↥J
      exact absurd (Nat.Coprime.coprime_dvd_right h3 hcop) (by norm_num)
    have hkb3 : orderOf kb = 3 := by
      refine orderOf_eq_prime ?_ hkb1
      rw [hkb, ← QuotientGroup.mk_pow, ← hk'3, pow_orderOf_eq_one, QuotientGroup.mk_one]
    have h3Z := Subgroup.orderOf_dvd_natCard _ hZ
    rw [hkb3] at h3Z
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (PQuot 3 J))
    have h2 : Nat.card (PQuot 3 J) ∣ Nat.card J := Subgroup.card_quotient_dvd_card _
    have h3 : Nat.card J ∣ Nat.card (Subgroup.centralizer ({k} : Set S)) :=
      Subgroup.card_dvd_of_le hJ
    refine Dvd.dvd.trans ?_ (h2.trans h3)
    rw [h1, mul_comm]
    exact Nat.mul_dvd_mul_left _ h3Z
  · have hN : Subgroup.zpowers k ≤ Subgroup.normalizer (J : Set S) := by
      rw [Subgroup.zpowers_le]
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · intro hg
        have : k * g * k⁻¹ = g := by rw [← hkc g hg]; group
        rw [this]; exact hg
      · intro hg
        have hg' : k⁻¹ * (k * g * k⁻¹) * k ∈ J := by
          have hx := hkc _ hg
          have : k⁻¹ * (k * g * k⁻¹) * k = k * g * k⁻¹ := by
            calc k⁻¹ * (k * g * k⁻¹) * k = k⁻¹ * ((k * g * k⁻¹) * k) := by group
              _ = k⁻¹ * (k * (k * g * k⁻¹)) := by rw [hx]
              _ = k * g * k⁻¹ := by group
          rw [this]; exact hg
        have : k⁻¹ * (k * g * k⁻¹) * k = g := by group
        rwa [this] at hg'
    have hb : Subgroup.zpowers k ⊓ J = ⊥ := by
      have hd : Nat.card ↥(Subgroup.zpowers k ⊓ J) ∣ 3 := by
        rw [← hk, ← Nat.card_zpowers]
        exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
      · exact Subgroup.card_eq_one.1 h
      · exfalso
        have heq : Subgroup.zpowers k ⊓ J = Subgroup.zpowers k :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [Nat.card_zpowers, hk, h])
        exact hkJ ((heq ▸ inf_le_right : Subgroup.zpowers k ≤ J) (Subgroup.mem_zpowers k))
    have hc := CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.card_sup_of_inf_bot hN hb
    rw [Nat.card_zpowers, hk] at hc
    calc 3 * Nat.card (PSimple 3 J) ∣ 3 * Nat.card J := Nat.mul_dvd_mul_left 3 (KDL227Rows.card_pSimple_dvd 3 J)
      _ = Nat.card ↥(Subgroup.zpowers k ⊔ J) := hc.symm
      _ ∣ Nat.card (Subgroup.centralizer ({k} : Set S)) :=
        Subgroup.card_dvd_of_le (sup_le (Subgroup.zpowers_le.2
          (Subgroup.mem_centralizer_singleton_iff.2 rfl)) hJ)

theorem compOK_three_of_card_dvd_360 {Q : Type} [Group Q]
    [Finite Q] {k : Q} (hk3 : orderOf k = 3)
    (hk : Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 360) : CompOK 3 k := by
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
  exact typeOK_A5 (Or.inl rfl) fA

theorem row_three_of_check {s : TauCeti.SporadicName}
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (D : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.Data)
    (hD : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check D = true)
    {A B : Equiv.Perm (Fin D.n)}
    (hA : CFSG.Monster.B.Co2.Rep D.n D.A A) (hB : CFSG.Monster.B.Co2.Rep D.n D.B B)
    (b : ↥(Subgroup.closure {A, B}) ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hs : IsSimpleGroup ↥(Subgroup.closure {A, B})) (hpr : ¬ D.ord.Prime)
    (hsmall : ∀ c < D.cases.size, D.cases[c]!.card ∣ 360) : I1416SporRow s 3 := by
  obtain ⟨hcardP, hcls⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check_card_order_sound D hA hB hD
  refine row_of_model hOut b
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hcardP]; exact hpr))
    fun x hx => ?_
  have hx3 : orderOf (x : Equiv.Perm (Fin D.n)) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨c, hc, hcc⟩ := hcls x x.2 hx3
  refine compOK_three_of_card_dvd_360 hx ?_
  have hmapc := CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype
    (Subgroup.closure {A, B}) x
  have hcc' : Nat.card (Subgroup.centralizer ({x} : Set ↥(Subgroup.closure {A, B}))) =
      Nat.card ↥(Subgroup.centralizer ({(x : Equiv.Perm (Fin D.n))} : Set (Equiv.Perm (Fin D.n))) ⊓
        Subgroup.closure {A, B}) := by
    rw [← hmapc, Subgroup.card_map_of_injective (Subgroup.closure {A, B}).subtype_injective]
  rw [hcc', hcc]
  exact hsmall c hc

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem row_M23_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    I1416SporRow .M23 3 :=
  row_three_of_check hOut m23S3Data Certificates.certificate13511.2.2.2 rep_m23A rep_m23B
    (hbr .M23).some CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2
    (by rw [show m23S3Data.ord = 10200960 from rfl]; norm_num) (by decide +kernel)

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem row_HS_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    I1416SporRow .HS 3 := by
  have h := Certificates.certificate13514
  obtain ⟨hvA, hvB⟩ := check_valid h
  have e : CFSG.Blueprint.NativeSporadic.HS ≃* ↥CFSG.Sporadic.Schreier.hsP :=
    CFSG.Sporadic.Schreier.hsPermEquiv
  exact row_three_of_check hOut hsS3Data h (CFSG.RankThree.Native.rep_of_validA hvA)
    (CFSG.RankThree.Native.rep_of_validA hvB) (e.symm.trans (hbr .HS).some)
    (@MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.HS.isSimpleGroup_HS e.symm)
    (by rw [show hsS3Data.ord = 44352000 from rfl]; norm_num) (by decide +kernel)

end CFSG.LocalAnalysis.GLTheoremA.I1416Rows
