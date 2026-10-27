module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144IOutTri
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsUni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsSympA6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T14
public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRoot

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K144I

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup PerfectInLayer
  glaPComponent_map_fixSubgroup glaPComponent_isComponent_of_le_layer)
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel centerQuotAut centerQuotAut_mk
  center_centerQuot_eq_bot)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagKind FieldKind FamExc)
open CFSG.LocalAnalysis.GLTheoremA.K144 (I144OutFact I144Cat)

theorem card_pSimple_dvd_card {G : Type} [Group G] (p : ℕ) (X : Subgroup G) :
    Nat.card (PSimple p X) ∣ Nat.card ↥X :=
  (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _)

theorem canonLabel_of_tag_triD4 {lab : GLALabel} (h : lab.tag = .triD4) : canonLabel lab = lab := by
  obtain ⟨t, r, n⟩ := lab
  cases h
  rfl

theorem canonLabel_of_tag_D_four {lab : GLALabel} (h : lab.tag = .D) (hr : lab.rank = 4) :
    canonLabel lab = lab := by
  obtain ⟨t, r, n⟩ := lab
  cases h
  cases hr
  simp [canonLabel]

theorem n_eq_one_of_fieldRel {cK cJ : GLALabel}
    (hJ : cJ = ⟨.twA, 3, 1⟩ ∨ cJ = ⟨.twA, 4, 1⟩ ∨ cJ = ⟨.B, 3, 1⟩)
    (hK : cK.tag = .triD4 ∨ cK.tag = .D) (h : FieldRel 3 cK cJ) : cK.n = 1 := by
  have hJn : cJ.n = 1 := by rcases hJ with rfl | rfl | rfl <;> rfl
  have hJt : cJ.tag ≠ .triD4 ∧ cJ.tag ≠ .D := by
    rcases hJ with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
  rcases h with h | ⟨-, ⟨ht, -⟩ | ⟨-, -, -, ht⟩⟩
  · rw [hJn] at h
    exact Nat.dvd_one.1 h
  · rcases hK with hK | hK
    · exact absurd (ht.symm.trans hK) hJt.1
    · exact absurd (ht.symm.trans hK) hJt.2
  · exact absurd ht hJt.1

section Holds


theorem i144OutFact_holds : I144OutFact := by
  intro K _ _ α J hK hchev hα3 hJ hcat hnot
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hqK := isQuasisimple_of_openQuasisimple hK
  have hsimple : IsSimpleGroup (K ⧸ Subgroup.center K) := hqK.2.1
  have hna : ∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a := hqK.2.2
  have hcen : Subgroup.center (K ⧸ Subgroup.center K) = ⊥ := center_centerQuot_eq_bot hK
  have hβ3 : centerQuotAut K α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  haveI : Group.IsPerfect K := ⟨hK.1⟩
  have hSperf : commutator (K ⧸ Subgroup.center K) = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center K))
      (QuotientGroup.mk'_surjective _)).commutator_eq_top
  have hXS : HasLabel (K ⧸ Subgroup.center K) (fun _ => True) :=
    CFSG.StandardType.largeEvenMarking_of_isChevSimple hSperf hsimple hna hchev
  obtain ⟨labK, -, hXSK⟩ := exists_label_of_hasLabel hXS
  set π := QuotientGroup.mk' (Subgroup.center K) with hπ
  have hJb : GLAPComponent 3 (fixSubgroup (centerQuotAut K α)) (J.map π) :=
    glaPComponent_map_fixSubgroup π (by rw [QuotientGroup.ker_mk']) α (centerQuotAut K α)
      (fun k => (centerQuotAut_mk K α k).symm) (QuotientGroup.mk'_surjective _) hp3 hJ
  obtain ⟨eJ⟩ := nonempty_pSimple_equiv_map hp3 π hJ hJb
  have hcatJb : catalogIs (PSimple 3 (J.map π)) I144Cat := (catalogIs_congr eJ).1 hcat
  have h5J : 5 ∣ Nat.card ↥(J.map π) :=
    (five_dvd_card_of_i144Cat hcatJb).trans (card_pSimple_dvd_card 3 _)
  have h5fix : 5 ∣ Nat.card ↥(fixSubgroup (centerQuotAut K α)) :=
    h5J.trans (Subgroup.card_dvd_of_le hJb.1)
  have h5S : 5 ∣ Nat.card (K ⧸ Subgroup.center K) :=
    h5fix.trans (Subgroup.card_subgroup_dvd_card _)
  have hpil : PerfectInLayer (centerQuotAut K α) := by
    by_cases hβ1 : centerQuotAut K α = 1
    · rw [hβ1]
      exact perfectInLayer_one_of_simple hsimple hna
    rcases hchev with hlie | hamb
    · obtain ⟨d, hv, hd2, ⟨e⟩⟩ := exists_lieIndex_of_catalogIs_onLie hlie
      have hd2' : d.characteristic = 2 := hd2
      have hpd : (3 : ℕ) ≠ (⟨d, hv⟩ : TauCeti.ValidLieTypeIndex).1.characteristic := by
        show (3 : ℕ) ≠ d.characteristic
        rw [hd2']
        norm_num
      exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent _ hsimple hna
        ⟨d, hv⟩ ⟨e⟩ 3 hp3 (by norm_num) hpd _ hβ3 hβ1
    ·
      exfalso
      have hsmall := I91T.card_mem_ambiguous hamb
      have hge : 25920 ≤ Nat.card (PSimple 3 (J.map π)) := by
        rcases card_of_i144Cat hcatJb with h | h | h <;> rw [h] <;> norm_num
      have hdvd : Nat.card (PSimple 3 (J.map π)) ∣ Nat.card (K ⧸ Subgroup.center K) :=
        ((card_pSimple_dvd_card 3 _).trans (Subgroup.card_dvd_of_le hJb.1)).trans
          (Subgroup.card_subgroup_dvd_card _)
      have hle := Nat.le_of_dvd Nat.card_pos hdvd
      omega
  have hJle := hpil _ hJb.1 (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJb)
  have hJc := (glaPComponent_isComponent_of_le_layer hJb hJle).1
  obtain ⟨eA⟩ := chev2_quot_equiv hp3 hJb hJc.2.2
  have hcatb : catalogIs (↥(J.map π) ⧸ Subgroup.center ↥(J.map π)) I144Cat :=
    (catalogIs_congr eA).2 hcatJb
  obtain ⟨labJ, hlabJ, hJL⟩ := i144Cat_label_cases hJc.2.2 hcatb
  have hcJ : canonLabel labJ = labJ := by rcases hlabJ with rfl | rfl | rfl <;> rfl
  by_cases hin : InnDiagKind (K ⧸ Subgroup.center K) labK (centerQuotAut K α)
  · exact absurd (i144Inner_of_innDiagKind hK hin) hnot
  by_cases htri : labK.tag = .triD4
  ·
    exfalso
    have hfam : FamExc labK := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl htri)))))
    rcases Y10GClsExc.clsExc_holds _ 3 (centerQuotAut K α) labK hfam hp3 (by norm_num) hcen hXSK
      hβ3 with h | hfld
    · exact hin h
    have hFR := Y10GTri.triFieldTD4_holds _ (centerQuotAut K α) (J.map π) labK labJ htri hcen hXSK
      hfld hβ3 hJL hJb
    rw [canonLabel_of_tag_triD4 htri, hcJ] at hFR
    have hn1 := n_eq_one_of_fieldRel hlabJ (Or.inl htri) hFR
    obtain ⟨t, r, n⟩ := labK
    have ht : t = .triD4 := htri
    have hn : n = 1 := hn1
    subst ht
    subst hn
    have hcard := card_of_hasLabel_triD4_one hXSK
    have hiso : Nat.card ((K ⧸ Subgroup.center K) ⧸ Subgroup.center (K ⧸ Subgroup.center K)) =
        Nat.card (K ⧸ Subgroup.center K) :=
      Nat.card_congr
        ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).toEquiv
    rw [hiso] at hcard
    rw [hcard] at h5S
    norm_num at h5S
  by_cases hfld : FieldKind (K ⧸ Subgroup.center K) labK (centerQuotAut K α)
  · exact primeField_of_fieldKind hK hα3 htri hfld
  exfalso
  rcases Y10GField.cls_of_families Y10GField.ClsLin_holds Y10GField.ClsUni_holds
    Y10GField.ClsSymp_holds Y10GClsOrth.clsOrth_holds Y10GClsExc.clsExc_holds _ 3
    (centerQuotAut K α) labK hp3 (by norm_num) hcen hXSK hβ3 with h | h | ⟨hD, hr4, -⟩
  · exact hin h
  · exact hfld h
  have hFR := Y10GTri.triOuterD4_holds _ (centerQuotAut K α) (J.map π) labK labJ hD hr4 hcen hXSK
    hin hfld hβ3 hJL hJb
  rw [canonLabel_of_tag_D_four hD hr4, hcJ] at hFR
  have hn1 := n_eq_one_of_fieldRel hlabJ (Or.inr hD) hFR
  obtain ⟨t, r, n⟩ := labK
  have ht : t = .D := hD
  have hr : r = 4 := hr4
  have hn : n = 1 := hn1
  subst ht
  subst hr
  subst hn
  exact not_five_dvd_card_fixSubgroup_D4_two hcen hXSK hin hfld hβ3 h5fix

end Holds

end CFSG.LocalAnalysis.GLTheoremA.K144I

end
