module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeVSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCard
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeIITrue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ElevenP
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.SylowTwoFive
public import Certificates.Certificate441601

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup

private theorem factorization_80640_five : (80640 : ℕ).factorization 5 = 1 := by
  rw [show (80640 : ℕ) = 5 * 16128 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_five,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

private theorem orderOf_conj_inv {G : Type*} [Group G] (c x : G) :
    orderOf (c⁻¹ * x * c) = orderOf x := by
  simpa using orderOf_injective (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective x

section Cert


theorem shapesVOK_true : shapesVOK = true := Certificates.certificate441601

private theorem shapesV_parts : shapeD5OK = true ∧ shapeUOK = true ∧ shapeA8OK = true := by
  have h := shapesVOK_true
  simp only [shapesVOK, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem isConj_pB_of_card_centralizer (hP : Nat.card ↥P1408 = 177408000) {e : ↥P1408}
    (he : orderOf e = 2) (hcard : Nat.card ↥(centralizer ({e} : Set ↥P1408)) = 80640) :
    IsConj pB e := by
  obtain ⟨hz, haz, hb, hz₁⟩ := invClasses_classSpec hP
  obtain ⟨i, hi⟩ := involution_cover_inv hP e he
  fin_cases i
  · change IsConj pA e at hi
    obtain ⟨c, hc⟩ := isConj_iff.1 hi
    have hec : e = pA := by rw [← hc, pA_comm c, mul_assoc, mul_inv_cancel, mul_one]
    have hall : centralizer ({e} : Set ↥P1408) = ⊤ := by
      rw [hec, eq_top_iff]
      intro g _
      exact mem_centralizer_singleton_iff.2 (pA_comm g)
    rw [hall, Subgroup.card_top, hP] at hcard
    exact absurd hcard (by norm_num)
  · change IsConj pZ e at hi
    rw [card_centralizer_eq_of_isConj hi, card_centralizer_of_classSpec (t := pZ) rfl hz] at hcard
    exact absurd hcard (by decide)
  · change IsConj (pA * pZ) e at hi
    rw [card_centralizer_eq_of_isConj hi,
      card_centralizer_of_classSpec (t := pA * pZ) rfl haz] at hcard
    exact absurd hcard (by decide)
  · change IsConj pB e at hi
    exact hi
  · change IsConj pZ₁ e at hi
    rw [card_centralizer_eq_of_isConj hi, card_centralizer_of_classSpec (t := pZ₁) rfl hz₁] at hcard
    exact absurd hcard (by decide)

theorem sl25_le_centralizer_P (hP : Nat.card ↥P1408 = 177408000) (ρ : ↥P1408)
    (hρ : orderOf ρ = 5) (hC : IsShapeCentralizerFiveC ↥(centralizer ({ρ} : Set ↥P1408))) :
    ∃ S : Subgroup ↥(centralizer ({ρ} : Set ↥P1408)),
      Nonempty (↥S ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := by
  obtain ⟨d, hd, hconj, hcard⟩ := card_centralizer_of_primeFacts (primeFacts5 hP) hρ
  rw [hC.card_eq] at hcard
  obtain rfl : d = fix5C := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact absurd hcard (by decide)
    · exact absurd hcard (by decide)
    · rfl
  obtain ⟨e⟩ := nonempty_centralizer_mulEquiv_of_isConj hconj
  obtain ⟨D, hD, hDe⟩ := shapeD5OK_spec shapesV_parts.1
  exact exists_subgroup_mulEquiv_of_le hD
    ((centralizerSubtypeEquiv P1408 (repP fix5C)).symm.trans e) hDe

theorem sylow_two_five_P (hP : Nat.card ↥P1408 = 177408000) (ρ : ↥P1408) (hρ : orderOf ρ = 5)
    (hB : IsShapeCentralizerFiveB ↥(centralizer ({ρ} : Set ↥P1408)))
    (T : Sylow 2 ↥(centralizer ({ρ} : Set ↥P1408))) :
    ∃ u : ↥P1408, IsConj pZ₁ u ∧
      (T : Subgroup ↥(centralizer ({ρ} : Set ↥P1408))).map
        (centralizer ({ρ} : Set ↥P1408)).subtype = closure ({pA, u} : Set ↥P1408) := by
  haveI : Finite ↥P1408 := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  obtain ⟨d, hd, hconj, hcard⟩ := card_centralizer_of_primeFacts (primeFacts5 hP) hρ
  have h100 := hB.card_eq
  rw [h100] at hcard
  obtain rfl : d = fix5B := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact absurd hcard (by decide)
    · rfl
    · exact absurd hcard (by decide)
  obtain ⟨hu2, hu1, hua, hucomm, hc₀⟩ := shapeUOK_spec shapesV_parts.2.1
  have ha2 : pA * pA = 1 := Subtype.ext elemA_mul_self
  have ha1 : pA ≠ 1 := fun h => ne_one_of_orderOf_eq_two twoHSBasic_spec.1 (congrArg Subtype.val h)
  obtain ⟨u, hu2', hu1', hau, huρ, hz⟩ := exists_involution_of_isConj (a := pA) (z := pZ₁)
    (u₀ := (⟨elemW u0Word, elemW_mem _⟩ : ↥P1408)) hconj pA_comm (Subtype.ext hu2)
    (fun h => hu1 (congrArg Subtype.val h)) (fun h => hua (congrArg Subtype.val h))
    (Subtype.ext hucomm) (isConj_iff.2 ⟨⟨elemW c0Word, elemW_mem _⟩, Subtype.ext hc₀⟩)
  obtain ⟨u', hu', hT⟩ := TwoHSData.exists_conj_closure_of_sylow_two ha2 ha1 pA_comm hu2' hu1' hau
    huρ h100 T
  exact ⟨u', hz.trans hu', hT⟩

theorem centralizer_five_of_A8_P (hP : Nat.card ↥P1408 = 177408000) (c : ↥P1408)
    (hc : orderOf c = 2) (hA8 : IsShapeTwoTwoTimesA8 ↥(centralizer ({c} : Set ↥P1408)))
    (ρ : ↥P1408) (hρ : orderOf ρ = 5) (hρc : ρ * c = c * ρ) :
    IsShapeCentralizerFiveC ↥(centralizer ({ρ} : Set ↥P1408)) := by
  haveI : Finite ↥P1408 := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  have hcard := hA8.card_eq
  obtain ⟨x, hx⟩ := isConj_iff.1 (isConj_pB_of_card_centralizer hP hc hcard)
  have hρ'o : orderOf (x⁻¹ * ρ * x) = 5 := by rw [orderOf_conj_inv, hρ]
  have hρ'b : x⁻¹ * ρ * x * pB = pB * (x⁻¹ * ρ * x) :=
    calc x⁻¹ * ρ * x * pB = x⁻¹ * (ρ * (x * pB * x⁻¹)) * x := by group
      _ = x⁻¹ * (ρ * c) * x := by rw [hx]
      _ = x⁻¹ * (c * ρ) * x := by rw [hρc]
      _ = x⁻¹ * ((x * pB * x⁻¹) * ρ) * x := by rw [hx]
      _ = pB * (x⁻¹ * ρ * x) := by group
  obtain ⟨hrp5, hrpb, hconjs⟩ := shapeA8OK_spec shapesV_parts.2.2
  have hpB : Nat.card ↥(centralizer ({pB} : Set ↥P1408)) = 80640 := by
    obtain ⟨-, -, hb, -⟩ := invClasses_classSpec hP
    exact (card_centralizer_of_classSpec (t := pB) rfl hb).trans (by decide)
  have hmain : IsConj (repP fix5C) (x⁻¹ * ρ * x) := by
    refine isConj_of_mem_centralizer_of_orderOf_five (b := pB) (s := repP fix5C)
      (rp := (⟨elemW rpWord, elemW_mem _⟩ : ↥P1408)) ?_ (Subtype.ext hrpb)
      (by rw [hpB]; exact factorization_80640_five) ?_ hρ'o hρ'b
    · rw [← Subgroup.orderOf_coe]
      exact hrp5
    · intro k hk0 hk5
      obtain ⟨g, hg, hgk⟩ := hconjs k hk0 hk5
      exact isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext hgk⟩
  have hρconj : IsConj (repP fix5C) ρ :=
    hmain.trans (isConj_iff.2 ⟨x, by group⟩)
  obtain ⟨e⟩ := nonempty_centralizer_mulEquiv_of_isConj hρconj
  exact IsShapeCentralizerFiveC.of_mulEquiv e (isShape_repP_five_C hP)

end Cert

end CFSG.EvenSporadicStandard.HNRecog
