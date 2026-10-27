module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CentralizerEleven
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixPrimes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvClasses
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.SqClass
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableISpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongrK

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup

theorem card_centralizer_P_eq (t : ↥P1408) :
    Nat.card ↥(centralizer ({t} : Set ↥P1408)) =
      Nat.card ↥(P1408 ⊓ centralizer ({(t : Equiv.Perm (Fin 1408))} :
        Set (Equiv.Perm (Fin 1408)))) :=
  Nat.card_congr (centralizerSubtypeEquiv P1408 t).toEquiv

theorem card_centralizer_of_primeFacts {p : ℕ} {ds : List FixData} (hF : PrimeFacts p ds)
    {t : ↥P1408} (ht : orderOf t = p) :
    ∃ d ∈ ds, IsConj (repP d) t ∧ Nat.card ↥(centralizer ({t} : Set ↥P1408)) = d.centOrder := by
  obtain ⟨d, hd, hc⟩ := hF.2 t ht
  refine ⟨d, hd, hc, ?_⟩
  rw [card_centralizer_eq_of_isConj hc, card_centralizer_P_eq]
  exact (hF.1 d hd).1

theorem card_centralizer_of_classSpec {r : WClass} {t : ↥P1408} {s : Equiv.Perm (Fin 1408)}
    (hts : (t : Equiv.Perm (Fin 1408)) = s) (h : ClassSpec r s) :
    Nat.card ↥(centralizer ({t} : Set ↥P1408)) = r.centOrder := by
  rw [card_centralizer_P_eq, hts, h.cent_card]

section Cert


theorem pA_comm (g : ↥P1408) : g * pA = pA * g := Subtype.ext (elemA_comm g.2).symm

private theorem not_dvd_centralizer_involution (hP : Nat.card ↥P1408 = 177408000) {e : ↥P1408}
    (he : orderOf e = 2) (hne : e ≠ pA) : ¬ 11 ∣ Nat.card ↥(centralizer ({e} : Set ↥P1408)) := by
  obtain ⟨hz, haz, hb, hz₁⟩ := invClasses_classSpec hP
  obtain ⟨i, hi⟩ := involution_cover_inv hP e he
  fin_cases i
  · change IsConj pA e at hi
    obtain ⟨c, hc⟩ := isConj_iff.1 hi
    refine absurd ?_ hne
    rw [← hc, pA_comm c, mul_assoc, mul_inv_cancel, mul_one]
  · change IsConj pZ e at hi
    rw [card_centralizer_eq_of_isConj hi, card_centralizer_of_classSpec (t := pZ) rfl hz]
    decide
  · change IsConj (pA * pZ) e at hi
    rw [card_centralizer_eq_of_isConj hi, card_centralizer_of_classSpec (t := (pA * pZ)) rfl haz]
    decide
  · change IsConj pB e at hi
    rw [card_centralizer_eq_of_isConj hi, card_centralizer_of_classSpec (t := pB) rfl hb]
    decide
  · change IsConj pZ₁ e at hi
    rw [card_centralizer_eq_of_isConj hi, card_centralizer_of_classSpec (t := pZ₁) rfl hz₁]
    decide

theorem table_eleven_P (hP : Nat.card ↥P1408 = 177408000) (t : ↥P1408) (ht : orderOf t = 11) :
    IsShapeCentralizerEleven ↥(centralizer ({t} : Set ↥P1408)) := by
  haveI : Finite ↥P1408 := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  refine TwoHSData.centralizer_eleven_of_data pA (by rw [hP]; norm_num)
    (Subtype.ext elemA_mul_self)
    (fun h => ne_one_of_orderOf_eq_two twoHSBasic_spec.1 (congrArg Subtype.val h))
    pA_comm ?_ ?_ ?_ ?_ ?_ t ht
  · intro e he
    obtain ⟨d, hd, -, hcard⟩ := card_centralizer_of_primeFacts (primeFacts3 hP) he
    obtain rfl : d = fix3 := by simpa using hd
    rw [hcard]
    decide
  · intro e he
    obtain ⟨d, hd, -, hcard⟩ := card_centralizer_of_primeFacts (primeFacts5 hP) he
    rw [hcard]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> decide
  · intro e he
    obtain ⟨d, hd, -, hcard⟩ := card_centralizer_of_primeFacts (primeFacts7 hP) he
    obtain rfl : d = fix7 := by simpa using hd
    rw [hcard]
    decide
  · intro e he hne
    exact not_dvd_centralizer_involution hP he hne
  · intro g hg
    rw [card_centralizer_sq hP (by rw [pow_two]; exact hg)]
    decide

end Cert

end CFSG.EvenSporadicStandard.HNRecog
