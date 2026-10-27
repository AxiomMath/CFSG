module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93IdNot2
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char
public import CFSG.Adapters.TauCetiLieModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.List93

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.CatLeaf (lieSylowExponent lieOrderNumerator lieOrderDivisor)

open CFSG.HardMathSupport.Solomon.Coordinator (sporOrd sporadicOrdersTable_holds)

open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)


section Certs



theorem not_chev2_of_card {T : Type} [Group T] {a m : ℕ} (hm : Odd m) (ha : 1 ≤ a)
    (hT : Nat.card T = 2 ^ a * m)
    (hamb : 2 ^ a * m ≠ 60 ∧ 2 ^ a * m ≠ 168 ∧ 2 ^ a * m ≠ 360 ∧ 2 ^ a * m ≠ 6048 ∧
      2 ^ a * m ≠ 20160)
    (hb : ∀ t ∈ lie2Tags, ∀ n ≤ a + 1, ∀ f ≤ a, lieSylowExponent t n * f = a →
      2 ^ a * m * lieOrderDivisor t n (2 ^ f) ≠ lieOrderNumerator t n (2 ^ f)) :
    ¬ IsChevSimple 2 T := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact absurd hm (by decide)
  haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; positivity)
  have hc60 : Nat.card T ≠ 60 := by rw [hT]; exact hamb.1
  have hc168 : Nat.card T ≠ 168 := by rw [hT]; exact hamb.2.1
  have hc360 : Nat.card T ≠ 360 := by rw [hT]; exact hamb.2.2.1
  have hc6048 : Nat.card T ≠ 6048 := by rw [hT]; exact hamb.2.2.2.1
  have hc20160 : Nat.card T ≠ 20160 := by rw [hT]; exact hamb.2.2.2.2
  have hfact : (Nat.card T).factorization 2 = a := by rw [hT]; exact fact2_two_pow_mul hm
  intro h
  rcases h with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | cyclic _ _ => exact hi.elim
    | alternating _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
    | lie d =>
      have hd : d.1.characteristic = 2 := hi
      obtain ⟨t, n, f, hL⟩ := CFSG.StandardType.ChevTwo.exists_lieModel_two_of_valid d hd e
      obtain ⟨-, hnum, hsyl⟩ := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput T t n
        2 f (CFSG.Blueprint.LieModel.admissible hL) hL
      have hsum : lieSylowExponent t n * f = a := by rw [← hsyl, hfact]
      exact chk_of_bounded ha hb t n f hsum (by rw [← hT]; exact hnum)
  · cases i with
    | cyclic _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
    | alternating n' hn' =>
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · have h5 : Nat.card T = Nat.factorial 5 / 2 :=
          (Nat.card_congr e.toEquiv).trans
            (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt 5 (by norm_num))
        exact hc60 (by rw [h5]; norm_num [Nat.factorial])
      · have h6 : Nat.card T = Nat.factorial 6 / 2 :=
          (Nat.card_congr e.toEquiv).trans
            (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt 6 (by norm_num))
        exact hc360 (by rw [h6]; norm_num [Nat.factorial])
      · have h8 : Nat.card T = Nat.factorial 8 / 2 :=
          (Nat.card_congr e.toEquiv).trans
            (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt 8 (by norm_num))
        exact hc20160 (by rw [h8]; norm_num [Nat.factorial])
    | lie d =>
      obtain ⟨d1, hv⟩ := d
      rcases amb2_lie hv hi with ⟨q, rfl, hq⟩ | ⟨q, rfl, hq⟩
      · have hc := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.A 1 q, hv⟩ T ⟨e⟩
        simp only [lieOrderFormula, hq] at hc
        exact hc168 (by rw [hc]; decide +kernel)
      · have hc := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.twistedA 2 q, hv⟩ T ⟨e⟩
        simp only [lieOrderFormula, hq] at hc
        exact hc6048 (by rw [hc]; decide +kernel)

theorem not_chev2_spor {S : Type} [Group S] {s : TauCeti.SporadicName} {a m : ℕ} (hm : Odd m)
    (ha : 1 ≤ a) (hs : sporOrd s = 2 ^ a * m)
    (hamb : 2 ^ a * m ≠ 60 ∧ 2 ^ a * m ≠ 168 ∧ 2 ^ a * m ≠ 360 ∧ 2 ^ a * m ≠ 6048 ∧
      2 ^ a * m ≠ 20160)
    (hb : ∀ t ∈ lie2Tags, ∀ n ≤ a + 1, ∀ f ≤ a, lieSylowExponent t n * f = a →
      2 ^ a * m * lieOrderDivisor t n (2 ^ f) ≠ lieOrderNumerator t n (2 ^ f))
    (e : S ≃* (TauCeti.CFSGIndex.sporadic s).Group) : ¬ IsChevSimple 2 S :=
  not_chev2_of_card hm ha ((Nat.card_congr e.toEquiv).trans ((sporadicOrdersTable_holds s).trans hs))
    hamb hb

theorem notChev2_holds : ∀ (S : Type) [Group S] (j : TauCeti.CFSGIndex), NotChev2Idx j →
    Nonempty (S ≃* j.Group) → ¬ IsChevSimple 2 S := by
  intro S _ j hj hne
  obtain ⟨e⟩ := hne
  rcases hj with ⟨s, rfl, p, hp⟩ | ⟨h7, rfl⟩ | ⟨h9, rfl⟩ | hl
  · cases s
    case M11 =>
      exact not_chev2_spor (s := .M11) (a := 4) (m := 3 ^ 2 * 5 * 11) (by decide) (by norm_num)
        (by decide) (by norm_num) (by decide +kernel) e
    case J3 =>
      exact not_chev2_spor (s := .J3) (a := 7) (m := 3 ^ 5 * 5 * 17 * 19) (by decide) (by norm_num)
        (by decide) (by norm_num) (by decide +kernel) e
    case Co2 =>
      exact not_chev2_spor (s := .Co2) (a := 18) (m := 3 ^ 6 * 5 ^ 3 * 7 * 11 * 23) (by decide)
        (by norm_num) (by decide) (by norm_num) (by decide +kernel) e
    case Co3 =>
      exact not_chev2_spor (s := .Co3) (a := 10) (m := 3 ^ 7 * 5 ^ 3 * 7 * 11 * 23) (by decide)
        (by norm_num) (by decide) (by norm_num) (by decide +kernel) e
    case Suz =>
      exact not_chev2_spor (s := .Suz) (a := 13) (m := 3 ^ 7 * 5 ^ 2 * 7 * 11 * 13) (by decide)
        (by norm_num) (by decide) (by norm_num) (by decide +kernel) e
    case Fi22 =>
      exact not_chev2_spor (s := .Fi22) (a := 17) (m := 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13) (by decide)
        (by norm_num) (by decide) (by norm_num) (by decide +kernel) e
    case Fi23 =>
      exact not_chev2_spor (s := .Fi23) (a := 18) (m := 3 ^ 13 * 5 ^ 2 * 7 * 11 * 13 * 17 * 23)
        (by decide) (by norm_num) (by decide) (by norm_num) (by decide +kernel) e
    case McL =>
      exact not_chev2_spor (s := .McL) (a := 7) (m := 3 ^ 6 * 5 ^ 3 * 7 * 11) (by decide)
        (by norm_num) (by decide) (by norm_num) (by decide +kernel) e
    case Ly =>
      exact not_chev2_spor (s := .Ly) (a := 8) (m := 3 ^ 7 * 5 ^ 6 * 7 * 11 * 31 * 37 * 67)
        (by decide) (by norm_num) (by decide) (by norm_num) (by decide +kernel) e
    case B =>
      exact not_chev2_spor (s := .B) (a := 41)
        (m := 3 ^ 13 * 5 ^ 6 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 * 47) (by decide)
        (by norm_num) (by decide) (by norm_num) (by decide +kernel) e
    case Th =>
      exact not_chev2_spor (s := .Th) (a := 15) (m := 3 ^ 10 * 5 ^ 3 * 7 ^ 2 * 13 * 19 * 31)
        (by decide) (by norm_num) (by decide) (by norm_num) (by decide +kernel) e
    case ONan =>
      exact not_chev2_spor (s := .ONan) (a := 9) (m := 3 ^ 4 * 5 * 7 ^ 3 * 11 * 19 * 31)
        (by decide) (by norm_num) (by decide) (by norm_num) (by decide +kernel) e
    case Fi24Prime =>
      exact not_chev2_spor (s := .Fi24Prime) (a := 21)
        (m := 3 ^ 16 * 5 ^ 2 * 7 ^ 3 * 11 * 13 * 17 * 23 * 29) (by decide) (by norm_num) (by decide)
        (by norm_num) (by decide +kernel) e
    case M =>
      exact not_chev2_spor (s := .M) (a := 46)
        (m := 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71)
        (by decide) (by norm_num) (by decide) (by norm_num) (by decide +kernel) e
    case HN =>
      exact not_chev2_spor (s := .HN) (a := 14) (m := 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19) (by decide)
        (by norm_num) (by decide) (by norm_num) (by decide +kernel) e
    case HS =>
      exact not_chev2_spor (s := .HS) (a := 9) (m := 3 ^ 2 * 5 ^ 3 * 7 * 11) (by decide)
        (by norm_num) (by decide) (by norm_num) (by decide +kernel) e
    case Ru =>
      exact not_chev2_spor (s := .Ru) (a := 14) (m := 3 ^ 3 * 5 ^ 3 * 7 * 13 * 29) (by decide)
        (by norm_num) (by decide) (by norm_num) (by decide +kernel) e
    case He =>
      exact not_chev2_spor (s := .He) (a := 10) (m := 3 ^ 3 * 5 ^ 2 * 7 ^ 3 * 17) (by decide)
        (by norm_num) (by decide) (by norm_num) (by decide +kernel) e
    case J4 =>
      exact not_chev2_spor (s := .J4) (a := 21)
        (m := 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43) (by decide) (by norm_num) (by decide)
        (by norm_num) (by decide +kernel) e
    case M12 =>
      exact not_chev2_spor (s := .M12) (a := 6) (m := 3 ^ 3 * 5 * 11) (by decide) (by norm_num)
        (by decide) (by norm_num) (by decide +kernel) e
    all_goals simp [CFSG.Yardstones.Md0ec50421ce4.k2Spor] at hp
  · have h := (Nat.card_congr e.toEquiv).trans
      (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt 7 (by norm_num))
    exact not_chev2_of_card (a := 3) (m := 3 ^ 2 * 5 * 7) (by decide) (by norm_num)
      (by rw [h]; norm_num [Nat.factorial]) (by norm_num) (by decide +kernel)
  · have h := (Nat.card_congr e.toEquiv).trans
      (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt 9 (by norm_num))
    exact not_chev2_of_card (a := 6) (m := 3 ^ 4 * 5 * 7) (by decide) (by norm_num)
      (by rw [h]; norm_num [Nat.factorial]) (by norm_num) (by decide +kernel)
  · cases j with
    | cyclic _ _ => exact hl.elim
    | alternating _ _ => exact hl.elim
    | sporadic _ => exact hl.elim
    | lie d =>
      obtain ⟨dd, hv⟩ := d
      obtain ⟨q, rfl, hq⟩ := l33_lie hv hl
      have hM := CFSG.Models.lieModel_A 2 q hv e
      have hBP := CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
        (t := .PSL) (by simp [CFSG.Blueprint.classicalTags]) hM
      obtain ⟨-, hnum, -⟩ := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput S .PSL
        (2 + 1) q.p q.exponent (CFSG.Blueprint.LieModel.admissible hBP) hBP
      have hqc : q.p ^ q.exponent = 3 := by
        rw [← TauCeti.PrimePower.card_def]
        exact hq
      rw [hqc] at hnum
      have hd1 : lieOrderDivisor .PSL (2 + 1) 3 = 1 := by decide
      have hn1 : lieOrderNumerator .PSL (2 + 1) 3 = 5616 := by decide +kernel
      rw [hd1, hn1] at hnum
      have hT : Nat.card S = 2 ^ 4 * (3 ^ 3 * 13) := by
        norm_num at hnum ⊢
        exact hnum
      exact not_chev2_of_card (a := 4) (m := 3 ^ 3 * 13) (by decide) (by norm_num) hT
        (by norm_num) (by decide +kernel)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.List93

end
