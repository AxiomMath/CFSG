module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodOut
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodLangAlg
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodSteinberg
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodFrames
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodE8FourFive
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodE8TenTwelve
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangThreeProved
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyE8Three
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.SmallQE8Eight
public import CFSG.LieType.SeitzGeneration.ExcHigh.Classes
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSevenClasses

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.RankThree.PartOne.KE
  CFSG.Timmesfeld.ExceptionalOrders CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.K133H
  CFSG.RankThree.PartOne.OutStructure CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.RankThree.Lattice CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

theorem eq_seventeen_of_orderOf_two_eq_eight {p : ℕ} (hp : p.Prime)
    (h : orderOf ((2 : ℕ) : ZMod p) = 8) : p = 17 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h8 : ((2 : ℕ) : ZMod p) ^ 8 = 1 := by
    rw [← h]
    exact pow_orderOf_eq_one _
  have h2ne : ((2 : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    rw [h0] at h8
    norm_num at h8
  have hp2 : 2 ≤ p := hp.two_le
  have h9 : 9 ≤ p := by
    have hdvd : 8 ∣ p - 1 := h ▸ ZMod.orderOf_dvd_card_sub_one h2ne
    have h1 : 8 ≤ p - 1 := Nat.le_of_dvd (by omega) hdvd
    omega
  have h255 : ((255 : ℕ) : ZMod p) = 0 := by
    push_cast at h8 ⊢
    linear_combination h8
  have hd : p ∣ 255 := (ZMod.natCast_eq_zero_iff 255 p).1 h255
  have h255' : (255 : ℕ) = 3 * 5 * 17 := by norm_num
  rw [h255'] at hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h15 | h17
  · rcases (Nat.Prime.dvd_mul hp).1 h15 with h3 | h5
    · have := Nat.le_of_dvd (by norm_num) h3
      omega
    · have := Nat.le_of_dvd (by norm_num) h5
      omega
  · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h17

section E8Eight


theorem bigComponentSet_nonempty_E8_eight {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup .E8 L p) (hρ : RhoIs S e8EightMat) (hp7 : 7 ≤ p)
    (hord : orderOf ((S.D.q : ℕ) : ZMod p) = 8)
    {D₁ : Subgroup (ModGL .E8 L)} (hD₁E : D₁ ≤ S.E) (hD₁c : Nat.card D₁ = p ^ 2) :
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.bigComponentSet S D₁).Nonempty := by
  haveI : Fact p.Prime := ⟨S.hp⟩
  by_cases hq3 : 3 ≤ S.D.q
  · exact bigComponentSet_nonempty_of_classCheck S (Or.inr (Or.inr (Or.inr rfl)))
      (toMat_cartanList _) hρ hq3 hp7 hord e8Eight_classCheck hD₁E hD₁c
  · have hq2 : S.D.q = 2 := by
      have hle : S.D.q ≤ 2 := by omega
      have h1 : 1 < S.D.q := S.hqpow.1.one_lt
      omega
    have hp17 : p = 17 := by
      have h2 : orderOf (((2 : ℕ)) : ZMod p) = 8 := by
        rw [← hq2]
        exact hord
      exact eq_seventeen_of_orderOf_two_eq_eight S.hp h2
    exact bigComponentSet_nonempty_of_centralizerTrivial S hD₁E hD₁c
      (centralizerTrivial_E8_eight S hρ hq2 hp17 hD₁E hD₁c)

end E8Eight

section CatPlanes


theorem perfectCentralizerPlanes_cat_E8_three_char (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E8 q).Valid) (hq2 : q.card ≠ 2) (h3q : ¬ 3 ∣ q.card) :
    PerfectCentralizerPlanes 3 (Cat ⟨.E8 q, hv⟩) := by
  classical
  obtain ⟨K, hF, hFin, hK, -, ⟨φ⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
  letI : Field K := hF
  letI : Finite K := hFin
  have h3K : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    exact h3q
  have hK4 : 4 ≤ Nat.card K := by
    have h2 : 1 < Nat.card K := Finite.one_lt_card
    have hne2 : Nat.card K ≠ 2 := by rw [hK]; exact hq2
    have hne3 : Nat.card K ≠ 3 := fun h => h3K (h.symm ▸ dvd_rfl)
    omega
  exact PerfectCentralizerPlanes.of_mulEquiv φ.symm
    (perfectCentralizerPlanes_adjointGroup_three (Or.inr (Or.inr (Or.inr rfl)))
      CFSG.HardMathSupport.Timmesfeld.Torality.langToralPlane_E8_three K h3K hK4)

theorem perfectCentralizerPlanes_cat_E8_one_two (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E8 q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ≠ q.p) (hp3 : p ≠ 3)
    (hord : orderOf ((q.card : ℕ) : ZMod p) = 1 ∨
      orderOf ((q.card : ℕ) : ZMod p) = 2) :
    PerfectCentralizerPlanes p (Cat ⟨.E8 q, hv⟩) := by
  classical
  obtain ⟨K, hF, hFin, hK, -, ⟨φ⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
  letI : Field K := hF
  letI : Finite K := hFin
  rw [← hK] at hord
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
  rcases hord with h1 | h2
  · have hd : p ∣ Nat.card K - 1 :=
      CFSG.HardMathSupport.Timmesfeld.LocalTwo.dvd_sub_one_of_orderOf_eq_one
        Nat.card_pos h1
    by_cases hp5eq : p = 5
    · obtain rfl := hp5eq
      exact PerfectCentralizerPlanes.of_mulEquiv φ.symm
        (perfectCentralizerPlanes_adjointGroup_E8_five_steinberg K (Or.inl hd))
    by_cases hp7eq : p = 7
    · obtain rfl := hp7eq
      exact PerfectCentralizerPlanes.of_mulEquiv φ.symm
        (perfectCentralizerPlanes_adjointGroup_E8_seven_steinberg K (Or.inl hd))
    · have hp7 : 7 ≤ p := seven_le_of_prime_of_five_lt hp (by omega)
      have hp11 : 11 ≤ p :=
        CFSG.HardMathSupport.Timmesfeld.CrossChar.eleven_le_of_prime_seven_le_ne hp hp7 hp7eq
      exact PerfectCentralizerPlanes.of_mulEquiv φ.symm
        (perfectCentralizerPlanes_of_conj_into_torus hp hp2 hd
          (fun A hA hAp =>
            CFSG.HardMathSupport.Timmesfeld.LocalTwo.exists_conj_into_torus_E8 hp hp11 hd
              hA hAp))
  · have hd : p ∣ Nat.card K + 1 :=
      CFSG.LieType.SeitzGeneration.ExcHigh.dvd_add_one_of_orderOf_eq_two hp h2
    by_cases hp5eq : p = 5
    · obtain rfl := hp5eq
      exact PerfectCentralizerPlanes.of_mulEquiv φ.symm
        (perfectCentralizerPlanes_adjointGroup_E8_five_steinberg K (Or.inr hd))
    by_cases hp7eq : p = 7
    · obtain rfl := hp7eq
      exact PerfectCentralizerPlanes.of_mulEquiv φ.symm
        (perfectCentralizerPlanes_adjointGroup_E8_seven_steinberg K (Or.inr hd))
    · have hp7 : 7 ≤ p := seven_le_of_prime_of_five_lt hp (by omega)
      have hp11 : 11 ≤ p :=
        CFSG.HardMathSupport.Timmesfeld.CrossChar.eleven_le_of_prime_seven_le_ne hp hp7 hp7eq
      refine perfectCentralizerPlanes_cat_of_langTorusAtAlgM (k := .E8) trivial
        (langTorusAtAlgM_E8_2 frobeniusOnRoots_proved) ?_ q hv hp ⟨hp11, ?_⟩ hpq
      · intro L _ _ p' S q' hR hSq hAlg hρ D₁ hD₁E hD₁c
        haveI : Fact p'.Prime := ⟨S.hp⟩
        exact bigComponentSet_nonempty_of_classCheck S (Or.inr (Or.inr (Or.inr rfl)))
          (toMat_cartanList _) hρ
            (three_le_q_of_class S (by omega) (Or.inr (Or.inl rfl))
              (by rw [hSq]; exact hR.2)) (by omega) (by rw [hSq]; exact hR.2)
            e8Two_classCheck hD₁E hD₁c
      · rw [← hK]
        exact h2

theorem perfectCentralizerPlanes_cat_E8_three_four_six (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E8 q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ≠ q.p) (hp3 : p ≠ 3)
    (hord : orderOf ((q.card : ℕ) : ZMod p) = 3 ∨
      orderOf ((q.card : ℕ) : ZMod p) = 4 ∨
      orderOf ((q.card : ℕ) : ZMod p) = 6) :
    PerfectCentralizerPlanes p (Cat ⟨.E8 q, hv⟩) := by
  classical
  obtain ⟨K, hF, hFin, hK, -, ⟨φ⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
  letI : Field K := hF
  letI : Finite K := hFin
  rw [← hK] at hord
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  have hq0 : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    exact hpK ((ZMod.natCast_eq_zero_iff (Nat.card K) p).1 h0)
  rcases hord with h3 | h4 | h6
  · have hdvd : 3 ∣ p - 1 := h3 ▸ ZMod.orderOf_dvd_card_sub_one hq0
    have hp5' : p ≠ 5 := by rintro rfl; norm_num at hdvd
    have hp7 : 7 ≤ p := seven_le_of_prime_of_five_lt hp (by omega)
    refine perfectCentralizerPlanes_cat_of_langTorusAtAlgClass (k := .E8) trivial
      (langTorusAtAlgClass_E8_three frobeniusOnRoots_proved) ?_ q hv hp ⟨hp7, ?_⟩ hpq
    · intro L _ _ p' S q' hR hSq hAlg hC D₁ hD₁E hD₁c
      haveI : Fact p'.Prime := ⟨S.hp⟩
      exact bigComponentSet_nonempty_of_bigAnyPBig S
        (S.bigAnyPBig_of_weylClass_tri (Or.inr (Or.inr (Or.inr rfl))) hR.1 e8ThreeMat_rel hC)
        hD₁E hD₁c
    · rw [← hK]
      exact h3
  · by_cases hp5eq : p = 5
    · obtain rfl := hp5eq
      exact PerfectCentralizerPlanes.of_mulEquiv φ.symm
        (perfectCentralizerPlanes_adjointGroup_E8_four_five K
          (CFSG.LieType.SeitzGeneration.dvd_sq_add_one_of_orderOf_eq_four hp h4))
    · have hdvd : 4 ∣ p - 1 := h4 ▸ ZMod.orderOf_dvd_card_sub_one hq0
      have hp7 : 7 ≤ p := seven_le_of_prime_of_five_lt hp (by omega)
      refine perfectCentralizerPlanes_cat_of_langTorusAtAlgM (k := .E8) trivial
        (langTorusAtAlgM_E8_4 frobeniusOnRoots_proved) ?_ q hv hp ⟨hp7, ?_⟩ hpq
      · intro L _ _ p' S q' hR hSq hAlg hρ D₁ hD₁E hD₁c
        haveI : Fact p'.Prime := ⟨S.hp⟩
        exact bigComponentSet_nonempty_of_classCheck S (Or.inr (Or.inr (Or.inr rfl)))
          (toMat_cartanList _) hρ
            (three_le_q_of_class S hR.1 (Or.inr (Or.inr (Or.inl rfl)))
              (by rw [hSq]; exact hR.2)) hR.1 (by rw [hSq]; exact hR.2) e8Four_classCheck
            hD₁E hD₁c
      · rw [← hK]
        exact h4
  · have hdvd : 6 ∣ p - 1 := h6 ▸ ZMod.orderOf_dvd_card_sub_one hq0
    have hp5' : p ≠ 5 := by rintro rfl; norm_num at hdvd
    have hp7 : 7 ≤ p := seven_le_of_prime_of_five_lt hp (by omega)
    refine perfectCentralizerPlanes_cat_of_langTorusAtAlgClass (k := .E8) trivial
      (langTorusAtAlgClass_E8_six frobeniusOnRoots_proved) ?_ q hv hp ⟨hp7, ?_⟩ hpq
    · intro L _ _ p' S q' hR hSq hAlg hC D₁ hD₁E hD₁c
      haveI : Fact p'.Prime := ⟨S.hp⟩
      exact bigComponentSet_nonempty_of_bigAnyPBig S
        (S.bigAnyPBig_of_weylClass_hex (Or.inr (Or.inr (Or.inr rfl))) hR.1 e8SixMat_rel hC)
        hD₁E hD₁c
    · rw [← hK]
      exact h6

theorem perfectCentralizerPlanes_cat_E8_eight (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E8 q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ≠ q.p) (hp3 : p ≠ 3)
    (hord : orderOf ((q.card : ℕ) : ZMod p) = 8) :
    PerfectCentralizerPlanes p (Cat ⟨.E8 q, hv⟩) := by
  classical
  obtain ⟨K, hF, hFin, hK, -, ⟨φ⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
  letI : Field K := hF
  letI : Finite K := hFin
  rw [← hK] at hord
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  have hq0 : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    exact hpK ((ZMod.natCast_eq_zero_iff (Nat.card K) p).1 h0)
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : 8 ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hq0
  have hp5' : p ≠ 5 := by rintro rfl; norm_num at hdvd
  have hp7 : 7 ≤ p := seven_le_of_prime_of_five_lt hp (by omega)
  refine perfectCentralizerPlanes_cat_of_langTorusAtAlgM (k := .E8) trivial
    (langTorusAtAlgM_E8_8 frobeniusOnRoots_proved) ?_ q hv hp ⟨hp7, ?_⟩ hpq
  · intro L _ _ p' S q' hR hSq hAlg hρ D₁ hD₁E hD₁c
    exact bigComponentSet_nonempty_E8_eight S hρ hR.1 (by rw [hSq]; exact hR.2)
      hD₁E hD₁c
  · rw [← hK]
    exact hord

theorem perfectCentralizerPlanes_cat_E8_rigid (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E8 q).Valid) {p : ℕ} (hp : p.Prime) (hpq : p ≠ q.p)
    (hord : orderOf ((q.card : ℕ) : ZMod p) = 5 ∨
      orderOf ((q.card : ℕ) : ZMod p) = 10 ∨
      orderOf ((q.card : ℕ) : ZMod p) = 12) :
    PerfectCentralizerPlanes p (Cat ⟨.E8 q, hv⟩) := by
  classical
  obtain ⟨K, hF, hFin, hK, -, ⟨φ⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
  letI : Field K := hF
  letI : Finite K := hFin
  rw [← hK] at hord
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  have hq0 : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    exact hpK ((ZMod.natCast_eq_zero_iff (Nat.card K) p).1 h0)
  rcases hord with h5 | h10 | h12
  · exact PerfectCentralizerPlanes.of_mulEquiv φ.symm
      (perfectCentralizerPlanes_adjointGroup_E8_five K hp h5)
  · have hdvd : 10 ∣ p - 1 := h10 ▸ ZMod.orderOf_dvd_card_sub_one hq0
    have hp2' : p ≠ 2 := by rintro rfl; norm_num at hdvd
    have hp3' : p ≠ 3 := by rintro rfl; norm_num at hdvd
    have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2' hp3'
    have hp5' : p ≠ 5 := by rintro rfl; norm_num at hdvd
    have hp7 : 7 ≤ p := seven_le_of_prime_of_five_lt hp (by omega)
    exact PerfectCentralizerPlanes.of_mulEquiv φ.symm
      (perfectCentralizerPlanes_adjointGroup_E8_ten K hp hp7 h10)
  · have hdvd : 12 ∣ p - 1 := h12 ▸ ZMod.orderOf_dvd_card_sub_one hq0
    have hp2' : p ≠ 2 := by rintro rfl; norm_num at hdvd
    have hp3' : p ≠ 3 := by rintro rfl; norm_num at hdvd
    have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2' hp3'
    have hp5' : p ≠ 5 := by rintro rfl; norm_num at hdvd
    have hp7 : 7 ≤ p := seven_le_of_prime_of_five_lt hp (by omega)
    exact PerfectCentralizerPlanes.of_mulEquiv φ.symm
      (perfectCentralizerPlanes_adjointGroup_E8_twelve K hp hp7 h12)

theorem perfectCentralizerPlanes_cat_E8 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E8 q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ≠ q.p) (h32 : ¬ (p = 3 ∧ q.card = 2)) :
    PerfectCentralizerPlanes p (Cat ⟨.E8 q, hv⟩) := by
  by_cases hp3 : p = 3
  · subst hp3
    refine perfectCentralizerPlanes_cat_E8_three_char q hv ?_ ?_
    · intro h
      exact h32 ⟨rfl, h⟩
    · intro h3
      exact not_dvd_card_of_ne hp hpq h3
  · by_cases hcnt : 2 ≤ degCount Tag.E8 (orderOf ((q.card : ℕ) : ZMod p))
    · rcases degCount_E8_ge_two hcnt with h1 | h2 | h3 | h4 | h5 | h6 | h8 | h10 | h12
      · exact perfectCentralizerPlanes_cat_E8_one_two q hv hp hp2 hpq hp3 (Or.inl h1)
      · exact perfectCentralizerPlanes_cat_E8_one_two q hv hp hp2 hpq hp3 (Or.inr h2)
      · exact perfectCentralizerPlanes_cat_E8_three_four_six q hv hp hp2 hpq hp3 (Or.inl h3)
      · exact perfectCentralizerPlanes_cat_E8_three_four_six q hv hp hp2 hpq hp3
          (Or.inr (Or.inl h4))
      · exact perfectCentralizerPlanes_cat_E8_rigid q hv hp hpq (Or.inl h5)
      · exact perfectCentralizerPlanes_cat_E8_three_four_six q hv hp hp2 hpq hp3
          (Or.inr (Or.inr h6))
      · exact perfectCentralizerPlanes_cat_E8_eight q hv hp hp2 hpq hp3 h8
      · exact perfectCentralizerPlanes_cat_E8_rigid q hv hp hpq (Or.inr (Or.inl h10))
      · exact perfectCentralizerPlanes_cat_E8_rigid q hv hp hpq (Or.inr (Or.inr h12))
    · exact PerfectCentralizerPlanes.of_rankLE1 hp (rankLE1_cat_E8 q hv hp hpq (by omega))

end CatPlanes

section Out


theorem outPNice_cat_E8 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid)
    {p : ℕ} (hp : p.Prime) : OutPNice p (Cat ⟨.E8 q, hv⟩) := by
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel (Cat ⟨.E8 q, hv⟩) .E8 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.untwistedChevalleyModel_of_bridge
        CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 (MulEquiv.refl _)⟩
  exact outPNice_E8_gen hp hm

end Out

section Catalogue


theorem innGoodAt_E8 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p) (h32 : ¬ (p = 3 ∧ q.card = 2)) :
    InnGoodAt p (.E8 q) (Cat ⟨.E8 q, hv⟩) := by
  obtain ⟨K, hF, hFin, -, -, ⟨φ⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
  letI : Field K := hF
  letI : Finite K := hFin
  haveI : Finite (Cat ⟨.E8 q, hv⟩) := Finite.of_equiv _ φ.symm.toEquiv
  have hZ : Subgroup.center (Cat ⟨.E8 q, hv⟩) = ⊥ := by
    rw [← Subgroup.map_center_eq φ.symm, center_adjointGroup_eq_bot, Subgroup.map_bot]
  exact innGoodAt_of_outPNice hp hZ (outPNice_cat_E8 q hv hp)
    (perfectCentralizerPlanes_cat_E8 q hv hp hp2 hpq h32) (.E8 q)

theorem lieInnGood_E8 : LieInnGood fun d => ∃ q, d = .E8 q := by
  intro d p hp hp2 hpc h3 h5 hP
  obtain ⟨idx, hv⟩ := d
  obtain ⟨q, rfl⟩ := hP
  refine innGoodAt_E8 q hv hp hp2 ?_ h3
  rwa [TauCeti.LieTypeIndex.characteristic_E8 q] at hpc

end Catalogue

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end

