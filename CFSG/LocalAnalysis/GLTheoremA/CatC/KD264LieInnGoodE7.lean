module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodE7TwoFive
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodOut
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodLangAlg
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodSteinberg
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E7FourAux.Chain
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.SmallQE7Three
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodA2E8
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerFamE
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangThreeProved
public import CFSG.LieType.SeitzGeneration.ExcHigh.Classes
public import CFSG.RankThree.PartOne.MB3.OddOutExceptional
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge
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
  CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2 CFSG.RankThree.Lattice

section FourNeTwo


theorem langTorusAtAlgM_E7_four_odd_ne_two (hF : FrobeniusOnRoots) :
    LangTorusAtAlgM .E7 (fun p c => 5 ≤ p ∧ c ≠ 2 ∧ orderOf ((c : ℕ) : ZMod p) = 4)
      e7FourBMat :=
  fun hk q hv p hp hR hpq =>
    langTorusAtAlgM_E7_four_odd hF hk q hv p hp ⟨hR.1, hR.2.2⟩ hpq

end FourNeTwo

section ClassCheck


theorem bigComponentSet_nonempty_of_classCheck_E7_two {L : Type} [Field L] [IsAlgClosed L]
    {p : ℕ} (S : LangSetup .E7 L p) (hp11 : 11 ≤ p)
    (he : orderOf ((S.D.q : ℕ) : ZMod p) = 2) (hρ : RhoIs S e7TwoMat)
    {D₁ : Subgroup (ModGL .E7 L)} (hD₁ : D₁ ≤ S.E) (hc : Nat.card D₁ = p ^ 2) :
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.bigComponentSet S D₁).Nonempty :=
  bigComponentSet_nonempty_of_classCheck S (Or.inr (Or.inr (Or.inl rfl))) (toMat_cartanList _)
    hρ (three_le_q_of_class S (by omega) (Or.inr (Or.inl rfl)) he) (by omega) he
    e7Two_classCheck hD₁ hc

theorem bigComponentSet_nonempty_of_classCheck_E7_six {L : Type} [Field L] [IsAlgClosed L]
    {p : ℕ} (S : LangSetup .E7 L p) (hp7 : 7 ≤ p)
    (he : orderOf ((S.D.q : ℕ) : ZMod p) = 6) (hρ : RhoIs S e7SixMat)
    {D₁ : Subgroup (ModGL .E7 L)} (hD₁ : D₁ ≤ S.E) (hc : Nat.card D₁ = p ^ 2) :
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.bigComponentSet S D₁).Nonempty :=
  bigComponentSet_nonempty_of_classCheck S (Or.inr (Or.inr (Or.inl rfl))) (toMat_cartanList _)
    hρ (three_le_q_of_class S hp7 (Or.inr (Or.inr (Or.inr rfl))) he) hp7 he
    e7Six_classCheck hD₁ hc

end ClassCheck

section ClassCheckOdd


theorem bigComponentSet_nonempty_of_classCheck_E7_four {L : Type} [Field L] [IsAlgClosed L]
    {p : ℕ} (S : LangSetup .E7 L p) (hp3 : 3 ≤ p) (hq2 : S.D.q ≠ 2)
    (he : orderOf ((S.D.q : ℕ) : ZMod p) = 4) (hρ : RhoIs S e7FourBMat)
    {D₁ : Subgroup (ModGL .E7 L)} (hD₁ : D₁ ≤ S.E) (hc : Nat.card D₁ = p ^ 2) :
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.bigComponentSet S D₁).Nonempty :=
  bigComponentSet_nonempty_of_classCheck_odd S (Or.inr (Or.inr (Or.inl rfl)))
    (toMat_cartanList _) hρ (three_le_q_of_ne_two S hq2) hp3 he
    e7FourB_classCheck hD₁ hc

theorem bigComponentSet_nonempty_of_classCheck_E7_three {L : Type} [Field L] [IsAlgClosed L]
    {p : ℕ} (S : LangSetup .E7 L p) (hp7 : 7 ≤ p)
    (he : orderOf ((S.D.q : ℕ) : ZMod p) = 3) (hρ : RhoIs S e7ThreeMat)
    {D₁ : Subgroup (ModGL .E7 L)} (hD₁ : D₁ ≤ S.E) (hc : Nat.card D₁ = p ^ 2) :
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.bigComponentSet S D₁).Nonempty := by
  by_cases hq2 : S.D.q = 2
  · have he2 : orderOf (((2 : ℕ)) : ZMod p) = 3 := by
      rw [← hq2]
      exact he
    have hp7' : p = 7 :=
      prime_eq_seven_of_order_three S.hp (Or.inr trivial) he2
    exact bigComponentSet_nonempty_of_centralizerTrivial S hD₁ hc
      (centralizerTrivial_E7_two S hρ hq2 hp7' hD₁ hc)
  · exact bigComponentSet_nonempty_of_classCheck S (Or.inr (Or.inr (Or.inl rfl)))
      (toMat_cartanList _) hρ (three_le_q_of_ne_two S hq2) hp7 he e7Three_classCheck hD₁ hc

end ClassCheckOdd

section LangPlanes


theorem perfectCentralizerPlanes_adjointGroup_E7_lang_two {K : Type} [Field K]
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid)
    (ε : Cat ⟨.E7 q, hv⟩ ≃* adjointGroup Tag.E7 K) (hK : Nat.card K = q.card)
    {p : ℕ} (hp : p.Prime) (hpq : p ≠ q.p) (hp11 : 11 ≤ p)
    (h2 : orderOf ((Nat.card K : ℕ) : ZMod p) = 2) :
    PerfectCentralizerPlanes p (adjointGroup Tag.E7 K) := by
  have h2' : orderOf ((q.card : ℕ) : ZMod p) = 2 := by
    rw [← hK]
    exact h2
  have hcat : PerfectCentralizerPlanes p (Cat ⟨.E7 q, hv⟩) :=
    perfectCentralizerPlanes_cat_of_langTorusAtAlgM (k := .E7) trivial
      (langTorusAtAlgM_E7_2 frobeniusOnRoots_proved)
      (fun L _ _ p S q' hR hSq _ hρ _ hD₁ hc =>
        bigComponentSet_nonempty_of_classCheck_E7_two S hR.1 (by rw [hSq]; exact hR.2) hρ
          hD₁ hc)
      q hv hp ⟨hp11, h2'⟩ hpq
  exact PerfectCentralizerPlanes.of_mulEquiv ε hcat

theorem perfectCentralizerPlanes_adjointGroup_E7_lang_three {K : Type} [Field K]
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid)
    (ε : Cat ⟨.E7 q, hv⟩ ≃* adjointGroup Tag.E7 K) (hK : Nat.card K = q.card)
    {p : ℕ} (hp : p.Prime) (hpq : p ≠ q.p) (hp7 : 7 ≤ p)
    (h3 : orderOf ((Nat.card K : ℕ) : ZMod p) = 3) :
    PerfectCentralizerPlanes p (adjointGroup Tag.E7 K) := by
  have h3' : orderOf ((q.card : ℕ) : ZMod p) = 3 := by
    rw [← hK]
    exact h3
  have hcat : PerfectCentralizerPlanes p (Cat ⟨.E7 q, hv⟩) :=
    perfectCentralizerPlanes_cat_of_langTorusAtAlgM (k := .E7) trivial
      (langTorusAtAlgM_E7_3 frobeniusOnRoots_proved)
      (fun L _ _ p S q' hR hSq _ hρ _ hD₁ hc =>
        bigComponentSet_nonempty_of_classCheck_E7_three S hR.1 (by rw [hSq]; exact hR.2) hρ
          hD₁ hc)
      q hv hp ⟨hp7, h3'⟩ hpq
  exact PerfectCentralizerPlanes.of_mulEquiv ε hcat

theorem perfectCentralizerPlanes_adjointGroup_E7_lang_six {K : Type} [Field K]
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid)
    (ε : Cat ⟨.E7 q, hv⟩ ≃* adjointGroup Tag.E7 K) (hK : Nat.card K = q.card)
    {p : ℕ} (hp : p.Prime) (hpq : p ≠ q.p) (hp7 : 7 ≤ p)
    (h6 : orderOf ((Nat.card K : ℕ) : ZMod p) = 6) :
    PerfectCentralizerPlanes p (adjointGroup Tag.E7 K) := by
  have h6' : orderOf ((q.card : ℕ) : ZMod p) = 6 := by
    rw [← hK]
    exact h6
  have hcat : PerfectCentralizerPlanes p (Cat ⟨.E7 q, hv⟩) :=
    perfectCentralizerPlanes_cat_of_langTorusAtAlgM (k := .E7) trivial
      (langTorusAtAlgM_E7_6 frobeniusOnRoots_proved)
      (fun L _ _ p S q' hR hSq _ hρ _ hD₁ hc =>
        bigComponentSet_nonempty_of_classCheck_E7_six S hR.1 (by rw [hSq]; exact hR.2) hρ
          hD₁ hc)
      q hv hp ⟨hp7, h6'⟩ hpq
  exact PerfectCentralizerPlanes.of_mulEquiv ε hcat

theorem perfectCentralizerPlanes_adjointGroup_E7_lang_four {K : Type} [Field K]
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid)
    (ε : Cat ⟨.E7 q, hv⟩ ≃* adjointGroup Tag.E7 K) (hK : Nat.card K = q.card)
    {p : ℕ} (hp : p.Prime) (hpq : p ≠ q.p) (hp5 : 5 ≤ p) (hq2 : Nat.card K ≠ 2)
    (h4 : orderOf ((Nat.card K : ℕ) : ZMod p) = 4) :
    PerfectCentralizerPlanes p (adjointGroup Tag.E7 K) := by
  have h4' : orderOf ((q.card : ℕ) : ZMod p) = 4 := by
    rw [← hK]
    exact h4
  have hq2' : q.card ≠ 2 := by
    rw [← hK]
    exact hq2
  have hcat : PerfectCentralizerPlanes p (Cat ⟨.E7 q, hv⟩) :=
    perfectCentralizerPlanes_cat_of_langTorusAtAlgM (k := .E7) trivial
      (langTorusAtAlgM_E7_four_odd_ne_two frobeniusOnRoots_proved)
      (fun L _ _ p S q' hR hSq _ hρ _ hD₁ hc =>
        bigComponentSet_nonempty_of_classCheck_E7_four S (by omega)
          (fun h => hR.2.1 (hSq.symm.trans h)) (by rw [hSq]; exact hR.2.2) hρ hD₁ hc)
      q hv hp ⟨hp5, hq2', h4'⟩ hpq
  exact PerfectCentralizerPlanes.of_mulEquiv ε hcat

end LangPlanes

section SmallPrime


theorem perfectCentralizerPlanes_adjointGroup_E7_small_prime (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    (hd : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1) :
    PerfectCentralizerPlanes p (adjointGroup Tag.E7 K) := by
  rcases hp57 with rfl | rfl
  · exact perfectCentralizerPlanes_adjointGroup_E7_five_steinberg K hd
  · exact perfectCentralizerPlanes_adjointGroup_E7_seven_steinberg K hd

end SmallPrime

section One


theorem perfectCentralizerPlanes_adjointGroup_E7_one (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpK : ¬ p ∣ Nat.card K)
    (h1 : orderOf ((Nat.card K : ℕ) : ZMod p) = 1) :
    PerfectCentralizerPlanes p (adjointGroup Tag.E7 K) := by
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
  have hd : p ∣ Nat.card K - 1 :=
    CFSG.HardMathSupport.Timmesfeld.LocalTwo.dvd_sub_one_of_orderOf_eq_one Nat.card_pos h1
  by_cases hp11 : 11 ≤ p
  · exact perfectCentralizerPlanes_of_conj_into_torus hp hp2 hd
      (fun A hA hAp => exists_conj_into_torus_E7 hp hp11 hd hA hAp)
  · have hp57 : p = 5 ∨ p = 7 := by
      by_contra h
      push Not at h
      exact hp11 (CFSG.HardMathSupport.Timmesfeld.CrossChar.eleven_le_of_prime_seven_le_ne
        hp (seven_le_of_prime_of_five_lt hp (by omega)) h.2)
    exact perfectCentralizerPlanes_adjointGroup_E7_small_prime K hp57 (Or.inl hd)

end One

section CatPlanes


theorem perfectCentralizerPlanes_cat_E7 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E7 q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ≠ q.p) (h32 : ¬ (p = 3 ∧ q.card = 2)) :
    PerfectCentralizerPlanes p (Cat ⟨.E7 q, hv⟩) := by
  classical
  obtain ⟨K, hF, hFin, hK, -, ⟨ε⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
  letI : Field K := hF
  letI : Finite K := hFin
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  have hplanes : PerfectCentralizerPlanes p (adjointGroup Tag.E7 K) := by
    rcases eq_or_ne p 3 with rfl | hp3
    · have h3K : ¬ 3 ∣ Nat.card K := hpK
      have hK4 : 4 ≤ Nat.card K := by
        have h1 : 1 < Nat.card K := Finite.one_lt_card
        have hne2 : Nat.card K ≠ 2 := fun h => h32 ⟨rfl, by rw [← hK]; exact h⟩
        have hne3 : Nat.card K ≠ 3 := fun h => h3K (h.symm ▸ dvd_rfl)
        omega
      exact perfectCentralizerPlanes_adjointGroup_three (Or.inr (Or.inr (Or.inl rfl)))
        langToralPlane_E7_three K h3K hK4
    · have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
      by_cases hcnt : 2 ≤ degCount Tag.E7 (orderOf ((Nat.card K : ℕ) : ZMod p))
      · rcases degCount_E7_ge_two hcnt with h1 | h2 | h3 | h4 | h6
        · exact perfectCentralizerPlanes_adjointGroup_E7_one K hp hp2 hp3 hpK h1
        · by_cases hp11 : 11 ≤ p
          · exact perfectCentralizerPlanes_adjointGroup_E7_lang_two q hv ε hK hp hpq hp11 h2
          · have hp57 : p = 5 ∨ p = 7 := by
              by_contra h
              push Not at h
              exact hp11 (CFSG.HardMathSupport.Timmesfeld.CrossChar.eleven_le_of_prime_seven_le_ne
                hp (seven_le_of_prime_of_five_lt hp (by omega)) h.2)
            have hd : p ∣ Nat.card K + 1 :=
              CFSG.LieType.SeitzGeneration.ExcHigh.dvd_add_one_of_orderOf_eq_two hp h2
            exact perfectCentralizerPlanes_adjointGroup_E7_small_prime K hp57 (Or.inr hd)
        · have hp7 : 7 ≤ p := by
            have hq0 : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := fun h =>
              hpK ((ZMod.natCast_eq_zero_iff (Nat.card K) p).1 h)
            have hdvd : 3 ∣ p - 1 := h3 ▸ ZMod.orderOf_dvd_card_sub_one hq0
            have hpne5 : p ≠ 5 := by
              rintro rfl
              norm_num at hdvd
            exact seven_le_of_prime_of_five_lt hp (by omega)
          exact perfectCentralizerPlanes_adjointGroup_E7_lang_three q hv ε hK hp hpq hp7 h3
        · by_cases hq2 : Nat.card K = 2
          · have h42 : orderOf (((2 : ℕ)) : ZMod p) = 4 := by
              rw [← hq2]
              exact h4
            have hp5' : p = 5 := e7Four_eq_five_of_orderOf_two_eq_four hp hp5 h42
            subst hp5'
            exact perfectCentralizerPlanes_adjointGroup_E7_two_five K hq2
          · exact perfectCentralizerPlanes_adjointGroup_E7_lang_four q hv ε hK hp hpq hp5 hq2 h4
        · have hp7 : 7 ≤ p := by
            have hq0 : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := fun h =>
              hpK ((ZMod.natCast_eq_zero_iff (Nat.card K) p).1 h)
            have hdvd : 6 ∣ p - 1 := h6 ▸ ZMod.orderOf_dvd_card_sub_one hq0
            have hpne5 : p ≠ 5 := by
              rintro rfl
              norm_num at hdvd
            exact seven_le_of_prime_of_five_lt hp (by omega)
          exact perfectCentralizerPlanes_adjointGroup_E7_lang_six q hv ε hK hp hpq hp7 h6
      · exact PerfectCentralizerPlanes.of_rankLE1 hp
          (RankLE1.of_mulEquiv ε (rankLE1_cat_E7 q hv hp hpq
            (by
              have hle : degCount Tag.E7 (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 1 :=
                Nat.lt_succ_iff.mp (not_le.mp hcnt)
              rwa [hK] at hle)))
  exact PerfectCentralizerPlanes.of_mulEquiv ε.symm hplanes

end CatPlanes

section Out


theorem outPNice_cat_E7 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : OutPNice p (Cat ⟨.E7 q, hv⟩) := by
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel (Cat ⟨.E7 q, hv⟩) .E7 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.untwistedChevalleyModel_of_bridge
        CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 (MulEquiv.refl _)⟩
  exact outPNice_E7_gen hp hp2 hm

end Out

section InnGood


theorem innGoodAt_E7 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p) (h32 : ¬ (p = 3 ∧ q.card = 2)) :
    InnGoodAt p (.E7 q) (Cat ⟨.E7 q, hv⟩) := by
  obtain ⟨K, hF, hFin, -, -, ⟨ε⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
  letI : Field K := hF
  letI : Finite K := hFin
  haveI : Finite (Cat ⟨.E7 q, hv⟩) := Finite.of_equiv _ ε.symm.toEquiv
  have hZ : Subgroup.center (Cat ⟨.E7 q, hv⟩) = ⊥ := by
    rw [← Subgroup.map_center_eq ε.symm, center_adjointGroup_eq_bot, Subgroup.map_bot]
  exact innGoodAt_of_outPNice hp hZ (outPNice_cat_E7 q hv hp hp2)
    (perfectCentralizerPlanes_cat_E7 q hv hp hp2 hpq h32) (.E7 q)

theorem lieInnGood_E7 : LieInnGood fun d => ∃ q, d = .E7 q := by
  intro d p hp hp2 hpc h3 h5 hP
  obtain ⟨idx, hv⟩ := d
  obtain ⟨q, rfl⟩ := hP
  refine innGoodAt_E7 q hv hp hp2 ?_ h3
  rwa [TauCeti.LieTypeIndex.characteristic_E7 q] at hpc

end InnGood

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
