module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodE6Planes
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodE6PlanesB
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodE6PlanesC
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodE6PlanesD
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodE6ThreeDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodOut
public import CFSG.LieType.SeitzGeneration.ExcHigh.Classes
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows.F4Six
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.F4Four

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.RankThree.PartOne.KE
  CFSG.Timmesfeld.ExceptionalOrders CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.K133H
  CFSG.RankThree.PartOne.OutStructure

section Planes


theorem perfectCentralizerPlanes_adjointGroup_E6_ge_five (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K) :
    PerfectCentralizerPlanes p (adjointGroup Tag.E6 K) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hK1 : 1 ≤ Nat.card K := Nat.card_pos
  by_cases hcnt : 2 ≤ degCount Tag.E6 (orderOf ((Nat.card K : ℕ) : ZMod p))
  · rcases degCount_E6_ge_two hcnt with h1 | h2 | h3 | h4 | h6
    ·
      have hd : p ∣ Nat.card K - 1 :=
        CFSG.HardMathSupport.Timmesfeld.LocalTwo.dvd_sub_one_of_orderOf_eq_one hK1 h1
      by_cases hp7 : 7 ≤ p
      · exact perfectCentralizerPlanes_adjointGroup_E6_one K hp hp7 hd
      · have hp5' : p = 5 := by
          by_contra hne
          exact hp7 (seven_le_of_prime_of_five_lt hp (by omega))
        subst hp5'
        exact perfectCentralizerPlanes_adjointGroup_E6_five K hpK (Or.inl (by omega))
    ·
      have hd : p ∣ Nat.card K + 1 :=
        CFSG.LieType.SeitzGeneration.ExcHigh.dvd_add_one_of_orderOf_eq_two hp h2
      by_cases hp7 : 7 ≤ p
      · exact perfectCentralizerPlanes_adjointGroup_E6_two K hp hp7 hpK hd h2
      · have hp5' : p = 5 := by
          by_contra hne
          exact hp7 (seven_le_of_prime_of_five_lt hp (by omega))
        subst hp5'
        exact perfectCentralizerPlanes_adjointGroup_E6_five K hpK (Or.inr (by omega))
    ·
      have hp7 : 7 ≤ p := by
        have hq0 : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := fun h =>
          hpK ((ZMod.natCast_eq_zero_iff (Nat.card K) p).1 h)
        have hdvd : 3 ∣ p - 1 := h3 ▸ ZMod.orderOf_dvd_card_sub_one hq0
        have hpne5 : p ≠ 5 := by
          rintro rfl
          norm_num at hdvd
        exact seven_le_of_prime_of_five_lt hp (by omega)
      exact perfectCentralizerPlanes_adjointGroup_E6_three K hp hp7 hpK h3
    ·
      exact perfectCentralizerPlanes_adjointGroup_E6_four K hp hp5
        (CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.dvd_sq_add_one_of_orderOf_eq_four hp h4)
    ·
      have hd : p ∣ Nat.card K ^ 2 - Nat.card K + 1 :=
        CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows.dvd_sq_sub_self_add_one_of_orderOf_eq_six
          hp h6
      have hle : Nat.card K ≤ Nat.card K ^ 2 := Nat.le_self_pow (by norm_num) _
      refine perfectCentralizerPlanes_adjointGroup_E6_six K hp (by omega) ?_
      have hz : (((Nat.card K ^ 2 - Nat.card K + 1 : ℕ)) : ℤ) =
          (Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1 := by
        push_cast [Nat.cast_sub hle]
        ring
      rw [← hz]
      exact_mod_cast hd
  ·
    exact PerfectCentralizerPlanes.of_rankLE1 hp (rankLE1_E6 K hp hpK (by omega))

theorem perfectCentralizerPlanes_cat_E6 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E6 q).Valid) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ≠ q.p) : PerfectCentralizerPlanes p (Cat ⟨.E6 q, hv⟩) := by
  classical
  obtain ⟨K, hF, hFin, hK, -, ⟨ε⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  letI : Field K := hF
  letI : Finite K := hFin
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  exact PerfectCentralizerPlanes.of_mulEquiv ε.symm
    (perfectCentralizerPlanes_adjointGroup_E6_ge_five K hp hp5 hpK)

end Planes

section OutInn


theorem outPNice_cat_E6 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid)
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hp2 : p ≠ 2) : OutPNice p (Cat ⟨.E6 q, hv⟩) := by
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel (Cat ⟨.E6 q, hv⟩) .E6 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.untwistedChevalleyModel_of_bridge
        CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 (MulEquiv.refl _)⟩
  exact outPNice_E6_gen hp hp3 hp2 hm

theorem innGoodAt_E6_ge_five (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ≠ q.p) :
    InnGoodAt p (.E6 q) (Cat ⟨.E6 q, hv⟩) := by
  obtain ⟨K, hF, hFin, -, -, ⟨ε⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  letI : Field K := hF
  letI : Finite K := hFin
  haveI : Finite (Cat ⟨.E6 q, hv⟩) := Finite.of_equiv _ ε.symm.toEquiv
  have hZ : Subgroup.center (Cat ⟨.E6 q, hv⟩) = ⊥ := by
    rw [← Subgroup.map_center_eq ε.symm, center_adjointGroup_eq_bot, Subgroup.map_bot]
  exact innGoodAt_of_outPNice hp hZ (outPNice_cat_E6 q hv hp (by omega) (by omega))
    (perfectCentralizerPlanes_cat_E6 q hv hp hp5 hpq) (.E6 q)

end OutInn

section InnGood


theorem innGoodAt_E6_three (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid)
    (hpq : 3 ≠ q.p) (h2 : q.card ≠ 2) : InnGoodAt 3 (.E6 q) (Cat ⟨.E6 q, hv⟩) := by
  obtain ⟨K, hF, hFin, hK, hKchar, ⟨ε⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  letI : Field K := hF
  letI : Finite K := hFin
  have hK3 : ringChar K ≠ 3 := by
    rw [ringChar.eq K q.p]
    exact hpq.symm
  have h3K : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne Nat.prime_three hpq
  have hK4 : 4 ≤ Nat.card K :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.four_le_of_not_three_dvd Finite.one_lt_card h3K
      (by rw [hK]; exact h2)
  exact innGoodAt_of_mulEquiv ε.symm (innGoodAt_adjointE6_three hK3 hK4 (.E6 q))

theorem innGoodAt_E6 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p) (h32 : ¬ (p = 3 ∧ q.card = 2)) :
    InnGoodAt p (.E6 q) (Cat ⟨.E6 q, hv⟩) := by
  rcases eq_or_ne p 3 with rfl | hp3
  · exact innGoodAt_E6_three q hv hpq fun h => h32 ⟨rfl, h⟩
  · exact innGoodAt_E6_ge_five q hv hp (hp.five_le_of_ne_two_of_ne_three hp2 hp3) hpq

theorem lieInnGood_E6 : LieInnGood fun d => ∃ q, d = .E6 q := by
  intro d p hp hp2 hpc h3 h5 hP
  obtain ⟨idx, hv⟩ := d
  obtain ⟨q, rfl⟩ := hP
  refine innGoodAt_E6 q hv hp hp2 ?_ h3
  rwa [TauCeti.LieTypeIndex.characteristic_E6 q] at hpc

end InnGood

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
