module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcTwE6Chains
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerMain
public import CFSG.LieType.SeitzGeneration.ExcTorusThreeTwCat
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcTwisted
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcVal
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResExcE
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge TauCeti CFSG.Timmesfeld.ExceptionalOrders
  CFSG.LieType.BorelTits
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevIndexTwo)

section Main


theorem noSylowNormalizesTwo_twE6 {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (hσc : ∀ c, σ c = c ^ 2 ^ n)
    (hH : Holds (twistedE6RootGroup K σ) 2) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : ¬ p ∣ 2 ^ n) {e : ℕ} (he : orderOf (((2 ^ n : ℕ)) : ZMod p) = e)
    (h34 : e = 3 ∨ e = 4) :
    NoSylowNormalizesTwo p (twistedE6RootGroup K σ) := by
  classical
  haveI : Fintype (WeylGroup TwistTag.E6.tag) := Fintype.ofFinite _
  refine noSylowNormalizesTwo_graphFixed_of_parabolic TwistTag.E6 σ hH fun J hJ hdvd => ?_
  have hfin : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨a, ha⟩ := (Set.ne_univ_iff_exists_notMem J).1 hJ
  have hsub : J ⊆ {b | b ≠ a} := fun b hb h => ha (h ▸ hb)
  have hle : graphFixedParabolic TwistTag.E6 K σ.toRingHom J ≤
      graphFixedParabolic TwistTag.E6 K σ.toRingHom {b | b ≠ a} :=
    ((fixed_standard_parabolic_cells TwistTag.E6 K σ).2.2.2.1 J _).2 hsub
  have hdvd' := hdvd.trans (Subgroup.card_dvd_of_le hle)
  have hval := (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd'
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hq : ∀ b, Nat.card (orbitField TwistTag.E6 K σ.toRingHom b) =
      (2 ^ n) ^ (TwistTag.E6.orbit b).card := card_orbitField Nat.prime_two hn hK hσc
  have hGI : GoodFactors p e twE6Full := by
    refine goodFactors_of_small hp hp5 ?_
    rcases h34 with rfl | rfl <;> decide
  have hGa : GoodFactors p e (twE6Fac a) := by
    refine goodFactors_of_small hp hp5 ?_
    rcases h34 with rfl | rfl <;> fin_cases a <;> decide
  have hcnt : cntFactors e (twE6Fac a) < cntFactors e twE6Full := by
    rcases h34 with rfl | rfl <;> fin_cases a <;> decide
  have hBne : Nat.card (graphFixedRootBorel TwistTag.E6 K σ.toRingHom) ≠ 0 := Nat.card_pos.ne'
  obtain ⟨hWne, -⟩ := factorization_prod_geomSum hp (by omega) hpq hq2 he twE6Full hGI
  obtain ⟨hAne, -⟩ := factorization_prod_geomSum hp (by omega) hpq hq2 he (twE6Fac a) hGa
  have eX : Nat.card (twistedE6RootGroup K σ) =
      Nat.card (graphFixedRootBorel TwistTag.E6 K σ.toRingHom) *
        (twE6Full.map fun f => geomSum f.1 f.2 (2 ^ n)).prod := by
    rw [← twistedParabolicSum_twE6_univ_eq, twistedParabolicSum_univ]
    exact card_graphFixedRootGroup_eq_borel_mul σ.surjective hq
  have eP : Nat.card (graphFixedParabolic TwistTag.E6 K σ.toRingHom {b | b ≠ a}) =
      Nat.card (graphFixedRootBorel TwistTag.E6 K σ.toRingHom) *
        ((twE6Fac a).map fun f => geomSum f.1 f.2 (2 ^ n)).prod := by
    rw [card_graphFixedParabolic_eq_borel_mul σ hq, foldMask_compl_E6,
      twistedParabolicSum_twE6_coat_eq]
  rw [eX, eP, Nat.factorization_mul hBne hWne, Nat.factorization_mul hBne hAne,
    Finsupp.add_apply, Finsupp.add_apply] at hval
  have hlt := factorization_prod_lt_of_cnt_lt hp (by omega) hpq hq2 he hGa hGI hcnt
  omega

theorem pClosureOdd_twistedE6 {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (hσc : ∀ c, σ c = c ^ 2 ^ n)
    (hH : Holds (twistedE6RootGroup K σ) 2) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hrk1 : ¬ RankLE1 p (twistedE6RootGroup K σ)) (hrk2 : RankLE2 p (twistedE6RootGroup K σ)) :
    PClosureOdd p (twistedE6RootGroup K σ) := by
  have hpq : ¬ p ∣ 2 ^ n := by
    intro hd'
    exact (by omega : p ≠ 2) ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      (hp.dvd_of_dvd_pow hd'))
  obtain ⟨e, he⟩ : ∃ e, orderOf (((2 ^ n : ℕ)) : ZMod p) = e := ⟨_, rfl⟩
  have h1 : 2 ≤ degCountTw e := by
    by_contra h
    exact hrk1 (rankLE1_twistedE6 Nat.prime_two hn K hK σ hσc hp hpq (by rw [he]; omega))
  have h3 : degCountTw e ≤ 2 := by
    by_contra h
    exact not_rankLE2_twistedE6 Nat.prime_two hn K hK σ hσc hp (by omega) hpq (by rw [he]; omega)
      hrk2
  have h34 : e = 3 ∨ e = 4 := degCountTw_eq_two (by omega)
  have hT : SylowTorus (twistedE6RootGroup K σ) p 2 := by
    rcases h34 with rfl | rfl
    · exact sylowTorus_twistedE6_three Nat.prime_two hn K hK σ hσc hp he
    · exact sylowTorus_twistedE6_four Nat.prime_two hn K hK σ hσc hp he
  exact pClosureOdd_of_sylowTorus hp hT (noSylowNormalizesTwo_twE6 σ hn hK hσc hH hp hp5 hpq he h34)

end Main

section Final


theorem chevTwoPClosureOddTwistedE6_holds : ChevTwoPClosureOddTwistedE6 := by
  intro p hp hp2 L _ _ hs hnab hrk hSE d hF hdi ⟨e⟩
  obtain ⟨d, hv⟩ := d
  cases d with
  | twistedE6 q =>
    have hq2 : q.p = 2 := hdi
    by_cases hp3 : p = 3
    · exfalso
      subst hp3
      exact not_rankLE2_cat_twistedE6_three q hv (by omega)
        (RankLE2.of_mulEquiv e (RankLE2.of_pRank hp hrk.le))
    · have hp5 := five_le_of_prime_ne hp hp2 hp3
      obtain ⟨K, _, σ, hK0, hσ0, ⟨eK⟩⟩ := exists_catEquiv_twistedE6 q hv
      have hn : 1 ≤ q.exponent := q.exponent_pos
      have hK : Nat.card K = (2 ^ q.exponent) ^ 2 := by rw [hK0, hq2]
      have hσc : ∀ c, σ c = c ^ 2 ^ q.exponent := fun c => by rw [hσ0 c, hq2]
      have hKfin : Finite K := Nat.finite_of_card_ne_zero (by
        rw [hK]
        exact pow_ne_zero 2 (pow_ne_zero _ two_ne_zero))
      have hK2 : Nat.card K = 2 ^ (2 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
      haveI : CharP K 2 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
          Nat.prime_two (by omega) hK2
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hTCM : TwistedChevalleyModel (ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) TwistTag.E6
          (q.p ^ q.exponent) :=
        CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
          CFSG.TauCetiBridge.Even.chevalleyBridgesEven.twistedE6 q hv hq2 (by decide)
          (MulEquiv.refl _)
      have hH0 : Holds (ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) 2 := by
        have hF2 : Fact (Nat.Prime q.p) := ⟨q.prime_p⟩
        have := holds_of_twistedChevalleyModel hn hTCM
        rwa [hq2] at this
      have hCfin : Finite (ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) :=
        Finite.of_equiv _ eK.symm.toEquiv
      have hH : Holds (twistedE6RootGroup K σ) 2 := hH0.of_mulEquiv eK
      let θ : L ≃* twistedE6RootGroup K σ := e.trans eK
      obtain ⟨hrk2, E, hE, hEc⟩ := rank_data_of_pRank hp hrk θ
      exact PClosureOdd.of_mulEquiv θ.symm
        (pClosureOdd_twistedE6 σ hn hK hσc hH hp hp5 (not_rankLE1_of_sq hp hE hEc) hrk2)
  | A _ _ => exact absurd hF (by simp [LieFamilyTwistedE6])
  | twistedA _ _ => exact absurd hF (by simp [LieFamilyTwistedE6])
  | B _ _ => exact absurd hF (by simp [LieFamilyTwistedE6])
  | C _ _ => exact absurd hF (by simp [LieFamilyTwistedE6])
  | D _ _ => exact absurd hF (by simp [LieFamilyTwistedE6])
  | twistedD _ _ => exact absurd hF (by simp [LieFamilyTwistedE6])
  | E6 _ => exact absurd hF (by simp [LieFamilyTwistedE6])
  | E7 _ => exact absurd hF (by simp [LieFamilyTwistedE6])
  | E8 _ => exact absurd hF (by simp [LieFamilyTwistedE6])
  | F4 _ => exact absurd hF (by simp [LieFamilyTwistedE6])
  | G2 _ => exact absurd hF (by simp [LieFamilyTwistedE6])
  | trialityD4 _ => exact absurd hF (by simp [LieFamilyTwistedE6])
  | suzuki _ => exact absurd hF (by simp [LieFamilyTwistedE6])
  | reeG2 _ => exact absurd hF (by simp [LieFamilyTwistedE6])
  | reeF4 _ => exact absurd hF (by simp [LieFamilyTwistedE6])
  | tits => exact absurd hF (by simp [LieFamilyTwistedE6])

end Final

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
