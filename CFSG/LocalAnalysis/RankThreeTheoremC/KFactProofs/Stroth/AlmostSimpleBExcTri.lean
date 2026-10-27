module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcTwisted
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcVal
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResExcE
public import CFSG.RankThree.PartOne.S11d.HighRankExc
public import CFSG.RankThree.PartTwo.Sec4.Census.WiringInputs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge TauCeti CFSG.Timmesfeld.ExceptionalOrders
  CFSG.Quasithin.F134.LieD4 CFSG.LieType.BorelTits CFSG.RankThree.PartOne.K128
  CFSG.RankThree.PartOne.K1214 CFSG.RankThree.PartOne.KFU
open CFSG.RankThree.PartOne.KE (cycloVal cycloVal_twelve)
open CFSG.HardMathSupport.Timmesfeld.CrossChar (rankLE1_of_pRank)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevIndexTwo)

section Tri

open Classical in
theorem card_graphFixedRootGroup_D4_borel {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3) (hσc : ∀ c, σ c = c ^ 2 ^ n) :
    Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
      Nat.card (graphFixedRootBorel TwistTag.D4 K σ.toRingHom) *
        (geomSum 2 3 (2 ^ n) * (geomSum 3 4 (2 ^ n) * geomSum 2 1 (2 ^ n))) := by
  haveI : Fintype (WeylGroup TwistTag.D4.tag) := Fintype.ofFinite _
  rw [card_graphFixedRootGroup_eq_borel_mul σ.surjective
    (card_orbitField Nat.prime_two hn hK hσc), sum_length_relWeylTwist_D4]

theorem card_graphFixedParabolic_D4 {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3) (hσc : ∀ c, σ c = c ^ 2 ^ n)
    (a : Fin TwistTag.D4.foldedTag.rank) :
    Nat.card (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}) =
      Nat.card (graphFixedRootBorel TwistTag.D4 K σ.toRingHom) *
        geomSum 2 (TwistTag.D4.orbit a).card (2 ^ n) := by
  rw [card_graphFixedParabolic_singleton σ.surjective a,
    card_graphFixedInversionUnipotent_D4 σ hn hK hσc a]
  simp only [geomSum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, mul_zero,
    pow_zero, mul_one]

theorem noSylowNormalizesTwo_D4 {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3) (hσc : ∀ c, σ c = c ^ 2 ^ n)
    (hH : Holds (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) 2) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : ¬ p ∣ 2 ^ n) {e : ℕ} (he : orderOf (((2 ^ n : ℕ)) : ZMod p) = e)
    (h236 : e = 2 ∨ e = 3 ∨ e = 6) :
    NoSylowNormalizesTwo p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  refine noSylowNormalizesTwo_graphFixed_of_parabolic TwistTag.D4 σ hH fun J hJ hdvd => ?_
  have hfin : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem J).1 hJ
  have hex : ∀ i : Fin TwistTag.D4.foldedTag.rank, ∃ j : Fin TwistTag.D4.foldedTag.rank,
      ∀ k, k ≠ i → k = j := by decide
  obtain ⟨a, ha⟩ := hex i
  have hsub : J ⊆ {a} := fun k hk => ha k (fun h => hi (h ▸ hk))
  have hle : graphFixedParabolic TwistTag.D4 K σ.toRingHom J ≤
      graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} :=
    ((fixed_standard_parabolic_cells TwistTag.D4 K σ).2.2.2.1 J {a}).2 hsub
  have hdvd' := hdvd.trans (Subgroup.card_dvd_of_le hle)
  have hval := (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd'
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have he0 : 0 < e := by
    have : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpq
    omega
  have hk : (TwistTag.D4.orbit a).card = 1 ∨ (TwistTag.D4.orbit a).card = 3 := by
    have : ∀ c : Fin TwistTag.D4.foldedTag.rank,
        (TwistTag.D4.orbit c).card = 1 ∨ (TwistTag.D4.orbit c).card = 3 := by decide
    exact this a
  have hGI : GoodFactors p e [(2, 3), (3, 4), (2, 1)] := by
    refine goodFactors_of_small hp hp5 ?_
    rcases h236 with rfl | rfl | rfl <;> decide
  have hGa : GoodFactors p e [(2, (TwistTag.D4.orbit a).card)] := by
    refine goodFactors_of_small hp hp5 ?_
    rcases hk with hk | hk <;> rw [hk] <;> rcases h236 with rfl | rfl | rfl <;> decide
  have hcnt : cntFactors e [(2, (TwistTag.D4.orbit a).card)] <
      cntFactors e [(2, 3), (3, 4), (2, 1)] := by
    rcases hk with hk | hk <;> rw [hk] <;> rcases h236 with rfl | rfl | rfl <;> decide
  have hBne : Nat.card (graphFixedRootBorel TwistTag.D4 K σ.toRingHom) ≠ 0 := Nat.card_pos.ne'
  obtain ⟨hWne, -⟩ := factorization_prod_geomSum hp (by omega) hpq hq2 he
    [(2, 3), (3, 4), (2, 1)] hGI
  obtain ⟨hAne, -⟩ := factorization_prod_geomSum hp (by omega) hpq hq2 he
    [(2, (TwistTag.D4.orbit a).card)] hGa
  have eX : Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
      Nat.card (graphFixedRootBorel TwistTag.D4 K σ.toRingHom) *
        ([(2, 3), (3, 4), (2, 1)].map fun f => geomSum f.1 f.2 (2 ^ n)).prod := by
    rw [card_graphFixedRootGroup_D4_borel σ hn hK hσc]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have eP : Nat.card (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}) =
      Nat.card (graphFixedRootBorel TwistTag.D4 K σ.toRingHom) *
        ([(2, (TwistTag.D4.orbit a).card)].map fun f => geomSum f.1 f.2 (2 ^ n)).prod := by
    rw [card_graphFixedParabolic_D4 σ hn hK hσc a]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [eX, eP, Nat.factorization_mul hBne hWne, Nat.factorization_mul hBne hAne,
    Finsupp.add_apply, Finsupp.add_apply] at hval
  have hlt := factorization_prod_lt_of_cnt_lt hp (by omega) hpq hq2 he hGa hGI hcnt
  omega

end Tri

@[expose] def LieFamilyTrialityD4Split : TauCeti.LieTypeIndex → ℕ → Prop
  | .trialityD4 q, p => p = 3 ∨ orderOf ((q.card : ℕ) : ZMod p) = 1
  | _, _ => False

@[expose] def ChevTwoPClosureOddTrialityD4Split : Prop :=
  ChevTwoPClosureOddFamily LieFamilyTrialityD4Split

section Final

theorem chevTwoPClosureOddTrialityD4_of_split (hsplit : ChevTwoPClosureOddTrialityD4Split) :
    ChevTwoPClosureOddTrialityD4 := by
  intro p hp hp2 L _ _ hs hnab hrk hSE d hF hdi ⟨e⟩
  obtain ⟨d, hv⟩ := d
  cases d with
  | trialityD4 q =>
    have hq2 : q.p = 2 := hdi
    by_cases hS : p = 3 ∨ orderOf ((q.card : ℕ) : ZMod p) = 1
    · exact hsplit p hp hp2 L hs hnab hrk hSE ⟨.trialityD4 q, hv⟩ hS hdi ⟨e⟩
    · push Not at hS
      obtain ⟨hp3, hne1⟩ := hS
      have hp5 := five_le_of_prime_ne hp hp2 hp3
      have hn := q.exponent_pos
      have hqcard : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hq2]
      have hCEM0 := (CFSG.RankThree.PartTwo.Sec4.Census.bridgeExceptional46).trialityD4 q hv hq2
      have hCEM : ChevalleyExceptionalModel L .trialityD4 2 q.exponent :=
        CFSG.RankThree.PartOne.chevalleyExceptionalModel_congr e.symm hCEM0
      obtain ⟨K, hKf, hKfin, σ, hKcard, hσ, ⟨eL⟩⟩ :=
        exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hn hCEM.2
      have hK : Nat.card K = (2 ^ q.exponent) ^ 3 := hKcard
      have hK3 : Nat.card K = 2 ^ (3 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
      haveI : CharP K 2 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
          Nat.prime_two (by omega) hK3
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hH : Holds L 2 := holds_of_chevalleyExceptionalModel hCEM
      have hHC : Holds (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) 2 := hH.of_mulEquiv eL
      obtain ⟨hrk2, E, hE, hEc⟩ := rank_data_of_pRank hp hrk (MulEquiv.refl L)
      have hpT : p ∣ Nat.card L := by
        have h2 : p ^ 2 ∣ Nat.card L := hEc ▸ Subgroup.card_subgroup_dvd_card E
        exact (dvd_pow_self p two_ne_zero).trans h2
      have hpq : ¬ p ∣ 2 ^ q.exponent := by
        intro hd'
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd'))
      obtain ⟨m, hmem, hdvd⟩ := ((CFSG.RankThree.Chevalley.exact_E_type_and_triality_cross_prime_factor_exhaustion hp
        (by omega) (by omega : 2 ≠ p) hCEM).1 hpT).2.2.2.2 rfl
      have hd : (p : ℤ) ∣ cycloVal m 2 q.exponent := hdvd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      have hq1 : 1 ≤ 2 ^ q.exponent := Nat.one_le_two_pow
      by_cases h12 : m = 12
      · exfalso
        subst h12
        rw [cycloVal_twelve] at hd
        have hpd : p ∣ (2 ^ q.exponent) ^ 4 - (2 ^ q.exponent) ^ 2 + 1 := by
          have h24 : (2 ^ q.exponent) ^ 2 ≤ (2 ^ q.exponent) ^ 4 :=
            Nat.pow_le_pow_right hq1 (by omega)
          have h1 : (p : ℤ) ∣ (((2 ^ q.exponent) ^ 4 - (2 ^ q.exponent) ^ 2 + 1 : ℕ) : ℤ) := by
            rw [Nat.cast_add, Nat.cast_sub h24]
            push_cast
            exact hd
          exact_mod_cast h1
        obtain ⟨-, EC, hEC, hECc⟩ := rank_data_of_pRank hp hrk eL
        exact not_rankLE1_of_sq hp hEC hECc (rankLE1_of_pRank hp (fun _ =>
          pRank_le_one_D4_twelve Nat.prime_two hn K hK σ hσ hp hp5 hpd))
      have hm' : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6 := by omega
      have hpdQ : p ∣ phiNat m (2 ^ q.exponent) := dvd_phiNat_of_dvd_cycloVal hq1 hm' hd
      have hΦ : CFSG.RankThree.Chevalley.exhaustionPhi m = Polynomial.cyclotomic m ℤ := by
        rcases hm' with rfl | rfl | rfl | rfl
        · exact (Polynomial.cyclotomic_one ℤ).symm
        · exact (Polynomial.cyclotomic_two ℤ).symm
        · exact cyclotomic_three_eq.symm
        · exact cyclotomic_six_eq.symm
      have hpm : ¬ p ∣ m := not_dvd_of_small_quot hp hp5 (by omega)
      have hord : orderOf (((2 ^ q.exponent : ℕ)) : ZMod p) = m :=
        CFSG.RankThree.PartOne.KE.CTCyclo.orderOf_eq_of_dvd_cyclotomic hp hpm (by
          rw [← hΦ]
          exact hdvd)
      have hm236 : m = 2 ∨ m = 3 ∨ m = 6 := by
        rcases hm' with h | h | h | h
        · exfalso
          apply hne1
          rw [hqcard, hord, h]
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      exact PClosureOdd.of_mulEquiv eL.symm
        (pClosureOdd_of_sylowShape hp (sylowShape_D4 hn K hK σ hσ hm' hp hp5 hpdQ)
          (noSylowNormalizesTwo_D4 σ hn hK hσ hHC hp hp5 hpq hord hm236))
  | A _ _ => exact absurd hF (by simp [LieFamilyTrialityD4])
  | twistedA _ _ => exact absurd hF (by simp [LieFamilyTrialityD4])
  | B _ _ => exact absurd hF (by simp [LieFamilyTrialityD4])
  | C _ _ => exact absurd hF (by simp [LieFamilyTrialityD4])
  | D _ _ => exact absurd hF (by simp [LieFamilyTrialityD4])
  | twistedD _ _ => exact absurd hF (by simp [LieFamilyTrialityD4])
  | E6 _ => exact absurd hF (by simp [LieFamilyTrialityD4])
  | E7 _ => exact absurd hF (by simp [LieFamilyTrialityD4])
  | E8 _ => exact absurd hF (by simp [LieFamilyTrialityD4])
  | F4 _ => exact absurd hF (by simp [LieFamilyTrialityD4])
  | G2 _ => exact absurd hF (by simp [LieFamilyTrialityD4])
  | twistedE6 _ => exact absurd hF (by simp [LieFamilyTrialityD4])
  | suzuki _ => exact absurd hF (by simp [LieFamilyTrialityD4])
  | reeG2 _ => exact absurd hF (by simp [LieFamilyTrialityD4])
  | reeF4 _ => exact absurd hF (by simp [LieFamilyTrialityD4])
  | tits => exact absurd hF (by simp [LieFamilyTrialityD4])

end Final

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
