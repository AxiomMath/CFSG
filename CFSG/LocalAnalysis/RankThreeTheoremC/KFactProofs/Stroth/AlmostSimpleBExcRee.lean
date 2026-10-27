module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcTwisted
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcVal
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResExcE
public import CFSG.RankThree.PartOne.K128.F4Syl
public import CFSG.RankThree.PartOne.S11c.Sec66F4ReeK1
public import CFSG.RankThree.PartTwo.Sec4.Census.WiringInputs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge TauCeti CFSG.Timmesfeld.ExceptionalOrders
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.BorelTits CFSG.RankThree.PartOne.K128
  CFSG.RankThree.PartOne.K1214 CFSG.RankThree.PartOne.KLR
  CFSG.RankThree.LargeReeOrder CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevIndexTwo)

open CFSG.HardMathSupport.Timmesfeld.CrossChar (rankLE1_of_pRank)

section Arith

theorem orderOf_eq_of_dvd_phiF4 {p q d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 1 ≤ q)
    (hd : d = 1 ∨ d = 2 ∨ d = 4) (h : p ∣ phiF4 d q) (hne1 : orderOf ((q : ℕ) : ZMod p) ≠ 1) :
    orderOf ((q : ℕ) : ZMod p) = d := by
  haveI : Fact p.Prime := ⟨hp⟩
  set x : ZMod p := (q : ZMod p) with hxdef
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  rcases hd with rfl | rfl | rfl
  · exfalso
    apply hne1
    have h0 : ((q - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).2 h
    rw [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at h0
    rw [← hxdef] at h0
    rw [h0, orderOf_one]
  · have h0 : ((q + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).2 h
    push_cast at h0
    have hx : x = -1 := eq_neg_of_add_eq_zero_left h0
    have hx2 : x ^ 2 = 1 := by rw [hx]; norm_num
    refine orderOf_eq_prime hx2 (fun h1 => h2 ?_)
    rw [h1] at hx
    linear_combination hx
  · have h0 : ((q ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).2 h
    push_cast at h0
    have hx4 : x ^ 4 = 1 := by
      have : x ^ 2 = -1 := eq_neg_of_add_eq_zero_left h0
      calc x ^ 4 = (x ^ 2) ^ 2 := by ring
        _ = 1 := by rw [this]; norm_num
    have hx2 : x ^ 2 ≠ 1 := by
      intro h1
      have : x ^ 2 = -1 := eq_neg_of_add_eq_zero_left h0
      rw [this] at h1
      apply h2
      linear_combination -h1
    have hdvd : orderOf x ∣ 4 := orderOf_dvd_of_pow_eq_one hx4
    have h4 : orderOf x ∣ 2 ^ 2 := by simpa using hdvd
    obtain ⟨i, hi, hie⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h4
    interval_cases i
    · exfalso
      rw [pow_zero] at hie
      rw [orderOf_eq_one_iff] at hie
      apply hx2
      rw [hie]
      norm_num
    · exfalso
      rw [pow_one] at hie
      exact hx2 (by rw [← hie]; exact pow_orderOf_eq_one x)
    · simpa using hie

end Arith

section Ree

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem noSylowNormalizesTwo_reeGamma_of_parabolic (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hpar : ∀ j : Fin F4.fixedOrbitCount,
      ¬ p ^ (Nat.card ↥(F4.reeGamma K a)).factorization p ∣ Nat.card (F4.reeLocalParabolic K a j)) :
    NoSylowNormalizesTwo p ↥(F4.reeGamma K a) := by
  intro R E hR hR2 hE hdvd
  have hfin : Finite (ModGL F4.tag K) := finite_modGL
  set A : Subgroup (ModGL F4.tag K) := E.map (F4.reeGamma K a).subtype with hA
  set R' : Subgroup (ModGL F4.tag K) := R.map (F4.reeGamma K a).subtype with hR'
  have hAΓ : A ≤ F4.reeGamma K a := Subgroup.map_subtype_le _
  have hRΓ : R' ≤ F4.reeGamma K a := Subgroup.map_subtype_le _
  have hR0 : R' ≠ ⊥ := fun h =>
    hR ((Subgroup.map_eq_bot_iff_of_injective R (F4.reeGamma K a).subtype_injective).1 h)
  have hRp : IsPGroup 2 R' := hR2.map _
  have hAR : A ≤ Subgroup.normalizer (R' : Set (ModGL F4.tag K)) :=
    (Subgroup.map_mono hE).trans (Subgroup.le_normalizer_map _)
  obtain ⟨y, hy, j, hj⟩ := exists_conj_le_reeLocalParabolic hK hAΓ hRΓ hR0 hRp hAR
  refine hpar j (hdvd.trans ?_)
  have h1 := Subgroup.card_dvd_of_le hj
  rw [Subgroup.card_map_of_injective (MulAut.conj y).injective] at h1
  rwa [hA, Subgroup.card_map_of_injective (F4.reeGamma K a).subtype_injective] at h1

theorem card_reeLocalParabolic (j : Fin F4.fixedOrbitCount) :
    Nat.card (F4.reeLocalParabolic K a j) = Nat.card (F4.reeFixedBorel K a) *
      (Nat.card (F4.reeFixedOrbitUnipotent K a j) + 1) := by
  have hfin : Finite (ModGL F4.tag K) := finite_modGL
  have hBP : F4.reeFixedBorel K a ≤ F4.reeLocalParabolic K a j :=
    reeFixedBorel_le_reeGamma_inf_parabolicSubgroup _
  have hidx : (F4.reeFixedBorel K a).relIndex (F4.reeLocalParabolic K a j) =
      Nat.card (F4.reeFixedOrbitUnipotent K a j) + 1 := by
    rw [← CFSG.QuasithinUnique.Setup.X6.ncard_image_coset_eq_relIndex]
    change (F4.reeLocalCosets K a j).ncard = _
    rw [ncard_reeLocalCosets]
  have h := Subgroup.relIndex_mul_card (F4.reeFixedBorel K a) (F4.reeLocalParabolic K a j)
  rw [inf_eq_left.2 hBP, hidx] at h
  rw [mul_comm]
  exact h.symm

theorem card_reeGamma_eq_borel_mul (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (F4.reeGamma K a) = Nat.card (F4.reeFixedBorel K a) *
      (geomSum 2 1 (2 ^ (2 * a + 1)) * geomSum 2 2 (2 ^ (2 * a + 1)) *
        (geomSum 2 3 (2 ^ (2 * a + 1)) * geomSum 2 6 (2 ^ (2 * a + 1)))) := by
  rw [(large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK).1, card_reeFixedBorel hK]
  set q := 2 ^ (2 * a + 1) with hq
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 : 1 ≤ q := by omega
  have h2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have h24 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right h1 (by norm_num)
  have h3 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  simp only [geomSum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, mul_zero, pow_zero,
    mul_one]
  zify [h1, h2, h24, h3]
  ring

theorem noSylowNormalizesTwo_ree (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : ¬ p ∣ 2 ^ (2 * a + 1)) {e : ℕ}
    (he : orderOf (((2 ^ (2 * a + 1) : ℕ)) : ZMod p) = e) (h24 : e = 2 ∨ e = 4) :
    NoSylowNormalizesTwo p ↥(F4.reeGamma K a) := by
  classical
  refine noSylowNormalizesTwo_reeGamma_of_parabolic hK fun j hdvd => ?_
  have hq2 : 2 ≤ 2 ^ (2 * a + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hfin : Finite (ModGL F4.tag K) := finite_modGL
  have hval := (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd
  have hGI : GoodFactors p e [(2, 1), (2, 2), (2, 3), (2, 6)] := by
    refine goodFactors_of_small hp hp5 ?_
    rcases h24 with rfl | rfl <;> decide
  have hBne : Nat.card (F4.reeFixedBorel K a) ≠ 0 := Nat.card_pos.ne'
  obtain ⟨hWne, -⟩ := factorization_prod_geomSum hp (by omega) hpq hq2 he
    [(2, 1), (2, 2), (2, 3), (2, 6)] hGI
  have eX : Nat.card (F4.reeGamma K a) = Nat.card (F4.reeFixedBorel K a) *
      ([(2, 1), (2, 2), (2, 3), (2, 6)].map fun f => geomSum f.1 f.2 (2 ^ (2 * a + 1))).prod := by
    rw [card_reeGamma_eq_borel_mul hK]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    ring
  have key : ∀ fs : List (ℕ × ℕ), GoodFactors p e fs →
      cntFactors e fs < cntFactors e [(2, 1), (2, 2), (2, 3), (2, 6)] →
      Nat.card (F4.reeLocalParabolic K a j) = Nat.card (F4.reeFixedBorel K a) *
        (fs.map fun f => geomSum f.1 f.2 (2 ^ (2 * a + 1))).prod → False := by
    intro fs hGs hcnt eP
    obtain ⟨hAne, -⟩ := factorization_prod_geomSum hp (by omega) hpq hq2 he fs hGs
    rw [eX, eP, Nat.factorization_mul hBne hWne, Nat.factorization_mul hBne hAne,
      Finsupp.add_apply, Finsupp.add_apply] at hval
    have hlt := factorization_prod_lt_of_cnt_lt hp (by omega) hpq hq2 he hGs hGI hcnt
    omega
  fin_cases j
  · refine key [(2, 1)] ?_ ?_ ?_
    · refine goodFactors_of_small hp hp5 ?_
      rcases h24 with rfl | rfl <;> decide
    · rcases h24 with rfl | rfl <;> decide
    · rw [card_reeLocalParabolic, card_reeFixedOrbitUnipotent_zero hK, hK]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, geomSum,
        Finset.sum_range_succ, Finset.sum_range_zero, zero_add, mul_zero, pow_zero]
      ring
  · refine key [(2, 2)] ?_ ?_ ?_
    · refine goodFactors_of_small hp hp5 ?_
      rcases h24 with rfl | rfl <;> decide
    · rcases h24 with rfl | rfl <;> decide
    · rw [card_reeLocalParabolic, card_reeFixedOrbitUnipotent_one hK, hK]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, geomSum,
        Finset.sum_range_succ, Finset.sum_range_zero, zero_add, mul_zero, pow_zero]
      ring

end Ree

@[expose] def LieFamilyReeF4Split : TauCeti.LieTypeIndex → ℕ → Prop
  | .reeF4 m, p => p = 3 ∨ orderOf (((2 ^ (2 * m + 1) : ℕ)) : ZMod p) = 1
  | _, _ => False

@[expose] def ChevTwoPClosureOddReeF4Split : Prop :=
  ChevTwoPClosureOddFamily LieFamilyReeF4Split

section Final

theorem chevTwoPClosureOddReeF4_of_split (hsplit : ChevTwoPClosureOddReeF4Split) :
    ChevTwoPClosureOddReeF4 := by
  intro p hp hp2 L _ _ hs hnab hrk hSE d hF hdi ⟨e⟩
  obtain ⟨d, hv⟩ := d
  cases d with
  | reeF4 m =>
    by_cases hS : p = 3 ∨ orderOf (((2 ^ (2 * m + 1) : ℕ)) : ZMod p) = 1
    · exact hsplit p hp hp2 L hs hnab hrk hSE ⟨.reeF4 m, hv⟩ hS hdi ⟨e⟩
    · push Not at hS
      obtain ⟨hp3, hne1⟩ := hS
      have hp5 := five_le_of_prime_ne hp hp2 hp3
      have hR0 := (CFSG.RankThree.PartTwo.Sec4.Census.bridgeExceptional46).reeF4 m hv
      have hR : ReeTitsModel L .twistedF4 2 (2 * m + 1) :=
        CFSG.SectionRank.reeTitsModel_of_mulEquiv e hR0
      obtain ⟨a, K, _, _, _, ha, hfa, hKcard, ⟨eK⟩⟩ := reeF4_model_data hR
      have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hKcard, hfa]
      have ham : a = m := by omega
      subst ham
      obtain ⟨hrk2, E, hE, hEc⟩ := rank_data_of_pRank hp hrk eK
      have hpr : 2 ≤ CFSG.pRank p (ReeTag.F4.reeGamma K a) := by
        by_contra hlt
        exact not_rankLE1_of_sq hp hE hEc (rankLE1_of_pRank hp (fun _ => by omega))
      obtain ⟨d, hd, hpd⟩ := ree_class hK hp hp5 hpr
      have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
      have hord : orderOf (((2 ^ (2 * a + 1) : ℕ)) : ZMod p) = d :=
        orderOf_eq_of_dvd_phiF4 hp hp2 hq1 hd hpd hne1
      have hd24 : d = 2 ∨ d = 4 := by
        rcases hd with h | h | h
        · exact absurd (hord.trans h) hne1
        · exact Or.inl h
        · exact Or.inr h
      have hpq : ¬ p ∣ 2 ^ (2 * a + 1) := by
        intro hd'
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd'))
      exact PClosureOdd.of_mulEquiv eK.symm
        (pClosureOdd_of_sylowShape hp (sylowShape_ree hK hd hp hp5 hpd)
          (noSylowNormalizesTwo_ree hK hp hp5 hpq hord hd24))
  | A _ _ => exact absurd hF (by simp [LieFamilyReeF4])
  | twistedA _ _ => exact absurd hF (by simp [LieFamilyReeF4])
  | B _ _ => exact absurd hF (by simp [LieFamilyReeF4])
  | C _ _ => exact absurd hF (by simp [LieFamilyReeF4])
  | D _ _ => exact absurd hF (by simp [LieFamilyReeF4])
  | twistedD _ _ => exact absurd hF (by simp [LieFamilyReeF4])
  | E6 _ => exact absurd hF (by simp [LieFamilyReeF4])
  | E7 _ => exact absurd hF (by simp [LieFamilyReeF4])
  | E8 _ => exact absurd hF (by simp [LieFamilyReeF4])
  | F4 _ => exact absurd hF (by simp [LieFamilyReeF4])
  | G2 _ => exact absurd hF (by simp [LieFamilyReeF4])
  | twistedE6 _ => exact absurd hF (by simp [LieFamilyReeF4])
  | trialityD4 _ => exact absurd hF (by simp [LieFamilyReeF4])
  | suzuki _ => exact absurd hF (by simp [LieFamilyReeF4])
  | reeG2 _ => exact absurd hF (by simp [LieFamilyReeF4])
  | tits => exact absurd hF (by simp [LieFamilyReeF4])

end Final

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
