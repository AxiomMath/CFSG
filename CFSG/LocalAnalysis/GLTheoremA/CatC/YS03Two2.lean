module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03Two
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03Spor
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenFinal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenFinal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThirteen
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Seven
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFive
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03Mod
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03J4
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26Comp
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsHatSixCore
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AModel
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCOut
public import CFSG.HardMathSupport.Solomon.LocalBalance.ONFacts
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeFrontier
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Top
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionCyclic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionShadow
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.A3Structure314Defs
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.C1PackS15212C
public import CFSG.Quasithin.Background.C1PackS1531Top
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.F918H5
public import CFSG.Quasithin.Background.FFC4Tr2
public import CFSG.Quasithin.Background.GoldschmidtS146RBend1
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructFieldExt
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructPGL
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructSimple
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S14610Q1
public import CFSG.Quasithin.EmptyFaithful.S14610Top
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S152Y15
public import CFSG.Quasithin.EmptyFaithful.S152Y19
public import CFSG.Quasithin.EmptyFaithful.S153E59A
public import CFSG.Quasithin.EmptyFaithful.T1515Der
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.Recognition.ModelBridges
public import CFSG.Quasithin.Vol2.Ch10SecB4
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch1EightFourChar2
public import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Tools
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3315R
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323B
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3329
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3330

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicOnePair)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (ys03_sporadicLocalOnePairs)

@[expose] def SporOPrimePair (name : TauCeti.SporadicName) (p : ℕ) : Prop :=
  (name = .Th ∧ p = 5) ∨ (name = .M ∧ p = 11) ∨ (name = .M ∧ p = 13) ∨ (name = .Fi24Prime ∧ p = 7) ∨
    (name = .McL ∧ p = 5) ∨ (name = .HS ∧ p = 5) ∨ (name = .Ru ∧ p = 5) ∨ (name = .ONan ∧ p = 7) ∨
    (name = .He ∧ p = 7) ∨ (name = .J4 ∧ p = 11)

@[expose] def KD1912TwoLie (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, k2Lie p d.1 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) → ∀ A : Subgroup (MulAut S),
        IsElemAbelian p A → IsTwoPrimaryWeaklyLocallyBalanced p 1 A

theorem k2Lie_cases {p : ℕ} {d : TauCeti.LieTypeIndex} (h : k2Lie p d) : p = 3 ∨ p = 5 ∨ p = 13 := by
  unfold k2Lie at h
  split at h <;> (try simp only [Nat.even_iff, Nat.odd_iff] at h) <;> omega

theorem kd1912TwoLie_all (h3 : KD1912TwoLie 3) (h5 : KD1912TwoLie 5) (h13 : KD1912TwoLie 13)
    (p : ℕ) : KD1912TwoLie p := by
  intro S _ _ hS hnc d hd e A hA
  rcases k2Lie_cases hd with rfl | rfl | rfl
  · exact h3 S hS hnc d hd e A hA
  · exact h5 S hS hnc d hd e A hA
  · exact h13 S hS hnc d hd e A hA

theorem k2Spor_cases {p : ℕ} {name : TauCeti.SporadicName} (h : k2Spor p name) :
    SporadicOnePair name p ∨ (name = .M11 ∧ p = 3) ∨ (name = .M12 ∧ p = 11) ∨
      SporOPrimePair name p := by
  have hp : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 := by
    cases name <;> simp [k2Spor] at h <;> omega
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> cases name <;>
    simp [k2Spor, SporadicOnePair, SporOPrimePair] at h ⊢


theorem ys03_two_M11
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) (e : S ≃* (TauCeti.CFSGIndex.sporadic .M11).Group)
    {A : Subgroup (MulAut S)} (hA : IsElemAbelian 3 A) :
    IsTwoPrimaryWeaklyLocallyBalanced 3 1 A := by
  refine ys03_weak_of_coreFree Nat.prime_three (fun x hx hx1 H hH hxH => ?_) hA
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ys03_oneBalanced_M11 hS hnc ⟨e⟩ x
    (orderOf_eq_prime hx hx1) H hH hxH

theorem ys03_two_M12
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) (e : S ≃* (TauCeti.CFSGIndex.sporadic .M12).Group)
    {A : Subgroup (MulAut S)} (hA : IsElemAbelian 11 A) :
    IsTwoPrimaryWeaklyLocallyBalanced 11 1 A := by
  haveI := hS
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .M12
  let e' : S ≃* CFSG.Blueprint.NativeSporadic.M12 := e.trans b.symm
  have hcardS : Nat.card S = 95040 := by
    rw [Nat.card_congr e'.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M12
  have hAut : Nat.card (MulAut S) ≤ 2 * 95040 := by
    rw [Nat.card_congr (MulAut.congr e').toEquiv]
    have := CFSG.Sporadic.Schreier.m12_mulAut_card
    rwa [CFSG.Sporadic.Mathieu.card_M12] at this
  have hZ : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      exact hab ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm)
  have hInn : 95040 ∣ Nat.card (MulAut S) := by
    have h1 : Nat.card (innerAut S) = Nat.card S :=
      (Nat.card_congr (MonoidHom.ofInjective (ys03_conj_injective hZ)).toEquiv).symm
    rw [← hcardS, ← h1]
    exact Subgroup.card_subgroup_dvd_card _
  have hp11 : IsPGroup 11 A := by
    haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    exact isPGroup_of_isElemAbelian hA
  refine ys03_weak_of_card_le (by norm_num) ?_
  obtain ⟨k, hk⟩ := hp11.exists_card_eq
  have hdvd : Nat.card A ∣ Nat.card (MulAut S) := Subgroup.card_subgroup_dvd_card A
  obtain ⟨c, hc⟩ := hInn
  have hpos : 0 < Nat.card (MulAut S) := Nat.card_pos
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0, mul_zero] at hc
      omega
    · exact h0
  have hc2 : c ≤ 2 := by
    by_contra hc3
    have : 95040 * 3 ≤ 95040 * c := Nat.mul_le_mul_left _ (by omega)
    omega
  rw [hk] at hdvd ⊢
  rw [hc] at hdvd
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k <;> norm_num
  · exfalso
    have h121 : 11 ^ 2 ∣ 11 ^ k := pow_dvd_pow 11 hk2
    have := h121.trans hdvd
    interval_cases c <;> norm_num at this

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance in
theorem ys03_two_oPrimePairs
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a) {name : TauCeti.SporadicName}
    (e : S ≃* (TauCeti.CFSGIndex.sporadic name).Group) (hpair : SporOPrimePair name p)
    {A : Subgroup (MulAut S)} (hA : IsElemAbelian p A) :
    IsTwoPrimaryWeaklyLocallyBalanced p 1 A := by
  unfold SporOPrimePair at hpair
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ys03_weak_of_sporadicOPrime hp hp2 sporadicOPrimeHolds_Th_five hS hnc e hA
  · exact ys03_weak_of_sporadicOPrime hp hp2 sporadicOPrimeHolds_M_eleven hS hnc e hA
  · exact ys03_weak_of_sporadicOPrime hp hp2 (sporadicOPrimeHolds_M_thirteen_of
      bThirteenOddCore_holds) hS hnc e hA
  · exact ys03_weak_of_sporadicOPrime hp hp2 sporadicOPrimeHolds_Fi24_seven hS hnc e hA
  · exact ys03_weak_of_sporadicOPrime hp hp2 ys03_sporadicOPrimeHolds_McL_five hS hnc e hA
  · exact ys03_weak_of_sporadicOPrime hp hp2 ys03_sporadicOPrimeHolds_HS_five hS hnc e hA
  · exact ys03_weak_of_sporadicOPrime hp hp2 ys03_sporadicOPrimeHolds_Ru_five hS hnc e hA
  · exact ys03_weak_of_sporadicOPrime hp hp2 ys03_sporadicOPrimeHolds_ONan_seven hS hnc e hA
  · exact ys03_weak_of_sporadicOPrime hp hp2 ys03_sporadicOPrimeHolds_He_seven hS hnc e hA
  · exact ys03_weak_of_sporadicOPrime hp hp2 ys03_sporadicOPrimeHolds_J4_eleven hS hnc e hA

theorem ys03_two_spor_pair
    {p : ℕ} (hp : p.Prime) {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a) {name : TauCeti.SporadicName}
    (e : S ≃* (TauCeti.CFSGIndex.sporadic name).Group) (hpair : SporadicOnePair name p)
    {A : Subgroup (MulAut S)} (hA : IsElemAbelian p A) :
    IsTwoPrimaryWeaklyLocallyBalanced p 1 A := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ys03_weak_of_coreFree hp (fun x hx hx1 H hH hxH => ?_) hA
  exact ys03_sporadicLocalOnePairs S hS hnc name ⟨e⟩ p hp hpair x (orderOf_eq_prime hx hx1) H hH hxH

theorem kd1912Two_of_parts
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hLie : KD1912TwoLie p) :
    KD1912Two p := by
  intro S _ _ hS hnc hk A hA
  obtain ⟨i, hi, ⟨e⟩⟩ := hk
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating n hn => exact ys03_two_alt hp hp2 hn hi hS hnc e hA
  | lie d => exact hLie S hS hnc d hi ⟨e⟩ A hA
  | sporadic s =>
    rcases k2Spor_cases hi with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
    · exact ys03_two_spor_pair hp hS hnc e h hA
    · exact ys03_two_M11 hS hnc e hA
    · exact ys03_two_M12 hS hnc e hA
    · exact ys03_two_oPrimePairs hp hp2 hS hnc e h hA

end CFSG.LocalAnalysis.GLTheoremA
