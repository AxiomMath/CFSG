module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcE
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResExcE

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge TauCeti CFSG.Timmesfeld.ExceptionalOrders
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevIndexTwo)

@[expose] def LieFamilyE6Four : TauCeti.LieTypeIndex → ℕ → Prop
  | .E6 q, p => orderOf ((q.card : ℕ) : ZMod p) = 4
  | _, _ => False

@[expose] def ChevTwoPClosureOddE6Four : Prop := ChevTwoPClosureOddFamily LieFamilyE6Four

@[expose] def LieFamilyE7Four : TauCeti.LieTypeIndex → ℕ → Prop
  | .E7 q, p => orderOf ((q.card : ℕ) : ZMod p) = 4
  | _, _ => False

@[expose] def ChevTwoPClosureOddE7Four : Prop := ChevTwoPClosureOddFamily LieFamilyE7Four

section


theorem chevTwoPClosureOddE6_of_four (h4 : ChevTwoPClosureOddE6Four) : ChevTwoPClosureOddE6 := by
  intro p hp hp2 L _ _ hs hnab hrk hSE d hF hdi ⟨e⟩
  obtain ⟨d, hv⟩ := d
  cases d with
  | E6 q =>
    have hq2 : q.p = 2 := hdi
    by_cases hp3 : p = 3
    · exfalso
      subst hp3
      exact not_rankLE2_cat_E6_three q hv (by omega)
        (RankLE2.of_mulEquiv e (RankLE2.of_pRank hp hrk.le))
    · have hp5 := five_le_of_prime_ne hp hp2 hp3
      obtain ⟨K, _, _, hK, hchK, ⟨eK⟩⟩ :=
        exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
      haveI : CharP K 2 := hq2 ▸ hchK
      by_cases hord : orderOf ((q.card : ℕ) : ZMod p) = 4
      · exact h4 p hp hp2 L hs hnab hrk hSE ⟨.E6 q, hv⟩ hord hdi ⟨e⟩
      · let θ : L ≃* adjointGroup Tag.E6 K := e.trans eK
        obtain ⟨hrk2, E, hE, hEc⟩ := rank_data_of_pRank hp hrk θ
        have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK, PrimePower.card_def, hq2]
        exact PClosureOdd.of_mulEquiv θ.symm
          (pClosureOdd_adjointE6 K hK2 hp hp5 (by rw [hK]; exact hord)
            (not_rankLE1_of_sq hp hE hEc) hrk2)
  | A _ _ => exact absurd hF (by simp [LieFamilyE6])
  | twistedA _ _ => exact absurd hF (by simp [LieFamilyE6])
  | B _ _ => exact absurd hF (by simp [LieFamilyE6])
  | C _ _ => exact absurd hF (by simp [LieFamilyE6])
  | D _ _ => exact absurd hF (by simp [LieFamilyE6])
  | twistedD _ _ => exact absurd hF (by simp [LieFamilyE6])
  | E7 _ => exact absurd hF (by simp [LieFamilyE6])
  | E8 _ => exact absurd hF (by simp [LieFamilyE6])
  | F4 _ => exact absurd hF (by simp [LieFamilyE6])
  | G2 _ => exact absurd hF (by simp [LieFamilyE6])
  | twistedE6 _ => exact absurd hF (by simp [LieFamilyE6])
  | trialityD4 _ => exact absurd hF (by simp [LieFamilyE6])
  | suzuki _ => exact absurd hF (by simp [LieFamilyE6])
  | reeG2 _ => exact absurd hF (by simp [LieFamilyE6])
  | reeF4 _ => exact absurd hF (by simp [LieFamilyE6])
  | tits => exact absurd hF (by simp [LieFamilyE6])

theorem chevTwoPClosureOddE7_of_four (h4 : ChevTwoPClosureOddE7Four) : ChevTwoPClosureOddE7 := by
  intro p hp hp2 L _ _ hs hnab hrk hSE d hF hdi ⟨e⟩
  obtain ⟨d, hv⟩ := d
  cases d with
  | E7 q =>
    have hq2 : q.p = 2 := hdi
    by_cases hp3 : p = 3
    · exfalso
      subst hp3
      exact not_rankLE2_cat_E7_three q hv (by omega)
        (RankLE2.of_mulEquiv e (RankLE2.of_pRank hp hrk.le))
    · have hp5 := five_le_of_prime_ne hp hp2 hp3
      obtain ⟨K, _, _, hK, hchK, ⟨eK⟩⟩ :=
        exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
      haveI : CharP K 2 := hq2 ▸ hchK
      let θ : L ≃* adjointGroup Tag.E7 K := e.trans eK
      obtain ⟨hrk2, E, hE, hEc⟩ := rank_data_of_pRank hp hrk θ
      have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK, PrimePower.card_def, hq2]
      have hpK : ¬ p ∣ Nat.card K := by
        rw [hK2]
        intro hd'
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd'))
      obtain ⟨e', he'⟩ : ∃ e', orderOf ((Nat.card K : ℕ) : ZMod p) = e' := ⟨_, rfl⟩
      have h1 : 2 ≤ degCount Tag.E7 e' := by
        by_contra h
        exact not_rankLE1_of_sq hp hE hEc (rankLE1_E7 K hp hpK (by rw [he']; omega))
      have h3 : degCount Tag.E7 e' ≤ 2 := by
        by_contra h
        exact not_rankLE2_E7 K hp (by omega) hpK (by rw [he']; omega) hrk2
      obtain ⟨h4', -⟩ := sylowTorus_of_degCount_E7 K hp hpK he' (by omega)
      subst h4'
      exact h4 p hp hp2 L hs hnab hrk hSE ⟨.E7 q, hv⟩
        (show orderOf ((q.card : ℕ) : ZMod p) = 4 by rw [← hK]; exact he') hdi ⟨e⟩
  | A _ _ => exact absurd hF (by simp [LieFamilyE7])
  | twistedA _ _ => exact absurd hF (by simp [LieFamilyE7])
  | B _ _ => exact absurd hF (by simp [LieFamilyE7])
  | C _ _ => exact absurd hF (by simp [LieFamilyE7])
  | D _ _ => exact absurd hF (by simp [LieFamilyE7])
  | twistedD _ _ => exact absurd hF (by simp [LieFamilyE7])
  | E6 _ => exact absurd hF (by simp [LieFamilyE7])
  | E8 _ => exact absurd hF (by simp [LieFamilyE7])
  | F4 _ => exact absurd hF (by simp [LieFamilyE7])
  | G2 _ => exact absurd hF (by simp [LieFamilyE7])
  | twistedE6 _ => exact absurd hF (by simp [LieFamilyE7])
  | trialityD4 _ => exact absurd hF (by simp [LieFamilyE7])
  | suzuki _ => exact absurd hF (by simp [LieFamilyE7])
  | reeG2 _ => exact absurd hF (by simp [LieFamilyE7])
  | reeF4 _ => exact absurd hF (by simp [LieFamilyE7])
  | tits => exact absurd hF (by simp [LieFamilyE7])

theorem chevTwoPClosureOddE8_holds : ChevTwoPClosureOddE8 := by
  intro p hp hp2 L _ _ hs hnab hrk hSE d hF hdi ⟨e⟩
  obtain ⟨d, hv⟩ := d
  cases d with
  | E8 q =>
    have hq2 : q.p = 2 := hdi
    by_cases hp3 : p = 3
    · exfalso
      subst hp3
      exact not_rankLE2_cat_E8_three q hv (by omega)
        (RankLE2.of_mulEquiv e (RankLE2.of_pRank hp hrk.le))
    · have hp5 := five_le_of_prime_ne hp hp2 hp3
      obtain ⟨K, _, _, hK, hchK, ⟨eK⟩⟩ :=
        exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
      haveI : CharP K 2 := hq2 ▸ hchK
      let θ : L ≃* adjointGroup Tag.E8 K := e.trans eK
      obtain ⟨hrk2, E, hE, hEc⟩ := rank_data_of_pRank hp hrk θ
      have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK, PrimePower.card_def, hq2]
      exact PClosureOdd.of_mulEquiv θ.symm
        (pClosureOdd_adjointE8 K hK2 hp hp5 (not_rankLE1_of_sq hp hE hEc) hrk2)
  | A _ _ => exact absurd hF (by simp [LieFamilyE8])
  | twistedA _ _ => exact absurd hF (by simp [LieFamilyE8])
  | B _ _ => exact absurd hF (by simp [LieFamilyE8])
  | C _ _ => exact absurd hF (by simp [LieFamilyE8])
  | D _ _ => exact absurd hF (by simp [LieFamilyE8])
  | twistedD _ _ => exact absurd hF (by simp [LieFamilyE8])
  | E6 _ => exact absurd hF (by simp [LieFamilyE8])
  | E7 _ => exact absurd hF (by simp [LieFamilyE8])
  | F4 _ => exact absurd hF (by simp [LieFamilyE8])
  | G2 _ => exact absurd hF (by simp [LieFamilyE8])
  | twistedE6 _ => exact absurd hF (by simp [LieFamilyE8])
  | trialityD4 _ => exact absurd hF (by simp [LieFamilyE8])
  | suzuki _ => exact absurd hF (by simp [LieFamilyE8])
  | reeG2 _ => exact absurd hF (by simp [LieFamilyE8])
  | reeF4 _ => exact absurd hF (by simp [LieFamilyE8])
  | tits => exact absurd hF (by simp [LieFamilyE8])

end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
