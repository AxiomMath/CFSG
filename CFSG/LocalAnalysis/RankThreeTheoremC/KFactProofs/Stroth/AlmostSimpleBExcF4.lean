module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResExcF4
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcUntw
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerMain
public import CFSG.RankThree.PartOne.KF.ClsExcF4Two

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge TauCeti CFSG.Timmesfeld.ExceptionalOrders
  CFSG.RankThree.PartOne.KFU
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevIndexTwo)

section Chains

@[expose] def f4Full : List (ℕ × ℕ) := [(2, 1), (3, 1), (4, 1), (2, 3), (8, 1), (3, 4)]

@[expose] def f4Coat : Fin Tag.F4.rank → List (ℕ × ℕ) :=
  ![[(6, 1), (4, 1), (2, 1)], [(3, 1), (2, 1), (2, 1)], [(2, 1), (3, 1), (2, 1)],
    [(4, 1), (2, 3), (3, 1), (2, 1)]]

theorem chainFactors_f4ChainC3 : chainFactors f4ChainC3 = [(6, 1), (4, 1), (2, 1)] := rfl

theorem chainFactors_f4ChainA1A2 : chainFactors f4ChainA1A2 = [(3, 1), (2, 1), (2, 1)] := rfl

theorem chainFactors_f4ChainA2A1 : chainFactors f4ChainA2A1 = [(2, 1), (3, 1), (2, 1)] := rfl

theorem chainFactors_f4ChainB3 : chainFactors f4ChainB3 = [(4, 1), (2, 3), (3, 1), (2, 1)] := rfl

variable [Fintype (WeylGroup .F4)]

theorem parabolicSum_F4_univ_eq (q : ℕ) :
    parabolicSum .F4 Set.univ q = (f4Full.map fun f => geomSum f.1 f.2 q).prod := by
  rw [parabolicSum_univ, sum_length_F4]
  simp only [f4Full, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  ring

theorem parabolicSum_F4_coat_eq (i : Fin Tag.F4.rank) (q : ℕ) :
    parabolicSum .F4 (maskSet .F4 (coatomMask i)) q =
      ((f4Coat i).map fun f => geomSum f.1 f.2 q).prod := by
  fin_cases i
  · have h := parabolicSum_eq_of_chainCheck q _ _ f4ChainC3_check
    rw [chain_prod_eq, chainFactors_f4ChainC3] at h
    exact h
  · have h := parabolicSum_eq_of_chainCheck q _ _ f4ChainA1A2_check
    rw [chain_prod_eq, chainFactors_f4ChainA1A2] at h
    exact h
  · have h := parabolicSum_eq_of_chainCheck q _ _ f4ChainA2A1_check
    rw [chain_prod_eq, chainFactors_f4ChainA2A1] at h
    exact h
  · have h := parabolicSum_eq_of_chainCheck q _ _ f4ChainB3_check
    rw [chain_prod_eq, chainFactors_f4ChainB3] at h
    exact h

end Chains

section Main


theorem noSylowNormalizesTwo_F4 {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K) {e : ℕ}
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e) (h346 : e = 3 ∨ e = 4 ∨ e = 6) :
    NoSylowNormalizesTwo p (adjointGroup Tag.F4 K) := by
  classical
  haveI : Fintype (WeylGroup .F4) := Fintype.ofFinite _
  have he3 : 3 ≤ e := by omega
  have hB : 12 < p * e := by
    have := Nat.mul_le_mul hp5 he3
    omega
  refine noSylowNormalizesTwo_adjoint_of_chains .F4 hp (by omega) hpK he f4Full
    parabolicSum_F4_univ_eq coatomMask f4Coat coatomMask_cover parabolicSum_F4_coat_eq ?_ ?_ ?_
  · exact goodFactors_of_bound (by omega) hB (by decide)
  · intro i
    exact goodFactors_of_bound (by omega) hB (by fin_cases i <;> decide)
  · intro i
    rcases h346 with rfl | rfl | rfl <;> fin_cases i <;> decide

theorem sylowTorus_of_degCount_F4 (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpk : ¬ p ∣ Nat.card K) {e : ℕ}
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e) (hcnt : degCount Tag.F4 e = 2) :
    (e = 3 ∨ e = 4 ∨ e = 6) ∧ SylowTorus (adjointGroup Tag.F4 K) p 2 := by
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpk
  have hle := le_thirty_of_degCount_pos (τ := Tag.F4) (by simp) (by omega : 0 < degCount Tag.F4 e)
  have h346 : e = 3 ∨ e = 4 ∨ e = 6 := by
    interval_cases e <;> first | (left; rfl) | (right; left; rfl) | (right; right; rfl) |
      exact absurd hcnt (by decide) | omega
  have hk1 : 1 ≤ Nat.card K := Nat.card_pos
  refine ⟨h346, ?_⟩
  rcases h346 with rfl | rfl | rfl
  · exact sylowTorus_F4_three K hp hp3 (dvd_of_orderOf_three hp he)
  · exact sylowTorus_F4_four K hp hp3 (dvd_of_orderOf_four hp he)
  · exact sylowTorus_F4_six K hp hp3 (dvd_of_orderOf_six hp hk1 he)

theorem pClosureOdd_adjointF4 (K : Type) [Field K] [Finite K] [CharP K 2] {f p : ℕ}
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hrk1 : ¬ RankLE1 p (adjointGroup Tag.F4 K)) (hrk2 : RankLE2 p (adjointGroup Tag.F4 K)) :
    PClosureOdd p (adjointGroup Tag.F4 K) := by
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro hd'
    exact (by omega : p ≠ 2) ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      (hp.dvd_of_dvd_pow hd'))
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card K : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  have h1 : 2 ≤ degCount Tag.F4 e := by
    by_contra h
    exact hrk1 (rankLE1_F4 K hp hpK (by rw [he]; omega))
  have h3 : degCount Tag.F4 e ≤ 2 := by
    by_contra h
    exact not_rankLE2_F4 K hp (by omega) hpK (by rw [he]; omega) hrk2
  obtain ⟨h346, hT⟩ := sylowTorus_of_degCount_F4 K hp (by omega) hpK he (by omega)
  exact pClosureOdd_of_sylowTorus hp hT (noSylowNormalizesTwo_F4 hp hp5 hpK he h346)

end Main

section Final


theorem chevTwoPClosureOddF4_holds : ChevTwoPClosureOddF4 := by
  intro p hp hp2 L _ _ hs hnab hrk hSE d hF hdi ⟨e⟩
  obtain ⟨d, hv⟩ := d
  cases d with
  | F4 q =>
    have hq2 : q.p = 2 := hdi
    by_cases hp3 : p = 3
    · exfalso
      subst hp3
      exact not_rankLE2_cat_F4_three q hv (by omega)
        (RankLE2.of_mulEquiv e (RankLE2.of_pRank hp hrk.le))
    · have hp5 := five_le_of_prime_ne hp hp2 hp3
      obtain ⟨K, _, _, hK, hchK, ⟨eK⟩⟩ :=
        exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
      haveI : CharP K 2 := hq2 ▸ hchK
      let θ : L ≃* adjointGroup Tag.F4 K := e.trans eK
      obtain ⟨hrk2, E, hE, hEc⟩ := rank_data_of_pRank hp hrk θ
      have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK, PrimePower.card_def, hq2]
      exact PClosureOdd.of_mulEquiv θ.symm
        (pClosureOdd_adjointF4 K hK2 hp hp5 (not_rankLE1_of_sq hp hE hEc) hrk2)
  | A _ _ => exact absurd hF (by simp [LieFamilyF4])
  | twistedA _ _ => exact absurd hF (by simp [LieFamilyF4])
  | B _ _ => exact absurd hF (by simp [LieFamilyF4])
  | C _ _ => exact absurd hF (by simp [LieFamilyF4])
  | D _ _ => exact absurd hF (by simp [LieFamilyF4])
  | twistedD _ _ => exact absurd hF (by simp [LieFamilyF4])
  | E6 _ => exact absurd hF (by simp [LieFamilyF4])
  | E7 _ => exact absurd hF (by simp [LieFamilyF4])
  | E8 _ => exact absurd hF (by simp [LieFamilyF4])
  | G2 _ => exact absurd hF (by simp [LieFamilyF4])
  | twistedE6 _ => exact absurd hF (by simp [LieFamilyF4])
  | trialityD4 _ => exact absurd hF (by simp [LieFamilyF4])
  | suzuki _ => exact absurd hF (by simp [LieFamilyF4])
  | reeG2 _ => exact absurd hF (by simp [LieFamilyF4])
  | reeF4 _ => exact absurd hF (by simp [LieFamilyF4])
  | tits => exact absurd hF (by simp [LieFamilyF4])

end Final

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
