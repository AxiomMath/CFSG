module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResExcG2
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBG2Plane
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBG2Qplus
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBG2Split
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBG2Three
public import CFSG.RankThree.Chevalley.SteinbergCEG2EvenLocalCoreCommutator
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResExcF4
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcNum
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTorus
public import CFSG.RankThree.PartOne.K159.BorelSL
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge TauCeti CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.EvenG2 CFSG.Timmesfeld.ExceptionalOrders
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevIndexTwo)

section


theorem pClosureOdd_adjointG2 (K : Type) [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrle : RankLE2 p ↥(adjointGroup .G2 K))
    (hE₀ : ∃ E : Subgroup ↥(adjointGroup .G2 K), IsElemAbelian p E ∧ Nat.card E = p ^ 2) :
    PClosureOdd p ↥(adjointGroup .G2 K) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro d hd1 hdp
  have hord : orderOf d = p := orderOf_eq_prime hdp hd1
  have hq4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hq1 : 1 ≤ Nat.card K := by omega
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro hd'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd'))
  have hpdvd : p ∣ CFSG.Open.ordG2 (Nat.card K) := by
    rw [← card_adjointGroup_G2, ← hord]
    exact orderOf_dvd_natCard d
  have hp35 : p = 3 ∨ 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := fun h => by subst h; exact absurd hp (by norm_num)
    omega
  have hqplus : p ∣ Nat.card K + 1 →
      OddPCoreInClosure p ↥(Subgroup.centralizer ({d} : Set (adjointGroup .G2 K))) := by
    intro h
    have hT : ∃ T : Subgroup (adjointGroup .G2 K),
        T ≤ Subgroup.centralizer ({d} : Set _) ∧ Nat.card T = (Nat.card K + 1) ^ 2 := by
      rcases hp35 with rfl | hp5
      · obtain ⟨E, hE, hEc, hdE⟩ := exists_isElemAbelian_card_sq_of_mem hp hrle hE₀ hd1 hdp
        exact exists_torus_le_centralizer_qplus_three K h E hE hEc hdE
      · exact exists_torus_le_centralizer_qplus_large K hp (by omega) h hord
    exact OddPCoreInClosure.of_odd_core fun N hN hcop =>
      odd_card_of_normal_centralizer_qplus K hp hp2 h hT N hcop
  rcases hp35 with rfl | hp5
  ·
    by_cases h3 : 3 ∣ Nat.card K - 1
    · exact oddPCoreInClosure_centralizer_split_three K h3 hord
    · apply hqplus
      have : Nat.card K % 3 = 2 := by
        have h0 : ¬ 3 ∣ Nat.card K := hpK
        omega
      omega
  · rcases dvd_cases_of_dvd_ordG2 hq1 hp hpdvd hpK with h | h | h | h
    · exact oddPCoreInClosure_centralizer_split_large K hp (by omega) h hord
    · exact hqplus h
    · exact OddPCoreInClosure.of_odd_card (odd_card_centralizer_cyclotomic_of_charTwo hp
        (by omega) (Or.inr rfl) (d := Nat.card K ^ 2 + Nat.card K + 1) (by push_cast; ring) h hord)
    · have hq2 : Nat.card K ≤ Nat.card K ^ 2 := Nat.le_self_pow (by norm_num) _
      exact OddPCoreInClosure.of_odd_card (odd_card_centralizer_cyclotomic_of_charTwo hp
        (by omega) (Or.inl rfl) (d := Nat.card K ^ 2 - Nat.card K + 1)
        (by push_cast [Nat.cast_sub hq2]; ring) h hord)

end

section Final


theorem chevTwoPClosureOddG2_holds : ChevTwoPClosureOddG2 := by
  intro p hp hp2 L _ _ hs hnab hrk hSE d hF hdi ⟨e⟩
  obtain ⟨d, hv⟩ := d
  cases d with
  | G2 q =>
    have hq2 : q.p = 2 := hdi
    obtain ⟨K, _, _, hK, hchK, ⟨eK⟩⟩ :=
      exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
    haveI : CharP K 2 := hq2 ▸ hchK
    let θ : L ≃* adjointGroup Tag.G2 K := e.trans eK
    have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK, PrimePower.card_def, hq2]
    have h3 : 3 ≤ q.card := (LieTypeIndex.inStandardRange_iff _).1
      ((LieTypeIndex.valid_iff _).1 hv).1
    have hf2 : 2 ≤ q.exponent := by
      by_contra h
      have h1 : q.exponent = 1 := by have := q.exponent_pos; omega
      rw [PrimePower.card_def, hq2, h1] at h3
      omega
    obtain ⟨hrle, hE₀⟩ := rank_data_of_pRank hp hrk θ
    exact PClosureOdd.of_mulEquiv θ.symm
      (pClosureOdd_adjointG2 K hK2 hf2 hp hp2 hrle hE₀)
  | A _ _ => exact absurd hF (by simp [LieFamilyG2])
  | twistedA _ _ => exact absurd hF (by simp [LieFamilyG2])
  | B _ _ => exact absurd hF (by simp [LieFamilyG2])
  | C _ _ => exact absurd hF (by simp [LieFamilyG2])
  | D _ _ => exact absurd hF (by simp [LieFamilyG2])
  | twistedD _ _ => exact absurd hF (by simp [LieFamilyG2])
  | E6 _ => exact absurd hF (by simp [LieFamilyG2])
  | E7 _ => exact absurd hF (by simp [LieFamilyG2])
  | E8 _ => exact absurd hF (by simp [LieFamilyG2])
  | F4 _ => exact absurd hF (by simp [LieFamilyG2])
  | twistedE6 _ => exact absurd hF (by simp [LieFamilyG2])
  | trialityD4 _ => exact absurd hF (by simp [LieFamilyG2])
  | suzuki _ => exact absurd hF (by simp [LieFamilyG2])
  | reeG2 _ => exact absurd hF (by simp [LieFamilyG2])
  | reeF4 _ => exact absurd hF (by simp [LieFamilyG2])
  | tits => exact absurd hF (by simp [LieFamilyG2])

end Final

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
