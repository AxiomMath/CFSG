module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThOrbit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OuterTrivial
public import CFSG.Sporadic.ThSchreier.NodeCentralCentralizer
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.Blueprint

@[expose] def ThThreeResidual : Prop :=
  ∀ s : ↥CFSG.Sporadic.Th.J, orderOf s = 3 →
    (∃ P : Subgroup ↥CFSG.Sporadic.Th.J,
      P ≤ Subgroup.centralizer ({s} : Set ↥CFSG.Sporadic.Th.J) ∧ IsPGroup 3 P ∧
        3 ^ 7 ≤ Nat.card P) ∧
    ∀ q : ℕ, q.Prime → 5 ≤ q →
      q ∣ Nat.card (Subgroup.centralizer ({s} : Set ↥CFSG.Sporadic.Th.J)) →
      ∃ A : Subgroup ↥CFSG.Sporadic.Th.J,
        A ≤ Subgroup.centralizer ({s} : Set ↥CFSG.Sporadic.Th.J) ∧ IsElemAbelian 3 A ∧
          Nat.card A = 9 ∧ ∀ x ∈ A, x ≠ 1 →
            ¬ q ∣ Nat.card ↥(Subgroup.centralizer ({s} : Set ↥CFSG.Sporadic.Th.J) ⊓
              Subgroup.centralizer ({x} : Set ↥CFSG.Sporadic.Th.J))

theorem OPrimeCoreTrivialAt.of_mulEquiv' {p : ℕ} {K K' : Type} [Group K] [Group K']
    (e : K ≃* K') (h : OPrimeCoreTrivialAt p K') : OPrimeCoreTrivialAt p K :=
  OPrimeCoreTrivialAt.of_mulEquiv e h

section Facts


theorem card_centralizer_involution_Th (w : ↥CFSG.Sporadic.Th.J) (hw : orderOf w = 2) :
    Nat.card (Subgroup.centralizer ({w} : Set ↥CFSG.Sporadic.Th.J)) = 92897280 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (CFSG.Sporadic.Th.Max3.all_involutions_conjugate w hw)
  rw [← hc, card_centralizer_conj]
  exact CFSG.Sporadic.ThSchreier.ctuc_Th_full_central_involution_centralizer.2.1

theorem card_isPGroup_three_le_of_involution_Th (w : ↥CFSG.Sporadic.Th.J) (hw : orderOf w = 2)
    (R : Subgroup ↥CFSG.Sporadic.Th.J) (hR : IsPGroup 3 R)
    (hRw : R ≤ Subgroup.centralizer ({w} : Set ↥CFSG.Sporadic.Th.J)) : Nat.card R ≤ 81 := by
  have : Finite ↥CFSG.Sporadic.Th.J :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  have hdvd : Nat.card R ∣ 92897280 :=
    card_centralizer_involution_Th w hw ▸ Subgroup.card_dvd_of_le hRw
  exact card_le_of_isPGroup_of_dvd Nat.prime_three hR (e := 4) (by norm_num) hdvd

theorem oPrimeCoreTrivialAt_Th_three_of_residual (h : ThThreeResidual) :
    OPrimeCoreTrivialAt 3 ↥CFSG.Sporadic.Th.J := by
  have : Finite ↥CFSG.Sporadic.Th.J :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  intro s hs
  obtain ⟨⟨P, hPC, hP, hP7⟩, hA⟩ := h s hs
  obtain ⟨a, ha⟩ := hP.exists_card_eq
  have ha7 : 7 ≤ a := by
    rw [ha] at hP7
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hP7
  refine gLAPPrimeCoreOf_eq_bot_of_orbits Nat.prime_three hPC hP ha fun q hq hq3 hqC => ?_
  by_cases hq2 : q = 2
  · subst hq2
    refine Or.inl ⟨81, fun w _ hw R hR _ hRw => card_isPGroup_three_le_of_involution_Th w hw R hR
      hRw, fun k j hk hkC hj => ?_⟩
    have hk15 : k ≤ 15 := by
      by_contra hk16
      have h1 : 2 ^ 16 ∣ Nat.card ↥CFSG.Sporadic.Th.J :=
        (pow_dvd_pow 2 (by omega)).trans (hkC.trans (Subgroup.card_subgroup_dvd_card _))
      rw [CFSG.Sporadic.Th.Max3.natCard_J] at h1
      norm_num at h1
    have hj2 : j ≤ 2 := by
      by_contra hj3
      have h27 : 3 ^ 3 ∣ 2 ^ k - 1 := (pow_dvd_pow 3 (by omega)).trans hj
      interval_cases k <;> norm_num at h27
    calc 3 ^ j * 81 ≤ 3 ^ 2 * 81 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hj2)
      _ < 3 ^ 7 := by norm_num
      _ ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) ha7
  · right
    have hq5 : 5 ≤ q := by
      have h2 := hq.two_le
      have h4 : q ≠ 4 := by
        rintro rfl
        exact absurd hq (by norm_num)
      omega
    exact hA q hq hq5 hqC

theorem sporadicOPrimeHolds_Th_three_of_residual (h : ThThreeResidual) :
    SporadicOPrimeHolds .Th 3 := by
  have hK : OPrimeCoreTrivialAt 3 (NativeSporadic.Carrier .Th) :=
    OPrimeCoreTrivialAt.of_mulEquiv' (K := NativeSporadic.Carrier .Th) (K' := CFSG.Sporadic.Th.J)
      CFSG.Sporadic.Th.thEquivJ (oPrimeCoreTrivialAt_Th_three_of_residual h)
  exact fun _ _ _ _ ⟨e⟩ => OPrimeCoreTrivialAt.of_mulEquiv e hK

theorem sporadicOnePairHolds_Th_three_of_residual
    (h : ThThreeResidual) : SporadicOnePairHolds .Th 3 :=
  ⟨sporadicOPrimeHolds_Th_three_of_residual h, sporadicOuterHolds_Th 3⟩

end Facts

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
