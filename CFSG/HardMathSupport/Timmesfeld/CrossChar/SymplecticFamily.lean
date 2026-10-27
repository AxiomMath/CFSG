module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SymplecticPlaneQ
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SymplecticOuter
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeCCarrier
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem isLocallyBalancedAbs_psp {ℓ f r : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = ℓ ^ f) (hr : 2 ≤ r) (hrq : ¬ (r = 2 ∧ ℓ ^ f = 2)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) :
    IsLocallyBalancedAbs p 3 (StatedProj (StatedSp r K)) := by
  intro D hD hcard H hH _
  obtain ⟨E, hED, hEin, hE, hEc⟩ := exists_inner_plane_psp hℓ hf hr hK hp (by omega) D hD hcard
  exact le_bot_iff.1 ((localDeltaIn_antitone H hED).trans
    (localDeltaIn_eq_bot_psp hℓ hf hK hp hp3 hpℓ hr hrq E hEin hE hEc hH).le)

theorem isLocallyBalancedAbs_psp_q {ℓ f r : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = ℓ ^ f) (hq : 4 ≤ ℓ ^ f) (hr : 2 ≤ r) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) : IsLocallyBalancedAbs p 3 (StatedProj (StatedSp r K)) := by
  intro D hD hcard H hH _
  obtain ⟨E, hED, hEin, hE, hEc⟩ := exists_inner_plane_psp hℓ hf hr hK hp hp2 D hD hcard
  exact le_bot_iff.1 ((localDeltaIn_antitone H hED).trans
    (localDeltaIn_eq_bot_psp_q hℓ hf hK hq hp hp2 hpℓ hr E hEin hE hEc hH).le)

theorem isLocallyBalancedAbs_psp_of_odd {ℓ f r : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] (hK : Nat.card K = ℓ ^ f) (hr : 2 ≤ r) (hrq : ¬ (r = 2 ∧ ℓ ^ f = 2)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (h32 : ¬ (p = 3 ∧ ℓ ^ f = 2)) :
    IsLocallyBalancedAbs p 3 (StatedProj (StatedSp r K)) := by
  by_cases hp3 : 3 < p
  · exact isLocallyBalancedAbs_psp hℓ hf hK hr hrq hp hp3 hpℓ
  · have hp3' : p = 3 := by have := hp.two_le; omega
    subst hp3'
    have hq : 4 ≤ ℓ ^ f := by
      have h2 : 2 ≤ ℓ ^ f := hℓ.two_le.trans (Nat.le_self_pow (by omega) ℓ)
      have hq3 : ℓ ^ f ≠ 3 := fun h => hpℓ ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).mp
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_three (by rw [h] : 3 ∣ ℓ ^ f)))
      have hq2 : ℓ ^ f ≠ 2 := fun h => h32 ⟨rfl, h⟩
      omega
    exact isLocallyBalancedAbs_psp_q hℓ hf hK hq hr hp hp2 hpℓ

theorem crossCharFamCat_C : CrossCharFamCat .C := by
  rintro ⟨d, hv⟩ ⟨r, q, hd⟩ p hp hp2 hc
  change d = _ at hd
  subst hd
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hr : 3 ≤ r := hrange.1
  have hq2 : q.p ≠ 2 := hrange.2
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
    (⟨.C r q, hv⟩ : TauCeti.ValidLieTypeIndex)
  have hK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField
      (⟨.C r q, hv⟩ : TauCeti.ValidLieTypeIndex)) = q.p ^ q.exponent := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField]
    simp [TauCeti.ValidLieTypeIndex.fieldOrder]
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hodd : ¬ (p = 3 ∧ q.p ^ q.exponent = 2) := by
    rintro ⟨-, h⟩
    have h1 : q.p ∣ 2 := h ▸ dvd_pow_self q.p q.exponent_pos.ne'
    exact hq2 ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp h1)
  exact IsLocallyBalancedAbs.of_mulEquiv
    (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv)
    (isLocallyBalancedAbs_psp_of_odd q.prime_p q.exponent_pos hK (by omega) (by omega) hp hp2 hpq
      hodd)

end CFSG.HardMathSupport.Timmesfeld.CrossChar
