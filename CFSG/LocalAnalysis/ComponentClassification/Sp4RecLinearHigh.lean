module

public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecSmall
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorGraphField
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorOrthogonal
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorSplitFour

public noncomputable section

namespace CFSG.ComponentClassification.Sp4Rec

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.OutcomeLocal
open CFSG CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem linear_high_false {A : Type} [Group A] [Finite A] {W : Subgroup A} [W.Normal]
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLW : L ≤ W) (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A)))
    {p f : ℕ} (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2)
    (hrank : StatedClassicalModel (L ⧸ center L) .PSL 2 p f →
      2 ≤ CFSG.pRank 2 L ∨ Odd (Nat.card (center L)))
    {m ℓ e : ℕ} (hm : 5 ≤ m) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) {k : Type} [Field k]
    (hk : Nat.card k = ℓ ^ e) (φ : W ≃* projectiveSL m k) : False := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ hℓ.ne_zero)
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ he hk
  have hm3 : 3 ≤ m := by omega
  have hZ := OddSelector.center_projectiveSL_eq_bot (k := k) hm3
  obtain ⟨ρ, hinj, hρW, -, -⟩ := socle_extension hCW φ hZ
  obtain ⟨-, -, -, hL₁⟩ := OddSelector.socle_images φ hinj hρW hLW hL
  obtain ⟨-, hform⟩ := automorphism_generation (K := k) hm3
  obtain ⟨B, τ, ε, hε, hρa⟩ := hform (ρ a)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at hρa
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hρa
      obtain ⟨-, -, -, hm4⟩ :=
        OddSelector.inner_case_reduction ha (by omega) hℓ hℓ2 he hk hinj hL₁ hρa hp2 hsrc hrank
      omega
    · exact OddSelector.field_case_false ha hm3 hℓ hℓ2 he hk hinj hL₁ hτ hρa hp2 hsrc
  · rw [pow_one] at hρa
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hρa
      have hα2 : (conjAut m k B * dualAut m k) ^ 2 = 1 := by
        rw [← hρa, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
      rcases OddSelector.transpose_eq_or_eq_neg_of_pureGraph hm3 B hα2 with hB | hB
      · exact OddSelector.orthogonal_case_false hm hℓ hℓ2 he hk hinj hL₁ hρa hB hp2 hsrc
      · exact OddSelector.symplectic_case_false (by omega) hℓ hℓ2 he hk hinj hL₁ hρa hB hp2 hsrc
    · exact OddSelector.graph_field_case_false ha (by omega) hℓ hℓ2 he hk hinj hL₁ hτ hρa hp2
        hsrc

namespace Config

variable {H : Type} [Group H] [Finite H] (c : Sp4Rec.Config H)

theorem exists_src_J (hq : IsQuasisimple c.J) :
    ∃ p f : ℕ, p ≠ 2 ∧ (StatedClassicalModel (c.J ⧸ center c.J) .PSL 2 p f ∨
      Nonempty (c.J ⧸ center c.J ≃* alternatingGroup (Fin 7))) ∧ Odd (Nat.card (center c.J)) := by
  obtain ⟨hsimple, hnab⟩ := isSimpleGroup_of_isSmallAltOrL2 c.type_J
  have hZ := center_eq_pPrimeCore hq hsimple hnab
  have e : c.J ⧸ center c.J ≃* c.J ⧸ pPrimeCore 2 c.J := QuotientGroup.quotientMulEquivOfEq hZ
  have hodd : Odd (Nat.card (center c.J)) := by
    rw [hZ]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 =>
      Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h2 (pPrimeCore_coprime_card (p := 2)))
  rcases c.type_J with ⟨n, hn, ⟨e'⟩⟩ | ⟨p, f, -, hp2, -, -, hL⟩
  · rcases hn with rfl | rfl | rfl
    · exact ⟨5, 1, by decide, Or.inl
        (statedClassicalModel_psl_two_five_of_alternating_five _ ⟨e.trans e'⟩), hodd⟩
    · exact ⟨3, 2, by decide, Or.inl
        (statedClassicalModel_psl_two_nine_of_alternating_six _ ⟨e.trans e'⟩), hodd⟩
    · exact ⟨3, 1, by decide, Or.inr ⟨e.trans e'⟩, hodd⟩
  · exact ⟨p, f, hp2, Or.inl (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide)
      (LieType.CurtisTits.lieModel_of_mulEquiv e.symm hL)), hodd⟩

include c in
theorem false_of_linear_high {m p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 5 ≤ m)
    (hG : StatedClassicalModel ↥(generalizedFitting H) .PSL m p f) : False := by
  have hGn : (generalizedFitting H).Normal := LocalCores.generalized_fitting_characteristic.2
  obtain ⟨⟨-, hf, -⟩, K, _, _, hK, ⟨φ⟩⟩ := hG
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hodd : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  set φ' : ↥(generalizedFitting H) ≃* projectiveSL m K :=
    φ.trans ((projectiveSpecialLinearGroupEquivStatedProj m K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL m K)) with hφ'
  have hq := c.isQuasisimple_J_of_fixed φ' fun α hα2 hα1 L hL =>
    CatalogueBLinearHigherB.odd_higher_linear_involution_fixed_p_components m K hodd (by omega)
      α hα1 hα2 2 Nat.prime_two L hL
  obtain ⟨p', f', hp'2, hsrc, hZodd⟩ := c.exists_src_J hq
  exact linear_high_false (W := generalizedFitting H) c.centralizer_eq_bot c.orderOf_a c.J_le_G
    (c.isComponentOf_J hq) hp'2 (hsrc.elim Or.inl fun h => Or.inr (Or.inl h))
    (fun _ => Or.inr hZodd) hm hp hp2 hf hK φ'

end Config

end CFSG.ComponentClassification.Sp4Rec
