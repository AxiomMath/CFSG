module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBOSpinTwin
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBOEvenTwin
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBDInputs
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBDCover
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePOmegaEven
public import CFSG.LieType.Steinberg.CentralExt.SpinMinus
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open Matrix CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.UnbalancingLocal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg.CentralExt
open scoped MatrixGroups

variable {J : Type} [Group J] [Finite J] (K : Subgroup J) [K.Normal]

theorem burgoynePropB_POmegaPlus (hklein : BurgoynePropBSpinPlusKleinInput)
    (hexc : BurgoynePropBDrExcInput) {t : J} {Y : Subgroup J} {c : K ⧸ pPrimeCore 2 K}
    (hH : PropBHyp J K t Y c) {n p' f' : ℕ} (hp2' : p' ≠ 2) (hn5 : 5 ≤ n)
    (hL : LieModel (GeneralizedFitting.subgroup (rhoZ K).range) .POmegaPlus n p' f') :
    ∃ u : K ⧸ pPrimeCore 2 K, orderOf u = 2 ∧ ∃ S₁ S₂ : Subgroup (K ⧸ pPrimeCore 2 K),
      S₁ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₁.subgroupOf (centralizer ({u} : Set _))) ∧
      S₂ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₂.subgroupOf (centralizer ({u} : Set _))) ∧
      (∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
        Nonempty (S₁ ≃* SL(2, GaloisField p n)) ∧ Nonempty (S₂ ≃* SL(2, GaloisField p n))) ∧
      ⁅S₁, S₂⁆ = ⊥ ∧ S₁ ⊓ S₂ = ⊥ ∧
      (center ↥(S₁ ⊔ S₂)).map (S₁ ⊔ S₂).subtype = zpowers u ⊔ zpowers c ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₁ ⊥ ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₂ ⊥ := by
  obtain ⟨hq, hM4, ht, hY1, hY2, s, hs2, -, -, Q, hQs, hQc, hQiso, hcZ, hcQ, hc2, -⟩ := id hH
  have hII : PropBHypII (K ⧸ pPrimeCore 2 K) c := ⟨s, hs2, Q, hQs, hQc, hQiso, hcZ, hcQ, hc2⟩
  obtain ⟨hsimple, hnab, -, -, -⟩ := hM4
  have hL' := hL
  rcases hL with ⟨-, hcl⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  have hmod := hcl
  obtain ⟨⟨hp, hf, -⟩, L₀, _, _, hKc, ⟨e⟩⟩ := hcl
  have : Fintype L₀ := Fintype.ofFinite L₀
  have : Fact p'.Prime := ⟨hp⟩
  have : CharP L₀ p' := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar L₀ ≠ 2 := by rw [ringChar.eq L₀ p']; exact hp2'
  have h2 : (2 : L₀) ≠ 0 := Ring.two_ne_zero hK
  have hker₀ := oKer_coordinatePlus hmod L₀ hKc e
  have hsurj₀ := oSurj_coordinatePlus hmod L₀ hKc hn5 e
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadPlus n L₀)
    (regular_coordinateQuadPlus n L₀ (by omega)).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) L₀) : Matrix _ _ L₀) *ᵥ v) =
      ((1 : L₀ˣ) : L₀) * coordinateQuadPlus n L₀ v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  have hS₁' : ∀ v, oQ R ((1 : GL (Fin (2 * n)) L₀).val *ᵥ v) =
      ((1 : L₀ˣ) : L₀) * reindexQuadraticForm (plusIndexEquiv n) (quadPlus n L₀) v := hS₁
  have hker := hker₀.transport 1 1 hS₁
  have hsurj := hsurj₀.transport 1 1 hS₁
  set θ := (coordinatePlusWitnessEquiv L₀ e).trans (oTransport 1 1 hS₁) with hθ
  set tX := (rhoZ K).rangeRestrict t with htX
  have htX2 := orderOf_rangeRestrict_of_phiO K hq ht
  have hcore_ne : oddCentralizerCore tX ≠ ⊥ := fun h => hY1 (le_bot_iff.1 (h ▸ hY2))
  obtain ⟨g, hg⟩ := hsurj (socleAction θ tX)
  by_cases hσ : g.val.right = 1
  swap
  · exact (hcore_ne (field_odd_core_bot hK (by omega) hp hf hKc hR hker hsimple hnab θ
      (hsurj.surjX θ tX) htX2 hσ hg)).elim
  rcases inner_even_twin hK (by omega) hR hker hsimple hnab θ (hsurj.surjX θ tX) htX2 hσ hg with
    h | hT | hpc
  · exact (hcore_ne h).elim
  ·
    have : NeZero n := ⟨by omega⟩
    have : Finite (spinGroup (quadPlus n L₀)) :=
      CFSG.LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n))
    refine propB_of_twinSliceData K hH hp2' hK hKc θ hT (plusIndexEquiv n) (quadPlus n L₀)
      (coe_quadPlus n L₀) (range_spinMatrix_quadPlus (by omega))
      (spinToStatedProj_quadPlus (by omega)).1 ?_ 1 1 hS₁'
      (SpinPlusClosed.quadPlus_ne_zero (by omega)) ?_
    · intro E _ _ π hπ hker2 h2'
      obtain ⟨s, hs, -⟩ :=
        CFSG.LieType.Steinberg.spinPlus_central_two_extension_splitting (by omega) hK hπ hker2 h2'
      exact ⟨s, hs⟩
    · intro α' hα'
      rcases Nat.even_or_odd n with hev | hodd
      · exact hklein L₀ hK n (by obtain ⟨k, hk⟩ := hev; omega) hev _ α' hα' c hII
      · exact spinPlus_odd_cover hK (by omega) hodd α' hα' hII
  ·
    exact (hexc J K t Y c hH .POmegaPlus n p' f' (Or.inr ⟨rfl, hn5⟩) hL' L₀ hK hKc R hR
      (Or.inl ⟨rfl, hRQ⟩) θ g hσ hg hpc).elim

theorem burgoynePropB_POmegaMinus (hexc : BurgoynePropBDrExcInput) {t : J} {Y : Subgroup J}
    {c : K ⧸ pPrimeCore 2 K} (hH : PropBHyp J K t Y c) {n p' f' : ℕ} (hp2' : p' ≠ 2)
    (hL : LieModel (GeneralizedFitting.subgroup (rhoZ K).range) .POmegaMinus n p' f') :
    ∃ u : K ⧸ pPrimeCore 2 K, orderOf u = 2 ∧ ∃ S₁ S₂ : Subgroup (K ⧸ pPrimeCore 2 K),
      S₁ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₁.subgroupOf (centralizer ({u} : Set _))) ∧
      S₂ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₂.subgroupOf (centralizer ({u} : Set _))) ∧
      (∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
        Nonempty (S₁ ≃* SL(2, GaloisField p n)) ∧ Nonempty (S₂ ≃* SL(2, GaloisField p n))) ∧
      ⁅S₁, S₂⁆ = ⊥ ∧ S₁ ⊓ S₂ = ⊥ ∧
      (center ↥(S₁ ⊔ S₂)).map (S₁ ⊔ S₂).subtype = zpowers u ⊔ zpowers c ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₁ ⊥ ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₂ ⊥ := by
  obtain ⟨hq, hM4, ht, hY1, hY2, s, hs2, -, -, Q, hQs, hQc, hQiso, hcZ, hcQ, hc2, -⟩ := id hH
  have hII : PropBHypII (K ⧸ pPrimeCore 2 K) c := ⟨s, hs2, Q, hQs, hQc, hQiso, hcZ, hcQ, hc2⟩
  obtain ⟨hsimple, hnab, -, -, -⟩ := hM4
  have hL' := hL
  rcases hL with ⟨-, hcl⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  have hmod := hcl
  obtain ⟨⟨hp, hf, hn⟩, L₀, _, _, hKc, b, c₀, hirr, ⟨e⟩⟩ := hcl
  have : Fintype L₀ := Fintype.ofFinite L₀
  have : Fact p'.Prime := ⟨hp⟩
  have : CharP L₀ p' := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar L₀ ≠ 2 := by rw [ringChar.eq L₀ p']; exact hp2'
  have h2 : (2 : L₀) ≠ 0 := Ring.two_ne_zero hK
  have hn1 : 1 ≤ n := by omega
  have hker₀ := oKer_coordinateMinus hmod L₀ hKc b c₀ hirr e
  have hsurj₀ := oSurj_coordinateMinus hmod L₀ hKc b c₀ hirr e
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadMinus n L₀ hn1 b c₀)
    (regular_coordinateQuadMinus n L₀ b c₀ hn hirr).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) L₀) : Matrix _ _ L₀) *ᵥ v) =
      ((1 : L₀ˣ) : L₀) * coordinateQuadMinus n L₀ hn1 b c₀ v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  have hS₁' : ∀ v, oQ R ((1 : GL (Fin (2 * n)) L₀).val *ᵥ v) =
      ((1 : L₀ˣ) : L₀) * reindexQuadraticForm (minusIndexEquiv n hn1) (quadMinus n L₀ b c₀) v :=
    hS₁
  have hker := hker₀.transport 1 1 hS₁
  have hsurj := hsurj₀.transport 1 1 hS₁
  set θ := (coordinateMinusWitnessEquiv L₀ hn1 b c₀ e).trans (oTransport 1 1 hS₁) with hθ
  set tX := (rhoZ K).rangeRestrict t with htX
  have htX2 := orderOf_rangeRestrict_of_phiO K hq ht
  have hcore_ne : oddCentralizerCore tX ≠ ⊥ := fun h => hY1 (le_bot_iff.1 (h ▸ hY2))
  obtain ⟨g, hg⟩ := hsurj (socleAction θ tX)
  by_cases hσ : g.val.right = 1
  swap
  · exact (hcore_ne (field_odd_core_bot hK (by omega) hp hf hKc hR hker hsimple hnab θ
      (hsurj.surjX θ tX) htX2 hσ hg)).elim
  rcases inner_even_twin hK hn hR hker hsimple hnab θ (hsurj.surjX θ tX) htX2 hσ hg with
    h | hT | hpc
  · exact (hcore_ne h).elim
  ·
    have : Finite (spinGroup (quadMinus n L₀ b c₀)) :=
      CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
        (coe_ker_spinMatrix_quadMinus (n := n) hirr)
    refine propB_of_twinSliceData K hH hp2' hK hKc θ hT (minusIndexEquiv n hn1)
      (quadMinus n L₀ b c₀) (coe_quadMinus n L₀ b c₀) (range_spinMatrix_quadMinus hn hirr)
      (spinToStatedProj_quadMinus hn hirr).1 ?_ 1 1 hS₁' SpinMinusClosed.quadMinus_ne_zero'
      (fun α' hα' => spinMinus_cover hK hKc hn hirr α' hα' hII)
    intro E _ _ π hπ hker2 h2'
    obtain ⟨s, hs, -⟩ :=
      CFSG.LieType.Steinberg.spinMinus_central_two_extension_splitting hn hK hirr hπ hker2 h2'
    exact ⟨s, hs⟩
  ·
    exact (hexc J K t Y c hH .POmegaMinus n p' f' (Or.inl rfl) hL' L₀ hK hKc R hR
      (Or.inr ⟨rfl, hn1, b, c₀, hirr, hRQ⟩) θ g hσ hg hpc).elim

end CFSG.ComponentClassification.Burgoyne.B
