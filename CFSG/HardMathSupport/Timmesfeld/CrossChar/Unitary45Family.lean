module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary45Main
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary32Family

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem isLocallyBalancedAbs_primeFormP_three_two_small (h : UnitaryFieldData ℓ f K)
    (hq : ℓ ^ f = 2) (hn : n = 4 ∨ n = 5) :
    IsLocallyBalancedAbs 3 3 (primeFormP h (idGram K n)) := by
  intro D hD hcard H hH _
  exact localDeltaIn_eq_bot_three_two_small h hq hn D hD (by rw [hcard]; norm_num)
    (le_innerAut_primeFormP_three_two h hq (by omega) (fun h' => by omega) (by omega) hD) hH

@[expose] def regimeTwistedAThreeTwoSmall (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .twistedA r q ∧ p = 3 ∧ q.card = 2 ∧
    (r + 1 = 4 ∨ r + 1 = 5)

theorem crossCharFamAt_twistedA_threeTwo_small :
    CrossCharFamAt .twistedA regimeTwistedAThreeTwoSmall := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨r, q, hd, rfl, h2, h45⟩
  change d = _ at hd
  subst hd
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv
    (MulEquiv.refl (Cat ⟨.twistedA r q, hv⟩))
  obtain ⟨⟨hℓ, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hq2 : q.p ^ q.exponent = 2 := hcard ▸ h2
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := r + 1) (K := K))
  let e : Cat ⟨.twistedA r q, hv⟩ ≃* primeFormP h (idGram K (r + 1)) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_primeFormP_three_two_small h hq2 h45)

@[expose] def regimeTwistedAThreeTwoDiag (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .twistedA r q ∧ p = 3 ∧ q.card = 2 ∧
    (3 ∣ r + 1 ∨ r + 1 ≤ 3)

theorem crossCharFamAt_twistedA_threeTwo_of_rest_diag
    (hdiag : CrossCharFamAt .twistedA regimeTwistedAThreeTwoDiag) :
    CrossCharFamAt .twistedA regimeTwistedAThreeTwoRest := by
  intro idx hk p hp hp2 hc ⟨r, q, hd, h3, h2, hr⟩
  by_cases h45 : r + 1 = 4 ∨ r + 1 = 5
  · exact crossCharFamAt_twistedA_threeTwo_small idx hk p hp hp2 hc ⟨r, q, hd, h3, h2, h45⟩
  · refine hdiag idx hk p hp hp2 hc ⟨r, q, hd, h3, h2, ?_⟩
    omega

end CFSG.HardMathSupport.Timmesfeld.CrossChar
