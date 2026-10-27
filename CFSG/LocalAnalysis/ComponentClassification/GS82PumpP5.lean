module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP5Basic
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpMainLie
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpLeafMain
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpSpor
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpA8Lift
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpA8Leaf
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpA8Spor
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddAssemblyHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.L44CoverTrivial
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.TwoHSNoPowFour
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.TwoAltEightPowFour
public import CFSG.Sporadic.Recognition.HeMultiplierCert
public import CFSG.Sporadic.Recognition.HNMultiplierCert
public import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup

theorem not_hs_of_twoAltEight
    {H : Type} [Group H] [Finite H] {T M : Subgroup H} (hTM : T ≤ M)
    (hT : GH74.GLS.IsDoubleCoverOfAlt (T ⧸ pPrimeCore 2 T) 8)
    (hM : IsQuasisimple (M ⧸ pPrimeCore 2 M)) {m : M} (hm : m ∈ Open.fusionZStar M)
    (hm2 : orderOf m = 2) (hmT : (m : H) ∈ T) :
    ¬ Nonempty (M ⧸ Open.fusionZStar M ≃* Blueprint.NativeSporadic.Carrier .HS) := by
  rintro ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect (M ⧸ pPrimeCore 2 M) := hM.1
  have e' := (Sol78.coreQuotientCenterEquiv M).trans e
  obtain ⟨hmc, hm1⟩ := mk_mem_center_ne_one hm hm2
  have hle := Sporadic.Recognition.HSMultiplier.card_center_le_two_of_certificate this
    (e' : _ ≃* Blueprint.NativeSporadic.HS)
  have hlt : 1 < Nat.card (center (M ⧸ pPrimeCore 2 M)) := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro h
    rw [h, mem_bot] at hmc
    exact hm1 hmc
  set w : T := ⟨m, hmT⟩
  have hwM : inclusion hTM w = m := Subtype.ext rfl
  have hw2 : orderOf w = 2 := by
    rw [← Subgroup.orderOf_coe, ← hm2, ← Subgroup.orderOf_coe m]
  obtain ⟨hwc, hw1⟩ := mk_mem_center_ne_one (mem_fusionZStar_of_le hTM (hwM ▸ hm)) hw2
  obtain ⟨u, hu⟩ := CatFC.exists_pow_four_eq_of_doubleCover_alt8 hT hwc hw1
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 T) u
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hu
  set o : T := (t ^ 4)⁻¹ * w with hodef
  have hk : Odd (orderOf o) :=
    Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
      (Subgroup.orderOf_dvd_natCard _ hu)
  let φ : T →* M ⧸ pPrimeCore 2 M := (QuotientGroup.mk' (pPrimeCore 2 M)).comp (inclusion hTM)
  have hφw : φ w = QuotientGroup.mk' (pPrimeCore 2 M) m := by
    simp only [φ, MonoidHom.comp_apply, hwM]
  have h4 : φ t ^ 4 = φ w * (φ o)⁻¹ := by
    rw [← map_pow, ← map_inv, ← map_mul, hodef]
    congr 1
    group
  have hcomm : Commute (φ w) (φ o)⁻¹ := by
    rw [hφw]
    exact ((mem_center_iff.mp hmc) _).symm
  have ho : (φ o)⁻¹ ^ orderOf o = 1 := by
    rw [inv_pow, ← map_pow, pow_orderOf_eq_one, map_one, inv_one]
  have hwk : φ w ^ orderOf o = φ w := by
    have hw2' : w ^ 2 = 1 := by
      rw [← hw2]
      exact pow_orderOf_eq_one w
    obtain ⟨j, hj⟩ := hk
    rw [hj, pow_succ, pow_mul, ← map_pow, hw2', map_one, one_pow, one_mul]
  apply CatFC.pow_four_ne_of_doubleCover_hs this (by omega) ⟨e'⟩ hmc hm1 (φ t ^ orderOf o)
  rw [← pow_mul, mul_comm, pow_mul, h4, hcomm.mul_pow, ho, mul_one, hwk, hφw]

theorem altCentralPumpInput_holds :
    AltCentralPumpInput := by
  intro H _ _ hK M hM x hx hxN T hTM hTC hTpc n hn hTdc w hw hwT hwM
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hex := fusionZStar_map_le hTM hTdc.2.1 hw hwT hwM
  have eT : T ⧸ Open.fusionZStar T ≃* alternatingGroup (Fin n) :=
    (Sol78.coreQuotientCenterEquiv T).symm.trans hTdc.2.2.some
  obtain ⟨m, hm, rfl⟩ := hwM
  have hm2 : orderOf m = 2 := by rwa [← Subgroup.orderOf_coe]
  have hQ : IsQuasisimple (M ⧸ pPrimeCore 2 M) :=
    CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 M hM
  have hQO : pPrimeCore 2 (M ⧸ pPrimeCore 2 M) = ⊥ := CFSG.pPrimeCore_quotient_eq_bot Nat.prime_two
  obtain ⟨hmc, hm1⟩ := mk_mem_center_ne_one hm hm2
  have hQZ : center (M ⧸ pPrimeCore 2 M) ≠ ⊥ := by
    intro h
    rw [h, mem_bot] at hmc
    exact hm1 hmc
  have eQ := Sol78.coreQuotientCenterEquiv M
  have alt : ∀ k, 7 ≤ k → (M ⧸ Open.fusionZStar M ≃* alternatingGroup (Fin k)) →
      GH74.GLS.IsDoubleCoverOfAlt (M ⧸ pPrimeCore 2 M) k := fun k hk e =>
    isDoubleCoverOfAlt_of_center_ne_bot Alternating.Multipliers.schurAlternatingMultiplierInput hQ
      hQO hQZ (by omega) (eQ.trans e)
  have hONO := SolMax.onOuterComponentsInput_of_local SolMax.ONOut.onOuterLocalInput_holds
  rcases Nat.even_or_odd n with hev | hodd
  · rcases (show n = 8 ∨ 10 ≤ n by obtain ⟨j, rfl⟩ := hev; omega) with rfl | h10
    · rcases EvenPump.a8PumpInput_of_leaf
        (EvenPump.a8PumpLeaf_of_clauses CatLeafProof.gls3OddLieAutComponentsInput_holds
            CatLeafProof.lieOrderFormulasInput CatFC.evenOuterTypedInput_holds
            EvenPump.a8SporadicClause_holds) H hK M hM x hx hxN T hTM hTC hTpc hex ⟨eT⟩ with
        ⟨m', -, hm', ⟨e⟩⟩ | hL | hHS
      · exact ⟨m', hm', alt m' (by omega) e⟩
      · exact (hQZ (CatFC.center_eq_bot_of_quasisimple_psl44 hQ
          (Blueprint.LieModel.of_mulEquiv eQ.symm hL))).elim
      · exact (not_hs_of_twoAltEight hTM hTdc hQ hm hm2 hwT hHS).elim
    · rcases EvenPump.evenAltPumpInput_of_leaf
        (EvenPump.evenAltPumpLeaf_of_clauses CatLeafProof.gls3OddLieAutComponentsInput_holds
            CatLeafProof.lieOrderFormulasInput CatLeafProof.evenLieOuterTwoComponentsInput_holds
            (EvenPump.evenAltPumpSporadicClause_of_inputs SolMax.suzOuterComponentsInput_holds hONO)) H hK M hM x hx hxN T hTM hTC hTpc hex n hev h10
        ⟨eT⟩ with ⟨m', -, hm', ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
      · exact ⟨m', hm', alt m' (by omega) e⟩
      · exact (hQZ (Sporadic.Recognition.HNMultiplier.center_eq_bot_of_certificate hQ.1
          (Sol78.center_isPGroup_two hQO) (eQ.trans e))).elim
  · rcases SolMax.alternatingPumpUpInput_of_gls3 CatLeafProof.gls3OddLieAutComponentsInput_holds
      SolMax.suzOuterComponentsInput_holds hONO H hK M hM x hx hxN T hTM hTC hTpc hex n hodd hn
      ⟨eT⟩ with ⟨m', -, hm', ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
    · exact ⟨m', hm', alt m' (by omega) e⟩
    · exact (hQZ (Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate _ hQ
        ⟨eQ.trans e⟩)).elim

end CFSG.ComponentClassification.GS82PumpInputs
