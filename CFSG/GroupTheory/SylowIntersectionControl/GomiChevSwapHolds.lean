module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevAtomOrbitHolds
import CFSG.GH74.GLS.Stage4.HexModelD4
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevAtomTransport
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevNodeSwap
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevSwapClassical
import CFSG.LieType.Chevalley.PosUnipotentSylow
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6G2

public section

namespace CFSG.GroupTheory

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.Stage4.Hex

theorem gomiAtomsFixed_adjointGroup_G2
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F) :
    GomiAtomsFixed ↥(adjointGroup .G2 F) := by
  have : Finite (ModGL .G2 F) := finite_modGL
  have hUC : posUnipotent .G2 F ≤ adjointGroup .G2 F := posUnipotent_le_adjointGroup
  refine gomiAtomsFixed_of_covBy_imp
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_subgroupOf_top
      (isSylowTwoOf_posUnipotent .G2))
    (P := fun i => (parabolicSubgroup .G2 F {i}).subgroupOf (adjointGroup .G2 F)) ?_ ?_
  · intro A hA
    have h1 : IsGomiAtom ⊤ ((posUnipotent .G2 F).subgroupOf (adjointGroup .G2 F)) A :=
      (isGomiAtom_top_iff_covBy _ _).2 hA
    have h2 : IsGomiAtom (adjointGroup .G2 F) (posUnipotent .G2 F)
        (A.map (adjointGroup .G2 F).subtype) := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hUC]
      exact (isGomiAtom_map_subtype_iff (adjointGroup .G2 F) _ A).2 h1
    obtain ⟨hcover, hAle⟩ := (isGomiAtom_iff_covBy _ _ _).1 h2
    rw [(borel_self_normalizers .G2 F).1] at hcover
    obtain ⟨i, hi⟩ := (borelGroup_covBy_iff hAle).1 hcover
    refine ⟨i, ?_⟩
    rw [← hi]
    exact (Subgroup.comap_map_eq_self_of_injective
      (adjointGroup .G2 F).subtype_injective A).symm
  · intro α i hα
    exact CFSG.QuasithinUnique.Setup.X6.G2_invariant_parabolic hF hα i

theorem gomiAtomsFixed_of_lie_G2
    {K : Type} [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower}
    (hd : d.1 = .G2 q) (hq : q.p = 2) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    GomiAtomsFixed K := by
  obtain ⟨dd, hv⟩ := d
  obtain rfl : dd = .G2 q := hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hq3 : 3 ≤ q.card :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
  have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hq
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hq
    (GaloisField q.p q.exponent) hcard
  have hexp : 2 ≤ q.exponent := by
    by_contra h
    have h1 : q.exponent = 1 := by
      have := q.exponent_pos
      omega
    rw [TauCeti.PrimePower.card_def, hq, h1] at hq3
    norm_num at hq3
  have h4 : 4 ≤ Nat.card (GaloisField q.p q.exponent) := by
    rw [hcard, TauCeti.PrimePower.card_def, hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hexp
  have : Finite ↥(adjointGroup .G2 (GaloisField q.p q.exponent)) := generated_group_finite .G2 _
  have hc : Subgroup.center ↥(adjointGroup .G2 (GaloisField q.p q.exponent)) = ⊥ :=
    center_adjointGroup_eq_bot
  exact GomiAtomsFixed.of_mulEquiv
    ((e.trans b.symm).trans
      ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot))
    (gomiAtomsFixed_adjointGroup_G2 h4)

theorem gomiNoAtomSwap_of_lie_F4
    {K : Type} [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower}
    (hd : d.1 = .F4 q) (hq : q.p = 2) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    GomiNoAtomSwap K := by
  obtain ⟨dd, hv⟩ := d
  obtain rfl : dd = .F4 q := hd
  obtain ⟨F, _, _, hK, ⟨φ⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.chevalleyBridgesEven.f4 q hv hq e
  have : CharP F 2 :=
    hq ▸ CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      q.prime_p q.exponent_pos hK
  have : Finite ↥(adjointGroup .F4 F) := generated_group_finite .F4 F
  exact gomiNoAtomSwap_of_borelQuotient
    (CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional.borelQuotient_f4 φ)
    (by show Tag.rank .F4 ≠ 2; decide)

theorem gomiNoAtomSwap_of_lie_E6
    {K : Type} [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower}
    (hd : d.1 = .E6 q) (hq : q.p = 2) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    GomiNoAtomSwap K := by
  obtain ⟨dd, hv⟩ := d
  obtain rfl : dd = .E6 q := hd
  obtain ⟨F, _, _, hK, ⟨φ⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e6 q hv hq e
  have : CharP F 2 :=
    hq ▸ CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      q.prime_p q.exponent_pos hK
  have : Finite ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup F) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup
      CFSG.LieType.Steinberg.Minuscule.e6Data_valid F
  exact gomiNoAtomSwap_of_borelQuotient
    (CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional.borelQuotient_e6 φ)
    (by show Tag.rank .E6 ≠ 2; decide)

theorem gomiNoAtomSwap_of_lie_E7
    {K : Type} [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower}
    (hd : d.1 = .E7 q) (hq : q.p = 2) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    GomiNoAtomSwap K := by
  obtain ⟨dd, hv⟩ := d
  obtain rfl : dd = .E7 q := hd
  obtain ⟨F, _, _, hK, ⟨φ⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e7 q hv hq e
  have : CharP F 2 :=
    hq ▸ CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      q.prime_p q.exponent_pos hK
  have : Finite ↥(CFSG.LieType.Steinberg.Minuscule.e7Data_valid.minGroup F) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup
      CFSG.LieType.Steinberg.Minuscule.e7Data_valid F
  exact gomiNoAtomSwap_of_borelQuotient
    (CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional.borelQuotient_e7 φ)
    (by show Tag.rank .E7 ≠ 2; decide)

theorem gomiNoAtomSwap_of_lie_E8
    {K : Type} [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower}
    (hd : d.1 = .E8 q) (hq : q.p = 2) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    GomiNoAtomSwap K := by
  obtain ⟨dd, hv⟩ := d
  obtain rfl : dd = .E8 q := hd
  obtain ⟨F, _, _, hK, ⟨φ⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e8 q hv hq e
  have : CharP F 2 :=
    hq ▸ CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      q.prime_p q.exponent_pos hK
  have : Finite ↥(adjointGroup .E8 F) := generated_group_finite .E8 F
  exact gomiNoAtomSwap_of_borelQuotient
    (CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional.borelQuotient_e8 φ)
    (by show Tag.rank .E8 ≠ 2; decide)

theorem gomiNoAtomSwap_of_lie_twistedE6
    {K : Type} [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower}
    (hd : d.1 = .twistedE6 q) (hq : q.p = 2) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    GomiNoAtomSwap K := by
  obtain ⟨dd, hv⟩ := d
  obtain rfl : dd = .twistedE6 q := hd
  obtain ⟨F, _, _, hK, σ, hσ, ⟨φ⟩⟩ := CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.chevalleyBridgesEven.twistedE6 q hv hq (by decide) e
  have hK' : Nat.card F = (q.p ^ q.exponent) ^ 2 := hK
  have : CharP F 2 := by
    have h := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      q.prime_p (show 1 ≤ q.exponent * 2 by have := q.exponent_pos; omega)
      (show Nat.card F = q.p ^ (q.exponent * 2) by rw [hK', pow_mul])
    rwa [hq] at h
  have h2le : 2 ≤ q.p ^ q.exponent := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) q.exponent_pos
  have hθ :=
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional.involutive_of_card hK' hσ
  have : Finite ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup F) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup
      CFSG.LieType.Steinberg.Minuscule.e6Data_valid F
  have : Finite ↥(CFSG.LieType.Steinberg.TwistedE6.fixedGroup F σ) := Subtype.finite
  have hK4 : 4 ≤ Nat.card F := by
    rw [hK']
    calc 4 ≤ 2 ^ 2 := by norm_num
      _ ≤ (q.p ^ q.exponent) ^ 2 := Nat.pow_le_pow_left h2le 2
  exact gomiNoAtomSwap_of_borelQuotient
    (CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional.borelQuotient_e6tw
      hθ hK4 hK' hσ φ)
    (by show Tag.rank .F4 ≠ 2; decide)

theorem gomiNoAtomSwap_of_mulEquiv_alternatingGroup_five
    {K : Type} [Group K] [Finite K] (e : K ≃* alternatingGroup (Fin 5)) : GomiNoAtomSwap K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero 2 := ⟨by norm_num⟩
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl hK)
  exact gomiNoAtomSwap_of_borelQuotient
    (CFSG.AGLEmbedding.ParabHub.borelQuotient_sl (m := 1) (F := GaloisField 2 2)
      (((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
        (GaloisField 2 2)).trans e5).trans e.symm))
    (by show (1 : ℕ) ≠ 2; decide)

theorem gomiNoAtomSwap_of_mulEquiv_alternatingGroup_eight {K : Type} [Group K] [Finite K]
    (e : K ≃* alternatingGroup (Fin 8)) : GomiNoAtomSwap K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero 1 := ⟨by norm_num⟩
  obtain ⟨e8⟩ := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff
    (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (GaloisField 2 1))).1
    CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_four_two_lieModel
  exact gomiNoAtomSwap_of_borelQuotient
    (CFSG.AGLEmbedding.ParabHub.borelQuotient_sl (m := 3) (F := GaloisField 2 1)
      (e8.trans e.symm))
    (by show (3 : ℕ) ≠ 2; decide)

section TrialityD4Aux


private theorem gomiNoAtomSwap_of_lie_trialityD4_aux
    {K : Type} [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower}
    (hd : d.1 = .trialityD4 q) (hq : q.p = 2) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    GomiNoAtomSwap K := by
  obtain ⟨dd, hv⟩ := d
  obtain rfl : dd = .trialityD4 q := hd
  obtain ⟨F, _, _, hK, σ, hσ, ⟨φ⟩⟩ := CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hv hq (by decide) e
  have hF' : Nat.card F = (q.p ^ q.exponent) ^ 3 := hK
  have : CharP F 2 := by
    have h := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      q.prime_p (show 1 ≤ q.exponent * 3 by have := q.exponent_pos; omega)
      (show Nat.card F = q.p ^ (q.exponent * 3) by rw [hF', pow_mul])
    rwa [hq] at h
  have h2le : 2 ≤ q.p ^ q.exponent := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) q.exponent_pos
  have : Finite ↥(adjointGroup d4 F) := generated_group_finite d4 F
  have : Finite ↥(twistedGroup σ) := Subtype.finite
  have hσ3 := CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card hF' hσ
  let i0 : Fin (Tag.rank .G2) := ng 0
  let i1 : Fin (Tag.rank .G2) := ng 1
  refine gomiNoAtomSwap_of_borelQuotient_card_ne
    (CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional.borelQuotient_d4tw
      h2le hF' hσ φ) (i := i0) (j := i1) ?_
  show Nat.card ↥(twistedRootGroup σ (Pi.single i0 1)) ≠
    Nat.card ↥(twistedRootGroup σ (Pi.single i1 1))
  have hlong : Nat.card ↥(twistedRootGroup σ (Pi.single i0 1)) = q.p ^ q.exponent :=
    (card_twistedRootGroup_long hσ3 (isRoot_single .G2 i0) (by decide)).trans
      (card_fixedField_of_cube σ h2le hF' hσ)
  have hshort : Nat.card ↥(twistedRootGroup σ (Pi.single i1 1)) =
      (q.p ^ q.exponent) ^ 3 :=
    (card_twistedRootGroup_short hσ3 (isRoot_single .G2 i1) (by decide)).trans hF'
  intro h
  rw [hlong, hshort] at h
  have hlt : (q.p ^ q.exponent) ^ 1 < (q.p ^ q.exponent) ^ 3 :=
    Nat.pow_lt_pow_right (by omega) (by norm_num)
  rw [pow_one] at hlt
  omega

end TrialityD4Aux

theorem gomiNoAtomSwap_of_lie_trialityD4
    {K : Type} [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower}
    (hd : d.1 = .trialityD4 q) (hq : q.p = 2) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    GomiNoAtomSwap K := by
  exact gomiNoAtomSwap_of_lie_trialityD4_aux hd hq e

section LieDispatchAux


private theorem gomiSwapTop_of_lie_aux
    {K : Type} [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex)
    (hd : AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsChevIndexTwo d.1)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : GomiSwapTop K := by
  obtain ⟨i, hv⟩ := d
  cases i with
  | A r q =>
    exact gomiSwapTop_of_lie_A (d := ⟨.A r q, hv⟩) rfl hd e
  | twistedA r q =>
    exact (gomiNoAtomSwap_of_lie_twistedA (d := ⟨.twistedA r q, hv⟩) rfl hd e).gomiSwapTop
  | B r q =>
    exact gomiSwapTop_of_lie_B (d := ⟨.B r q, hv⟩) rfl hd e
  | C r q =>
    exfalso
    have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    rw [TauCeti.LieTypeIndex.inStandardRange_iff] at h
    exact h.2 hd
  | D r q =>
    exact (gomiNoAtomSwap_of_lie_D (d := ⟨.D r q, hv⟩) rfl hd e).gomiSwapTop
  | twistedD r q =>
    exact (gomiNoAtomSwap_of_lie_twistedD (d := ⟨.twistedD r q, hv⟩) rfl hd e).gomiSwapTop
  | G2 q =>
    exact (gomiAtomsFixed_of_lie_G2 (d := ⟨.G2 q, hv⟩) rfl hd e).gomiNoAtomSwap.gomiSwapTop
  | E6 q =>
    exact (gomiNoAtomSwap_of_lie_E6 (d := ⟨.E6 q, hv⟩) rfl hd e).gomiSwapTop
  | E7 q =>
    exact (gomiNoAtomSwap_of_lie_E7 (d := ⟨.E7 q, hv⟩) rfl hd e).gomiSwapTop
  | E8 q =>
    exact (gomiNoAtomSwap_of_lie_E8 (d := ⟨.E8 q, hv⟩) rfl hd e).gomiSwapTop
  | F4 q =>
    exact (gomiNoAtomSwap_of_lie_F4 (d := ⟨.F4 q, hv⟩) rfl hd e).gomiSwapTop
  | twistedE6 q =>
    exact (gomiNoAtomSwap_of_lie_twistedE6 (d := ⟨.twistedE6 q, hv⟩) rfl hd e).gomiSwapTop
  | trialityD4 q =>
    exact (gomiNoAtomSwap_of_lie_trialityD4 (d := ⟨.trialityD4 q, hv⟩) rfl hd e).gomiSwapTop
  | suzuki m =>
    have h := (gomiAtomsFixed_of_lie_suzuki (d := ⟨.suzuki m, hv⟩) rfl e).gomiNoAtomSwap
    exact h.gomiSwapTop
  | reeG2 m =>
    exact absurd hd (by simp [AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsChevIndexTwo])
  | reeF4 m =>
    exact (gomiAtomsFixed_of_lie_reeF4 (d := ⟨.reeF4 m, hv⟩) rfl e).gomiNoAtomSwap.gomiSwapTop
  | tits =>
    exact (gomiAtomsFixed_of_lie_tits (d := ⟨.tits, hv⟩) rfl e).gomiNoAtomSwap.gomiSwapTop

end LieDispatchAux

theorem gomiSwapTop_of_lie
    {K : Type} [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex)
    (hd : AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsChevIndexTwo d.1)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : GomiSwapTop K := by
  exact gomiSwapTop_of_lie_aux d hd e

theorem gomiSwapTop_of_isChevTwo
    {K : Type} [Group K] [Finite K]
    (h : AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsChevTwo K) : GomiSwapTop K := by
  rcases h with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hdq, ⟨e⟩⟩
  · exact gomiSwapTop_of_lie d hd e
  · rcases hn with rfl | rfl | rfl
    · exact (gomiNoAtomSwap_of_mulEquiv_alternatingGroup_five e).gomiSwapTop
    · exact gomiSwapTop_of_isGomiSp4 (Or.inl ⟨e⟩)
    · exact (gomiNoAtomSwap_of_mulEquiv_alternatingGroup_eight e).gomiSwapTop
  · rcases hdq with ⟨q, hq, hdq⟩ | ⟨q, hq, hdq⟩
    · exact gomiSwapTop_of_isGomiL3 ⟨d, Or.inr ⟨q, hq, hdq⟩, ⟨e⟩⟩
    · exact (gomiAtomsFixed_of_lie_twistedA_three hq hdq e).gomiNoAtomSwap.gomiSwapTop

theorem gomiChevSwap_holds :
    GomiChevSwap :=
  gomiChevSwap_of_top fun _ _ _ _ _ h => gomiSwapTop_of_isChevTwo h

end CFSG.GroupTheory
