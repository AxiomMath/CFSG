module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddJ
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF4G2Aux
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal
  CFSG.HardMathSupport.Seitz.TrialityOdd.Inner CFSG.RankThree.PartOne.SEITZ3
  CFSG.RankThree.PartOne.K1214 CFSG.RankThree.PartOne.SEITZ11.G2Seven
  CFSG.RankThree.PartTwo.KFacts CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.ClassicalInvolution.G2D4Models CFSG.LieType.HighestRoot CFSG.RankThree.PartTwo.Sec19
  CFSG.RankThree.PartOne.CTP
open scoped MatrixGroups

section Dict

variable
  {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

@[expose] def triOddJRootEquiv :
    ↥((graphFixedRootGroup TwistTag.D4 (fixSubfield σ)
      (fixSubfieldRestrict σ σ).toRingHom).map
        (baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield σ).subtype)) ≃*
      ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield σ) (RingHom.id (fixSubfield σ))) :=
  (Subgroup.equivMapOfInjective _ (baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield σ).subtype)
    (baseChangeGL_injective _)).symm.trans
    (MulEquiv.subgroupCongr (by rw [fixSubfieldRestrict_toRingHom_eq_id]))

theorem triOdd_baseChange_jRootEquiv (w : ↥((graphFixedRootGroup TwistTag.D4 (fixSubfield σ)
      (fixSubfieldRestrict σ σ).toRingHom).map
        (baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield σ).subtype))) :
    baseChangeGL (fixSubfield σ).subtype
      ((triOddJRootEquiv σ w : ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield σ) (RingHom.id (fixSubfield σ)))) :
        ModGL TwistTag.D4.tag (fixSubfield σ)) = (w : ModGL TwistTag.D4.tag K) := by
  unfold triOddJRootEquiv
  rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
  have h := Subgroup.coe_equivMapOfInjective_apply
    (graphFixedRootGroup TwistTag.D4 (fixSubfield σ) (fixSubfieldRestrict σ σ).toRingHom)
    (baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield σ).subtype) (baseChangeGL_injective _)
    ((Subgroup.equivMapOfInjective
      (graphFixedRootGroup TwistTag.D4 (fixSubfield σ) (fixSubfieldRestrict σ σ).toRingHom)
      (baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield σ).subtype)
      (baseChangeGL_injective _)).symm w)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

@[expose] def triOddJG2Equiv (hk3 : (3 : ℕ∞) ≤ ENat.card (fixSubfield σ)) :
    ↥((graphFixedRootGroup TwistTag.D4 (fixSubfield σ)
      (fixSubfieldRestrict σ σ).toRingHom).map
        (baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield σ).subtype)) ≃*
      ↥(adjointGroup Tag.G2 (fixSubfield σ)) :=
  (triOddJRootEquiv σ).trans
    ((MulEquiv.subgroupCongr
      (d4_twistedFixedGroup_id_eq_graphFixedRootGroup (K := fixSubfield σ))).symm.trans
      (d4FixedG2EquivAll (fixSubfield σ) hk3))

section Model

variable (hK2 : ringChar K ≠ 2) {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 3)
  (hσq : ∀ c, σ c = c ^ q) (hσ3 : ∀ c, σ (σ (σ c)) = c)

@[expose] def triOddFixJEquiv :
    ↥(FixedSub σ) ≃* ↥((graphFixedRootGroup TwistTag.D4 (fixSubfield σ)
      (fixSubfieldRestrict σ σ).toRingHom).map
        (baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield σ).subtype)) :=
  MulEquiv.ofBijective
    (((twistedIncl σ.toRingHom).comp (FixedSub σ).subtype).codRestrict
      ((graphFixedRootGroup TwistTag.D4 (fixSubfield σ)
        (fixSubfieldRestrict σ σ).toRingHom).map
          (baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield σ).subtype))
      (fun z => (mem_J_iff σ hK2 hq hK hσq hσ3 z.1).2 z.2))
    ⟨fun a b h => by
      have h1 : twistedIncl σ.toRingHom a.1 = twistedIncl σ.toRingHom b.1 :=
        congrArg (Subtype.val : ↥((graphFixedRootGroup TwistTag.D4 (fixSubfield σ)
          (fixSubfieldRestrict σ σ).toRingHom).map
            (baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield σ).subtype)) →
              ModGL TwistTag.D4.tag K) h
      exact Subtype.ext
        (CFSG.ClassicalInvolution.G2D4Models.twistedIncl_injective σ.toRingHom h1), by
      rintro ⟨g, hg⟩
      have hgC : g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
        d4_trialityFieldImage_self_le σ hg
      have h := CFSG.LieType.Steinberg.CentralExt.TrialityClosed.map_twistedGroup_eq_graphFixedRootGroup
        (σ := σ.toRingHom) hK2 hq hK hσq
      rw [← h] at hgC
      obtain ⟨a, ha, rfl⟩ := hgC
      exact ⟨⟨⟨a, ha⟩, (mem_J_iff σ hK2 hq hK hσq hσ3 ⟨a, ha⟩).1 hg⟩, rfl⟩⟩

@[expose] def triOddJDict (hk3 : (3 : ℕ∞) ≤ ENat.card (fixSubfield σ)) :
    ↥(FixedSub σ) ≃* ↥(adjointGroup Tag.G2 (fixSubfield σ)) :=
  (triOddFixJEquiv σ hK2 hq hK hσq hσ3).trans (triOddJG2Equiv σ hk3)

theorem triOddJDict_coe_of (hk3 : (3 : ℕ∞) ≤ ENat.card (fixSubfield σ)) (z : ↥(FixedSub σ))
    (u : ModGL TwistTag.D4.tag (fixSubfield σ))
    (hu : u ∈ twistedFixedGroup TwistTag.D4 (fixSubfield σ) (RingHom.id (fixSubfield σ)))
    (hz : baseChangeGL (fixSubfield σ).subtype u = twistedIncl σ.toRingHom (z : twistedGroup σ.toRingHom)) :
    ((triOddJDict σ hK2 hq hK hσq hσ3 hk3 z : ↥(adjointGroup Tag.G2 (fixSubfield σ))) :
        ModGL Tag.G2 (fixSubfield σ)) =
      d4FixedToG2 (fixSubfield σ) ⟨u, hu⟩ := by
  set v := triOddJRootEquiv σ (triOddFixJEquiv σ hK2 hq hK hσq hσ3 z) with hv
  have h1 : baseChangeGL (fixSubfield σ).subtype
      ((v : ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield σ) (RingHom.id (fixSubfield σ)))) :
        ModGL TwistTag.D4.tag (fixSubfield σ)) =
      twistedIncl σ.toRingHom (z : twistedGroup σ.toRingHom) :=
    triOdd_baseChange_jRootEquiv σ (triOddFixJEquiv σ hK2 hq hK hσq hσ3 z)
  have h2 : ((v : ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield σ) (RingHom.id (fixSubfield σ)))) :
        ModGL TwistTag.D4.tag (fixSubfield σ)) = u :=
    baseChangeGL_injective (fixSubfield σ).subtype (h1.trans hz.symm)
  have h3 : triOddJDict σ hK2 hq hK hσq hσ3 hk3 z =
      d4FixedG2EquivAll (fixSubfield σ) hk3
        ((MulEquiv.subgroupCongr
          (d4_twistedFixedGroup_id_eq_graphFixedRootGroup (K := fixSubfield σ))).symm v) := rfl
  rw [h3, coe_d4FixedG2EquivAll]
  congr 1
  exact Subtype.ext h2

end Model

section Bridge


theorem triOdd_coe_xPar_simple_unit {L : Type} [Field L] [Finite L] (i : Fin d4.rank) {p : ℕ}
    (hp : CFSG.LieType.Steinberg.TwistedD4.d4Root p = Pi.single i 1) (c : L) :
    ((xPar (rootOperatorFamily d4) (Pi.single i 1) c : adjointGroup d4 L) : ModGL d4 L) =
      xUnit d4 L i c := by
  have h := CFSG.RankThree.PartTwo.Sec19.xd_simple_unit (X := L) i hp c
  simpa only [CFSG.RankThree.PartOne.SEITZ7.xd, hp] using h

theorem triOdd_coe_xPar_neg_simple_unit {L : Type} [Field L] [Finite L] (i : Fin d4.rank) {p : ℕ}
    (hp : CFSG.LieType.Steinberg.TwistedD4.d4Root p = -Pi.single i 1) (c : L) :
    ((xPar (rootOperatorFamily d4) (-Pi.single i 1) c : adjointGroup d4 L) : ModGL d4 L) =
      yUnit d4 L i c := by
  have h := CFSG.RankThree.PartTwo.Sec19.xd_neg_simple_unit (X := L) i hp c
  simpa only [CFSG.RankThree.PartOne.SEITZ7.xd, hp] using h

end Bridge

section Gen

variable (hK2 : ringChar K ≠ 2) {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 3)
  (hσq : ∀ c, σ c = c ^ q) (hσ3 : ∀ c, σ (σ (σ c)) = c)
  (hk3 : (3 : ℕ∞) ≤ ENat.card (fixSubfield σ))

include hσ3 in
theorem triOdd_twistedIncl_slLong_upper_unit (c : fixedField σ.toRingHom) :
    twistedIncl σ.toRingHom (slLong σ.toRingHom hσ3 (sl2Upper c)) =
      xUnit TwistTag.D4.tag K (nd 2) (c : K) := by
  exact (twistedIncl_slLong_upper (σ := σ.toRingHom) hσ3 c).trans
    (triOdd_coe_xPar_simple_unit (L := K) (nd 2) (p := 2) CFSG.RankThree.PartOne.SEITZ8.d4Root_simple_2 _)

include hσ3 in
theorem triOdd_twistedIncl_slLong_lower_unit (c : fixedField σ.toRingHom) :
    twistedIncl σ.toRingHom (slLong σ.toRingHom hσ3 (sl2Lower c)) =
      yUnit TwistTag.D4.tag K (nd 2) (c : K) := by
  exact (twistedIncl_slLong_lower (σ := σ.toRingHom) hσ3 c).trans
    (triOdd_coe_xPar_neg_simple_unit (L := K) (nd 2) (p := 8) CFSG.RankThree.PartOne.SEITZ8.d4Root_neg_2 _)

include hσ3 in
theorem triOdd_twistedIncl_slShort_upper_unit (c : K) (hc : σ c = c) :
    twistedIncl σ.toRingHom (slShort σ.toRingHom hσ3 (sl2Upper c)) =
      xUnit TwistTag.D4.tag K (nd 0) c * xUnit TwistTag.D4.tag K (nd 1) c *
        xUnit TwistTag.D4.tag K (nd 3) c := by
  have h := twistedIncl_slShort_upper (σ := σ.toRingHom) hσ3 c
  have hc' : σ.toRingHom c = c := hc
  refine h.trans ?_
  simp only [xOuter, Subgroup.coe_mul, one_smul, hc']
  rw [triOdd_coe_xPar_simple_unit (L := K) (nd 0) (p := 0) CFSG.RankThree.PartOne.SEITZ8.d4Root_simple_0,
    triOdd_coe_xPar_simple_unit (L := K) (nd 1) (p := 1) CFSG.RankThree.PartOne.SEITZ8.d4Root_simple_1,
    triOdd_coe_xPar_simple_unit (L := K) (nd 3) (p := 3) CFSG.RankThree.PartOne.SEITZ8.d4Root_simple_3]

include hσ3 in
theorem triOdd_twistedIncl_slShort_lower_unit (c : K) (hc : σ c = c) :
    twistedIncl σ.toRingHom (slShort σ.toRingHom hσ3 (sl2Lower c)) =
      yUnit TwistTag.D4.tag K (nd 0) c * yUnit TwistTag.D4.tag K (nd 1) c *
        yUnit TwistTag.D4.tag K (nd 3) c := by
  have h := twistedIncl_slShort_lower (σ := σ.toRingHom) hσ3 c
  have hc' : σ.toRingHom c = c := hc
  refine h.trans ?_
  simp only [xOuter, Subgroup.coe_mul, neg_smul, one_smul, hc']
  rw [triOdd_coe_xPar_neg_simple_unit (L := K) (nd 0) (p := 4) CFSG.RankThree.PartOne.SEITZ8.d4Root_neg_0,
    triOdd_coe_xPar_neg_simple_unit (L := K) (nd 1) (p := 6) CFSG.RankThree.PartOne.SEITZ8.d4Root_neg_1,
    triOdd_coe_xPar_neg_simple_unit (L := K) (nd 3) (p := 10) CFSG.RankThree.PartOne.SEITZ8.d4Root_neg_3]

omit hσ3 in
theorem triOdd_g2OrbitXUnit_short {L : Type} [Field L] (c : L) :
    g2OrbitXUnit L g2s c = xUnit TwistTag.D4.tag L (nd 0) c * xUnit TwistTag.D4.tag L (nd 1) c *
      xUnit TwistTag.D4.tag L (nd 3) c := by
  have h : TwistTag.D4.orbitWord (g2FoldedIndex g2s) = [nd 0, nd 1, nd 3] := by decide
  rw [g2OrbitXUnit, h]
  simp [mul_assoc]

omit hσ3 in
theorem triOdd_g2OrbitYUnit_short {L : Type} [Field L] (c : L) :
    g2OrbitYUnit L g2s c = yUnit TwistTag.D4.tag L (nd 0) c * yUnit TwistTag.D4.tag L (nd 1) c *
      yUnit TwistTag.D4.tag L (nd 3) c := by
  have h : TwistTag.D4.orbitWord (g2FoldedIndex g2s) = [nd 0, nd 1, nd 3] := by decide
  rw [g2OrbitYUnit, h]
  simp [mul_assoc]

include hσ3 in
theorem triOdd_map_sigma_map_subtype (M : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ.toRingHom)) :
    Matrix.SpecialLinearGroup.map σ.toRingHom
      (Matrix.SpecialLinearGroup.map (fixedField σ.toRingHom).subtype M) =
      Matrix.SpecialLinearGroup.map (fixedField σ.toRingHom).subtype M := by
  refine Subtype.ext ?_
  ext i j
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact (M.1 i j).2

include hσ3 in
@[expose] def triOddSlLongJ : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ.toRingHom) →* ↥(FixedSub σ) :=
  (slLong σ.toRingHom hσ3).codRestrict (FixedSub σ) (slLong_mem_FixedSub σ hσ3)

include hσ3 in
@[expose] def triOddSlShortJ :
    Matrix.SpecialLinearGroup (Fin 2) (fixedField σ.toRingHom) →* ↥(FixedSub σ) :=
  ((slShort σ.toRingHom hσ3).comp
    (Matrix.SpecialLinearGroup.map (fixedField σ.toRingHom).subtype)).codRestrict (FixedSub σ)
      (fun M => slShort_mem_FixedSub σ hσ3 _ (triOdd_map_sigma_map_subtype σ hσ3 M))

theorem triOddJDict_slLongJ_upper (c : fixedField σ.toRingHom) :
    triOddJDict σ hK2 hq hK hσq hσ3 hk3 (triOddSlLongJ σ hσ3 (sl2Upper c)) =
      g2RootSL2 g2l (fixSubfield σ) (sl2Upper c) := by
  apply Subtype.ext
  have hz : baseChangeGL (fixSubfield σ).subtype (g2OrbitXUnit (fixSubfield σ) g2l c) =
      twistedIncl σ.toRingHom
        ((triOddSlLongJ σ hσ3 (sl2Upper c) : ↥(FixedSub σ)) : twistedGroup σ.toRingHom) := by
    rw [baseChangeGL_g2OrbitXUnit]
    exact (CFSG.RankThree.PartTwo.Sec19.bridge_g2OrbitXUnit_long (c : K)).trans
      (triOdd_twistedIncl_slLong_upper_unit σ hσ3 c).symm
  rw [triOddJDict_coe_of σ hK2 hq hK hσq hσ3 hk3 _ _ (g2OrbitXUnit_mem g2l c) hz,
    d4FixedToG2_g2OrbitXUnitAll]
  exact (simpleRootSL2_uSL g2l c).symm

theorem triOddJDict_slLongJ_lower (c : fixedField σ.toRingHom) :
    triOddJDict σ hK2 hq hK hσq hσ3 hk3 (triOddSlLongJ σ hσ3 (sl2Lower c)) =
      g2RootSL2 g2l (fixSubfield σ) (sl2Lower c) := by
  apply Subtype.ext
  have hz : baseChangeGL (fixSubfield σ).subtype (g2OrbitYUnit (fixSubfield σ) g2l c) =
      twistedIncl σ.toRingHom
        ((triOddSlLongJ σ hσ3 (sl2Lower c) : ↥(FixedSub σ)) : twistedGroup σ.toRingHom) := by
    rw [baseChangeGL_g2OrbitYUnit]
    exact (CFSG.RankThree.PartTwo.Sec19.bridge_g2OrbitYUnit_long (c : K)).trans
      (triOdd_twistedIncl_slLong_lower_unit σ hσ3 c).symm
  rw [triOddJDict_coe_of σ hK2 hq hK hσq hσ3 hk3 _ _ (g2OrbitYUnit_mem g2l c) hz,
    d4FixedToG2_g2OrbitYUnitAll]
  exact (simpleRootSL2_vSL g2l c).symm

theorem triOddJDict_slShortJ_upper (c : fixedField σ.toRingHom) :
    triOddJDict σ hK2 hq hK hσq hσ3 hk3 (triOddSlShortJ σ hσ3 (sl2Upper c)) =
      g2RootSL2 g2s (fixSubfield σ) (sl2Upper c) := by
  apply Subtype.ext
  have hc : σ (c : K) = c := c.2
  have hz : baseChangeGL (fixSubfield σ).subtype (g2OrbitXUnit (fixSubfield σ) g2s c) =
      twistedIncl σ.toRingHom
        ((triOddSlShortJ σ hσ3 (sl2Upper c) : ↥(FixedSub σ)) : twistedGroup σ.toRingHom) := by
    rw [baseChangeGL_g2OrbitXUnit]
    have e : Matrix.SpecialLinearGroup.map (fixedField σ.toRingHom).subtype (sl2Upper c) =
        sl2Upper (c : K) := map_uSL _ c
    show _ = twistedIncl σ.toRingHom (slShort σ.toRingHom hσ3
      (Matrix.SpecialLinearGroup.map (fixedField σ.toRingHom).subtype (sl2Upper c)))
    rw [e]
    exact (triOdd_g2OrbitXUnit_short (c : K)).trans (triOdd_twistedIncl_slShort_upper_unit σ hσ3 (c : K) hc).symm
  rw [triOddJDict_coe_of σ hK2 hq hK hσq hσ3 hk3 _ _ (g2OrbitXUnit_mem g2s c) hz,
    d4FixedToG2_g2OrbitXUnitAll]
  exact (simpleRootSL2_uSL g2s c).symm

theorem triOddJDict_slShortJ_lower (c : fixedField σ.toRingHom) :
    triOddJDict σ hK2 hq hK hσq hσ3 hk3 (triOddSlShortJ σ hσ3 (sl2Lower c)) =
      g2RootSL2 g2s (fixSubfield σ) (sl2Lower c) := by
  apply Subtype.ext
  have hc : σ (c : K) = c := c.2
  have hz : baseChangeGL (fixSubfield σ).subtype (g2OrbitYUnit (fixSubfield σ) g2s c) =
      twistedIncl σ.toRingHom
        ((triOddSlShortJ σ hσ3 (sl2Lower c) : ↥(FixedSub σ)) : twistedGroup σ.toRingHom) := by
    rw [baseChangeGL_g2OrbitYUnit]
    have e : Matrix.SpecialLinearGroup.map (fixedField σ.toRingHom).subtype (sl2Lower c) =
        sl2Lower (c : K) := map_vSL _ c
    show _ = twistedIncl σ.toRingHom (slShort σ.toRingHom hσ3
      (Matrix.SpecialLinearGroup.map (fixedField σ.toRingHom).subtype (sl2Lower c)))
    rw [e]
    exact (triOdd_g2OrbitYUnit_short (c : K)).trans (triOdd_twistedIncl_slShort_lower_unit σ hσ3 (c : K) hc).symm
  rw [triOddJDict_coe_of σ hK2 hq hK hσq hσ3 hk3 _ _ (g2OrbitYUnit_mem g2s c) hz,
    d4FixedToG2_g2OrbitYUnitAll]
  exact (simpleRootSL2_vSL g2s c).symm

theorem triOddJDict_slLongJ (M : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ.toRingHom)) :
    triOddJDict σ hK2 hq hK hσq hσ3 hk3 (triOddSlLongJ σ hσ3 M) = g2RootSL2 g2l (fixSubfield σ) M := by
  have h : ((triOddJDict σ hK2 hq hK hσq hσ3 hk3).toMonoidHom.comp (triOddSlLongJ σ hσ3)) =
      g2RootSL2 g2l (fixSubfield σ) :=
    MonoidHom.eq_of_eqOn_dense
      (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := fixedField σ.toRingHom))
      (by
        rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
        · exact triOddJDict_slLongJ_upper σ hK2 hq hK hσq hσ3 hk3 c
        · exact triOddJDict_slLongJ_lower σ hK2 hq hK hσq hσ3 hk3 c)
  exact DFunLike.congr_fun h M

theorem triOddJDict_slShortJ (M : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ.toRingHom)) :
    triOddJDict σ hK2 hq hK hσq hσ3 hk3 (triOddSlShortJ σ hσ3 M) = g2RootSL2 g2s (fixSubfield σ) M := by
  have h : ((triOddJDict σ hK2 hq hK hσq hσ3 hk3).toMonoidHom.comp (triOddSlShortJ σ hσ3)) =
      g2RootSL2 g2s (fixSubfield σ) :=
    MonoidHom.eq_of_eqOn_dense
      (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := fixedField σ.toRingHom))
      (by
        rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
        · exact triOddJDict_slShortJ_upper σ hK2 hq hK hσq hσ3 hk3 c
        · exact triOddJDict_slShortJ_lower σ hK2 hq hK hσq hσ3 hk3 c)
  exact DFunLike.congr_fun h M

include hσ3 hσq hK hK2 in
theorem triOdd_jClassSplit_of_model (hK3 : ringChar K ≠ 3) (hq4 : 4 ≤ q)
    (x : twistedGroup σ.toRingHom) (hxJ : x ∈ FixedSub σ) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ j ∈ FixedSub σ,
      (∃ M : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ.toRingHom),
        j * x * j⁻¹ = slLong σ.toRingHom hσ3 M) ∨
      (∃ M : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ.toRingHom),
        j * x * j⁻¹ = slShort σ.toRingHom hσ3
          (Matrix.SpecialLinearGroup.map (fixedField σ.toRingHom).subtype M)) := by
  have hq2 : 2 ≤ q := by omega
  have hF : Nat.card (fixSubfield σ) = q :=
    CFSG.GH74.GLS.Stage4.Hex.card_fixedField_of_cube σ.toRingHom hq2 hK hσq
  have hk4 : 4 ≤ Nat.card (fixSubfield σ) := hF ▸ hq4
  have hk3 : (3 : ℕ∞) ≤ ENat.card (fixSubfield σ) := by
    rw [ENat.card_eq_coe_natCard]
    exact_mod_cast (by omega : 3 ≤ Nat.card (fixSubfield σ))
  have h3F : ringChar (fixSubfield σ) ≠ 3 := by
    haveI : CharP (fixSubfield σ) (ringChar K) :=
      (RingHom.charP_iff_charP (fixSubfield σ).subtype (ringChar K)).2 (ringChar.charP K)
    rw [ringChar.eq (fixSubfield σ) (ringChar K)]
    exact hK3
  set Φ := triOddJDict σ hK2 hq2 hK hσq hσ3 hk3 with hΦ
  set x' : ↥(FixedSub σ) := ⟨x, hxJ⟩ with hx'
  have hx'3 : x' ^ 3 = 1 := Subtype.ext hx3
  have hx'1 : x' ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  set y := Φ x' with hy
  have hy3 : y ^ 3 = 1 := by rw [hy, ← map_pow, hx'3, map_one]
  have hy1 : y ≠ 1 := fun h => hx'1 (Φ.injective (h.trans (map_one Φ).symm))
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof.g2ThreeConjSL2_holds
    (fixSubfield σ) h3F hk4 y hy3 hy1
  rcases hg with hS | hL
  · obtain ⟨M, hM⟩ := short_conj_mem (fixSubfield σ) _ hS
    refine ⟨((Φ.symm ((g2WeylRep (fixSubfield σ))⁻¹ * g) : ↥(FixedSub σ)) : twistedGroup σ.toRingHom),
      (Φ.symm _).2, Or.inr ⟨M, ?_⟩⟩
    have key : Φ (Φ.symm ((g2WeylRep (fixSubfield σ))⁻¹ * g) * x' *
        (Φ.symm ((g2WeylRep (fixSubfield σ))⁻¹ * g))⁻¹) = Φ (triOddSlShortJ σ hσ3 M) := by
      rw [triOddJDict_slShortJ σ hK2 hq2 hK hσq hσ3 hk3 M, ← hM, map_mul, map_mul, map_inv,
        MulEquiv.apply_symm_apply, MulAut.conj_apply]
      simp only [mul_inv_rev, inv_inv, mul_assoc]
      rfl
    have key' := congrArg Subtype.val (Φ.injective key)
    exact key'
  · obtain ⟨M, hM⟩ := long_conj_mem (fixSubfield σ) _ hL
    refine ⟨((Φ.symm g : ↥(FixedSub σ)) : twistedGroup σ.toRingHom), (Φ.symm g).2,
      Or.inl ⟨M, ?_⟩⟩
    have key : Φ (Φ.symm g * x' * (Φ.symm g)⁻¹) = Φ (triOddSlLongJ σ hσ3 M) := by
      rw [triOddJDict_slLongJ σ hK2 hq2 hK hσq hσ3 hk3 M, ← hM, map_mul, map_mul, map_inv,
        MulEquiv.apply_symm_apply]
    have key' := congrArg Subtype.val (Φ.injective key)
    exact key'

end Gen

theorem triOdd_jClassSplitAll : TriOddJClassSplitAll := by
  intro K _ _ σ hσ3 q hK3 hq4 hK hσq
  unfold TriOddJClassSplit
  intro hK2 _ _ x hxJ hx3 hx1
  exact triOdd_jClassSplit_of_model σ hK2 hK hσq hσ3 hK3 hq4 x hxJ hx3 hx1

theorem triOdd_fixedSubgroup_sup_tau {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (x₀ : C0 σ) (hx3 : x₀ ^ 3 = 1) (hx1 : x₀ ≠ 1)
    (hτx : tauAut σ x₀ = x₀) :
    fixedSubgroup (MulAut.conj x₀) ⊔ fixedSubgroup (tauAut σ) = ⊤ :=
  triOdd_fixedSubgroup_sup_tau_of_split triOdd_jClassSplitAll hℓ hℓ2 hℓ3 hf hK σ hσ x₀ hx3 hx1 hτx

theorem triOddJPlanes : TriOddJPlanes := triOddJPlanes_of_split triOdd_jClassSplitAll

end Dict

end CFSG.LieType.SeitzGeneration.ExcWideThree
