module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwAnyKind
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidSplit
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidE6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidTwE6
public import CFSG.LieType.Chevalley.E6GraphInnerCosetExhaustion

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE

section Finite


theorem exists_intermediateField_mem_map_adjointGroup {τ : Tag} {K L : Type} [Field K] [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] {g : ModGL τ L} (hg : g ∈ adjointGroup τ L) :
    ∃ E : IntermediateField K L, FiniteDimensional K E ∧
      g ∈ (adjointGroup τ E).map (baseChangeGL (algebraMap E L)) := by
  classical
  have hmono : ∀ {E₁ E : IntermediateField K L}, E₁ ≤ E →
      (adjointGroup τ E₁).map (baseChangeGL (algebraMap E₁ L)) ≤
        (adjointGroup τ E).map (baseChangeGL (algebraMap E L)) := by
    intro E₁ E hle
    rintro _ ⟨h, hh, rfl⟩
    refine ⟨baseChangeGL (IntermediateField.inclusion hle).toRingHom h,
      CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ hh, ?_⟩
    rw [baseChangeGL_baseChangeGL]
    rfl
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, c, hx | hx⟩ := hx
    · have hint : IsIntegral K c := (Algebra.IsAlgebraic.isAlgebraic c).isIntegral
      refine ⟨IntermediateField.adjoin K {c}, IntermediateField.adjoin.finiteDimensional hint,
        xUnit τ _ i ⟨c, IntermediateField.mem_adjoin_simple_self K c⟩,
        xUnit_mem_adjointGroup i _, ?_⟩
      rw [baseChangeGL_xUnit]
      exact Units.ext ((coe_xUnit i c).trans hx.symm)
    · have hint : IsIntegral K c := (Algebra.IsAlgebraic.isAlgebraic c).isIntegral
      refine ⟨IntermediateField.adjoin K {c}, IntermediateField.adjoin.finiteDimensional hint,
        yUnit τ _ i ⟨c, IntermediateField.mem_adjoin_simple_self K c⟩,
        yUnit_mem_adjointGroup i _, ?_⟩
      rw [baseChangeGL_yUnit]
      exact Units.ext ((coe_yUnit i c).trans hx.symm)
  | one => exact ⟨⊥, inferInstance, 1, one_mem _, map_one _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨E₁, hE₁, hx⟩ := hx
    obtain ⟨E₂, hE₂, hy⟩ := hy
    exact ⟨E₁ ⊔ E₂, inferInstance,
      mul_mem (hmono le_sup_left hx) (hmono le_sup_right hy)⟩
  | inv x _ hx =>
    obtain ⟨E, hE, hx⟩ := hx
    exact ⟨E, hE, inv_mem hx⟩

end Finite

section Graph


theorem not_forall_commute_mul_diagramMap_E6 {K L : Type} [Field K] [Finite K] [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] {w : ModGL TwistTag.E6.tag L}
    (hw : w ∈ adjointGroup TwistTag.E6.tag L) :
    ¬ ∀ h ∈ adjointGroup TwistTag.E6.tag L, Commute (w * diagramMap TwistTag.E6 L) h := by
  intro hcomm
  obtain ⟨E, hE, wE, hwE, rfl⟩ := exists_intermediateField_mem_map_adjointGroup (K := K) hw
  have : Finite E := Module.finite_of_finite K
  set ι : E →+* L := algebraMap E L with hι
  refine E6GraphInnerCoset.ordinary_not_inner E (g := wE⁻¹) (inv_mem hwE) fun h hh => ?_
  have h1 := (hcomm (baseChangeGL ι h)
    (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup ι hh)).eq
  have hP : baseChangeGL ι (diagramMap TwistTag.E6 E) = diagramMap TwistTag.E6 L :=
    baseChangeGL_diagramMap ι TwistTag.E6
  rw [← hP] at h1
  have h2 : baseChangeGL ι (diagramMap TwistTag.E6 E * h * (diagramMap TwistTag.E6 E)⁻¹) =
      baseChangeGL ι (wE⁻¹ * h * wE⁻¹⁻¹) := by
    simp only [map_mul, map_inv, inv_inv]
    calc baseChangeGL ι (diagramMap TwistTag.E6 E) * baseChangeGL ι h *
          (baseChangeGL ι (diagramMap TwistTag.E6 E))⁻¹ =
        (baseChangeGL ι wE)⁻¹ * (baseChangeGL ι wE * baseChangeGL ι (diagramMap TwistTag.E6 E) *
          baseChangeGL ι h) * (baseChangeGL ι (diagramMap TwistTag.E6 E))⁻¹ := by group
      _ = (baseChangeGL ι wE)⁻¹ * (baseChangeGL ι h * (baseChangeGL ι wE *
          baseChangeGL ι (diagramMap TwistTag.E6 E))) *
          (baseChangeGL ι (diagramMap TwistTag.E6 E))⁻¹ := by rw [h1]
      _ = (baseChangeGL ι wE)⁻¹ * baseChangeGL ι h * baseChangeGL ι wE := by group
  exact baseChangeGL_injective ι h2

theorem graphCentralizerEmpty_of_anyKind (hAK : AnyKindCommute) (hbig : ThreeBigComponents)
    {K L : Type} [Field K] [Finite K] [Field L] [IsAlgClosed L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (S : LangSetup .E6 L 3) (hq4 : 4 ≤ S.D.q)
    {D₁ : Subgroup (ModGL .E6 L)} (hD₁E : D₁ ≤ S.E) (hD₁c : Nat.card D₁ = 3 ^ 2) :
    GraphCentralizerEmpty S D₁ := by
  intro w hw hcomm
  exact not_forall_commute_mul_diagramMap_E6 (K := K) hw
    (commute_adjointGroup_of_anyKind hAK hbig S (by decide) hq4 hD₁E hD₁c
      fun x hx => hcomm x (Or.inl hx))

theorem cosetCentralizerEmpty_of_anyKind (hAK : AnyKindCommute) (hbig : ThreeBigComponents)
    {K L : Type} [Field K] [Finite K] [Field L] [IsAlgClosed L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (S : LangSetup TwistTag.E6.tag L 3) (hq4 : 4 ≤ S.D.q)
    {D₁ : Subgroup (ModGL TwistTag.E6.tag L)} (hD₁E : D₁ ≤ S.E) (hD₁c : Nat.card D₁ = 3 ^ 2) :
    CosetCentralizerEmpty S D₁ (diagramMap TwistTag.E6 L) := by
  intro w hw hcomm
  exact not_forall_commute_mul_diagramMap_E6 (K := K) hw
    (commute_adjointGroup_of_anyKind hAK hbig S (by decide) hq4 hD₁E hD₁c
      fun x hx => hcomm x (Or.inl hx))

end Graph

theorem four_le_of_not_three_dvd {q : ℕ} (hq2 : 2 ≤ q) (h3 : ¬ 3 ∣ q) (h2 : q ≠ 2) : 4 ≤ q := by
  by_contra h
  interval_cases q
  · exact h2 rfl
  · exact h3 (dvd_refl 3)

section Rigid


theorem e6Three_setupRigid (hAK : AnyKindCommute) (hAF : AnyKindNoFrobenius)
    (hbig : ThreeBigComponents) (K : Type) [Field K] [Finite K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {w : WeylGroup Tag.E6} {g0 : ModGL Tag.E6 (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w)
    (S : LangSetup Tag.E6 (AlgebraicClosure K) 3)
    (hSD : S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0)
    (hq3 : ¬ 3 ∣ Nat.card K) (hq2 : Nat.card K ≠ 2) : SetupRigid S := by
  have hq : S.D.q = Nat.card K := by rw [hSD]; rfl
  have hq4 : 4 ≤ S.D.q := hq ▸ four_le_of_not_three_dvd Finite.one_lt_card hq3 hq2
  have hd : S.Descends := by
    have hd7 : LangDescent S.D 7 ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup Tag.E6 K).subtype) := by
      rw [hSD]
      exact langDescent_ofFrobenius (Or.inr (Or.inl rfl)) w K hFr hg0C hg0
    have hι : Function.Injective ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup Tag.E6 K).subtype) :=
      (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
    exact ⟨K, inferInstance, inferInstance, inferInstance, hd7.mulEquiv' hι, hq.symm,
      fun x => hd7.coe_mulEquiv' hι x⟩
  refine setupRigid_of_descends_E6 S hd (fun D₁ hD₁ hc => ?_) (fun D₁ hD₁ hc => ?_)
    (fun D₁ hD₁ hc => ?_)
  · exact noFrobeniusInner_of_anyKind hAF hbig S (by decide) hq4 (Or.inr (Or.inr (Or.inl rfl)))
      hD₁ hc
  · exact centralizerTrivial_of_anyKind hAK hbig S (by decide) hq4 hD₁ hc
  · exact graphCentralizerEmpty_of_anyKind (K := K) hAK hbig S hq4 hD₁ hc

theorem e6Three_setupRigidAtFrobenius (hAK : AnyKindCommute) (hAF : AnyKindNoFrobenius)
    (hbig : ThreeBigComponents) (w : WeylGroup Tag.E6) :
    SetupRigidAtFrobenius Tag.E6 w 3 fun q => ¬ 3 ∣ q ∧ q ≠ 2 := by
  intro K _ _ Fr hFr g0 hg0C hg0 S hSD hQK
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  exact e6Three_setupRigid hAK hAF hbig K hFr hg0C hg0 S hSD hQK.1 hQK.2

theorem twistedE6Three_setupRigid (hAK : AnyKindCommute) (hAF : AnyKindNoFrobenius)
    (hbig : ThreeBigComponents) {ℓ f : ℕ} (hq3 : ¬ 3 ∣ ℓ ^ f) (hq2 : ℓ ^ f ≠ 2) (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {v : WeylGroup TwistTag.E6.tag} {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    (S : LangSetup TwistTag.E6.tag (AlgebraicClosure K) 3)
    (hSD : S.D = LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr v hg0C hg0) : SetupRigid S := by
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have hq : S.D.q = ℓ ^ f := by rw [hSD]; rfl
  have hq4 : 4 ≤ S.D.q := hq ▸ four_le_of_not_three_dvd
    (le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)) hq3 hq2
  have hΦ : ∃ Fr' : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr' c = c ^ S.D.q) ∧
      S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr' :=
    ⟨Fr, fun c => by rw [hq]; exact hFr c, by rw [hSD]; rfl⟩
  have hAlg : S.IsAlgebraic := S.isAlgebraic_of_algebraic K 2 (by rw [hK, hq])
  refine setupRigid_twistedE6 S hΦ hAlg (fun D₁ hD₁ hc => ?_) (fun D₁ hD₁ hc => ?_)
    (fun D₁ hD₁ hc => ?_)
  · exact noFrobeniusInner_of_anyKind hAF hbig S (by decide) hq4 (Or.inr (Or.inr (Or.inl rfl)))
      hD₁ hc
  · exact centralizerTrivial_of_anyKind hAK hbig S (by decide) hq4 hD₁ hc
  · exact cosetCentralizerEmpty_of_anyKind (K := K) hAK hbig S hq4 hD₁ hc

end Rigid

section Balance


theorem e6Three_langTorusPlaneBalance (hsub : LangSubnormal)
    (hin : LangComponentsQuasisimple .inner) (hsu : LangComponentsQuasisimple .suN)
    (htw : LangComponentsQuasisimple .twoD) (hex : LangComponentsQuasisimple .exc)
    (hAK : AnyKindCommute) (hAF : AnyKindNoFrobenius) (hbig : ThreeBigComponents)
    (w : WeylGroup Tag.E6) :
    LangTorusPlaneBalance Tag.E6 w 3 fun q => ¬ 3 ∣ q ∧ q ≠ 2 :=
  langTorusPlaneBalance_of_setupRigidAt (Or.inr (Or.inl rfl))
    (fun K _ _ => commutator_adjointGroup_E6_eq_top K) w Nat.prime_three
    (fun _ hq2 hQ => ⟨hQ.1, Or.inr (four_le_of_not_three_dvd hq2 hQ.1 hQ.2)⟩)
    (e6Three_setupRigidAtFrobenius hAK hAF hbig w) hsub hin hsu htw hex

theorem twistedE6Three_langTorusPlaneBalance (hsub : LangSubnormal)
    (hin : LangComponentsQuasisimple .inner) (hsu : LangComponentsQuasisimple .suN)
    (htw : LangComponentsQuasisimple .twoD) (hex : LangComponentsQuasisimple .exc)
    (hAK : AnyKindCommute) (hAF : AnyKindNoFrobenius) (hbig : ThreeBigComponents)
    (v : WeylGroup TwistTag.E6.tag) :
    TwistedE6LangTorusPlaneBalance v 3 fun q => ¬ 3 ∣ q ∧ q ≠ 2 :=
  twistedE6LangTorusPlaneBalance_of_setupRigidAt v Nat.prime_three
    (fun _ hq2 hQ => ⟨hQ.1, Or.inr (four_le_of_not_three_dvd hq2 hQ.1 hQ.2)⟩)
    (fun ℓ f hℓ hf hQq K _ hK _ _ Fr hFr g0 hg0C hg0 S hSD => by
      have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
      exact twistedE6Three_setupRigid hAK hAF hbig hQq.1 hQq.2 hℓ hf K hK hFr hg0C hg0 S hSD)
    hsub hin hsu htw hex

end Balance

end CFSG.HardMathSupport.Timmesfeld.CrossChar
