module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6FiveAux.Plane
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityTw

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.TauCetiBridge CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE

set_option linter.unusedSectionVars false

section Rigid


theorem twistedE6Five_setupRigid (hAK : AnyKindCommute) (hAF : AnyKindNoFrobenius) {ℓ f : ℕ}
    (hq5 : ℓ ^ f % 5 = 1 ∨ ℓ ^ f % 5 = 4) (hℓ : ℓ.Prime) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {v : WeylGroup TwistTag.E6.tag}
    {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    (S : LangSetup TwistTag.E6.tag (AlgebraicClosure K) 5)
    (hSD : S.D = LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr v hg0C hg0) : SetupRigid S := by
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have hq : S.D.q = ℓ ^ f := by rw [hSD]; rfl
  have hq5' : S.D.q % 5 = 1 ∨ S.D.q % 5 = 4 := by rw [hq]; exact hq5
  have hq4 : 4 ≤ S.D.q := by
    have := S.hqpow.1.two_le
    omega
  have hΦ : ∃ Fr' : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr' c = c ^ S.D.q) ∧
      S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr' :=
    ⟨Fr, fun c => by rw [hq]; exact hFr c, by rw [hSD]; rfl⟩
  have hAlg : S.IsAlgebraic := S.isAlgebraic_of_algebraic K 2 (by rw [hK, hq])
  have hPS : BigAnyPBig S := bigAnyPBig_five S hq5'
  refine setupRigid_twistedE6 S hΦ hAlg (fun D₁ hD₁ hc => ?_) (fun D₁ hD₁ hc => ?_)
    (fun D₁ hD₁ hc => ?_)
  · exact hAF _ _ 5 S (by decide) (Or.inr (Or.inr (Or.inl rfl))) D₁ hD₁
      (hasBigAnyComponent_of_pbig S hq4 hPS hD₁ hc)
  · exact centralizerTrivial_of_bigAnyGenerate hAK S (by decide) (by omega) hD₁
      (bigAnyComponentsGenerate_of_pbig S (Or.inr (Or.inl rfl)) hq4 hPS hD₁ hc)
  · exact cosetCentralizerEmpty_of_bigAnyGenerate (K := K) hAK S (by omega) hD₁
      (bigAnyComponentsGenerate_of_pbig S (Or.inr (Or.inl rfl)) hq4 hPS hD₁ hc)

theorem twistedE6Five_langTorusPlaneBalance (hsub : LangSubnormal)
    (hin : LangComponentsQuasisimple .inner) (hsu : LangComponentsQuasisimple .suN)
    (htw : LangComponentsQuasisimple .twoD) (hex : LangComponentsQuasisimple .exc)
    (hAK : AnyKindCommute) (hAF : AnyKindNoFrobenius) (v : WeylGroup TwistTag.E6.tag) :
    TwistedE6LangTorusPlaneBalance v 5 fun q => 5 ∣ q + 1 :=
  twistedE6LangTorusPlaneBalance_of_setupRigidAt v Nat.prime_five
    (fun q hq2 hQ => ⟨by omega, Or.inl le_rfl⟩)
    (fun ℓ f hℓ hf hQq K _ hK σ hσ Fr hFr g0 hg0C hg0 S hSD => by
      have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
      have h2 : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
      exact twistedE6Five_setupRigid hAK hAF (by omega) hℓ K hK hFr hg0C hg0 S hSD)
    hsub hin hsu htw hex

end Rigid

section Toral


theorem twistedE6_toral_five {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (h5 : ¬ 5 ∣ ℓ ^ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (A : Subgroup (twistedE6RootGroup K σ))
    (hAp : ∀ x ∈ A, x ^ 5 = 1) (hAc : Nat.card A = 5 ^ 2) :
    ∃ (v : WeylGroup TwistTag.E6.tag) (Fr : AlgebraicClosure K →+* AlgebraicClosure K),
      (∀ c, Fr c = c ^ (ℓ ^ f)) ∧ ∃ g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K),
        twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
          g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v ∧
        ∀ x ∈ A, baseChangeGL (algebraMap K (AlgebraicClosure K))
            (x : ModGL TwistTag.E6.tag K) ∈
          (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
            (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).map (MulAut.conj g0).toMonoidHom := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have hpK : ¬ 5 ∣ Nat.card K := by
    rw [hK]
    intro h
    exact h5 (Nat.prime_five.dvd_of_dvd_pow h)
  set ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K) with hι
  set Fr : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius _ ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFι : ι.comp σ.toRingHom = Fr.comp ι := RingHom.ext fun c => by
    simp only [RingHom.comp_apply, hFr, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσ, map_pow]
  set φ : twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    (baseChangeGL ι).comp (twistedE6RootGroup K σ).subtype with hφ
  have hφinj : Function.Injective φ :=
    (baseChangeGL_injective ι).comp (Subgroup.subtype_injective _)
  set AL : Subgroup (ModGL TwistTag.E6.tag (AlgebraicClosure K)) := A.map φ with hAL
  have hxΓ : ∀ x : twistedE6RootGroup K σ, (x : ModGL TwistTag.E6.tag K) ∈
      twistedFixedGroup TwistTag.E6 K σ.toRingHom :=
    fun x => graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom x.2
  have hAL_le : AL ≤ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    rintro _ ⟨x, -, rfl⟩
    exact baseChangeGL_mem_adjointGroup ι ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (hxΓ x)).1
  have hALp : ∀ y ∈ AL, y ^ 5 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hAp x hx, map_one]
  have hALcard : Nat.card AL = 5 ^ 2 := by
    rw [hAL, ← Nat.card_congr (Subgroup.equivMapOfInjective A φ hφinj).toEquiv]
    exact hAc
  have hALcomm : ∀ x ∈ AL, ∀ y ∈ AL, x * y = y * x := by
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    intro x hx y hy
    have hc := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 5) (G := AL) hALcard).is_comm
    exact congrArg Subtype.val (hc.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hFix : ∀ y ∈ AL, twistHom TwistTag.E6 (AlgebraicClosure K) Fr y = y := by
    rintro _ ⟨x, -, rfl⟩
    change twistHom TwistTag.E6 (AlgebraicClosure K) Fr
        (baseChangeGL ι (x : ModGL TwistTag.E6.tag K)) = baseChangeGL ι (x : ModGL TwistTag.E6.tag K)
    rw [twistHom_baseChangeGL ι hFι, ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (hxΓ x)).2]
  obtain ⟨g, hgG, hg⟩ := planesToralBar_E6_five K hpK AL hAL_le hALcomm hALp hALcard
  obtain ⟨v, g0, hg0C, hg0, hmem⟩ := exists_lang_torus_of_conj_torus_twisted ℓ TwistTag.E6 f hf
    (A := AL) hFix hgG hg
  exact ⟨v, Fr, hFr, g0, hg0C, hg0, fun x hx => hmem _ ⟨x, hx, rfl⟩⟩

end Toral

section Inner


theorem innerPlaneBalance_twistedE6_five_of_toral
    (hT1 : ∀ v : WeylGroup TwistTag.E6.tag,
      TwistedE6LangTorusPlaneBalance v 5 fun q => 5 ∣ q + 1) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (h5 : 5 ∣ ℓ ^ f + 1) :
    InnerPlaneBalance 5 (twistedE6RootGroup K σ) := by
  have hnd : ¬ 5 ∣ ℓ ^ f := by omega
  intro D hDin hD hcard H hH
  have hinj : Function.Injective
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) :=
    CFSG.LieType.Chevalley.mulAut_conj_injective_of_center_eq_bot
      (CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot σ.surjective)
  set D₀ := D.comap (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ))
    with hD₀
  have hDD : D₀.map MulAut.conj = D := Subgroup.map_comap_eq_self hDin
  have hD₀card : Nat.card D₀ = 5 ^ 2 := by
    rw [← hcard, ← hDD, Subgroup.card_map_of_injective hinj]
  have hpow₀ : ∀ x ∈ D₀, x ^ 5 = 1 := fun x hx => by
    have hx' : (MulAut.conj x) ^ 5 = 1 := hD.2 _ hx
    exact hinj (by rw [map_pow, hx', map_one])
  obtain ⟨v, Fr, hFr, g0, hg0C, hg0, htor⟩ :=
    twistedE6_toral_five hℓ hf hnd K hK σ hσ D₀ hpow₀ hD₀card
  rw [← hDD]
  exact hT1 v ℓ f hℓ hf h5 K hK σ hσ Fr hFr g0 hg0C hg0 D₀ hpow₀
    (by rw [hD₀card]; norm_num) htor H hH


section Cat


theorem innerPlaneBalance_catTwistedE6_five_neg (q : TauCeti.PrimePower)
    (hv : (excIndex .twistedE6 q).Valid) (h : 5 ∣ q.card + 1) :
    InnerPlaneBalance 5 (CatT ⟨excIndex .twistedE6 q, hv⟩) := by
  obtain ⟨hsub, hin, hsu, htw, hex⟩ := t1_pieces
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  rw [TauCeti.PrimePower.card_def] at h
  exact InnerPlaneBalance.of_mulEquiv e (innerPlaneBalance_twistedE6_five_of_toral
    (twistedE6Five_langTorusPlaneBalance hsub hin hsu htw hex
      (anyKindCommute_of_T anyKindCommuteT_holds) anyKindNoFrobenius_of_outer)
    q.prime_p q.exponent_pos K hK σ hσ h)

end Cat

end Inner

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
