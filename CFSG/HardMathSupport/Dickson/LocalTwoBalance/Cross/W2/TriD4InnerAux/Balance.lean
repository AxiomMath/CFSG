module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6Three
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidAssembly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodGraph

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups

set_option linter.unusedSectionVars false


theorem triD4Three_setupRigid (hAK : AnyKindCommute) (hAF : AnyKindNoFrobenius)
    (hbig : ThreeBigComponents) {L : Type} [Field L] [IsAlgClosed L]
    (S : LangSetup TwistTag.D4.tag L 3)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.D4 L Fr)
    (hAlg : S.IsAlgebraic) (hq4 : 4 ≤ S.D.q) : SetupRigid S := by
  refine setupRigid_triD4 S hΦ hAlg (fun D₁ hD₁ hc => ?_) (fun D₁ hD₁ hc => ?_)
    (fun D₁ hD₁ hc => ?_)
  · exact noFrobeniusInner_of_anyKind hAF hbig S (by decide) hq4 (Or.inr (Or.inl rfl)) hD₁ hc
  · exact centralizerTrivial_of_anyKind hAK hbig S (by decide) hq4 hD₁ hc
  · intro c hc' a ha0 ha3 hcomm
    refine noTriCosetCentralizes_D4 c hc' a ha0 ha3 ?_
    exact commute_adjointGroup_of_anyKind hAK hbig S (by decide) hq4 hD₁ hc
      (fun x hx => hcomm x (Or.inl hx))

theorem triD4Three_planeBalance_at_torus (hcp : LangComponentPieces) (hAK : AnyKindCommute)
    (hAF : AnyKindNoFrobenius) (hbig : ThreeBigComponents) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hq3 : ¬ 3 ∣ ℓ ^ f) (hq2 : ℓ ^ f ≠ 2) (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {v : WeylGroup TwistTag.D4.tag} {g0 : ModGL TwistTag.D4.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.D4 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.D4.tag) (AlgebraicClosure K) v)
    (D₀ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hpow : ∀ x ∈ D₀, x ^ 3 = 1)
    (hcard : 3 < Nat.card D₀)
    (hmem : ∀ x ∈ D₀, baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL TwistTag.D4.tag K) ∈
        (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.D4.tag) (AlgebraicClosure K) v)
          (twistHom TwistTag.D4 (AlgebraicClosure K) Fr)).map (MulAut.conj g0).toMonoidHom)
    {H : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))}
    (hH : innerAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≤ H) :
    localDeltaIn 3 H (D₀.map (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) = ⊥ := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have hq2' : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
  have hq4 : 4 ≤ ℓ ^ f := four_le_of_not_three_dvd hq2' hq3 hq2
  let D : LangDatum TwistTag.D4.tag (AlgebraicClosure K) :=
    LangDatum.ofTwist TwistTag.D4 Fr (ℓ ^ f) hFr v hg0C hg0
  have hΦ : D.Φ = twistHom TwistTag.D4 (AlgebraicClosure K) Fr := rfl
  have hd : LangDescent D 3 (triEmb K σ (AlgebraicClosure K)) :=
    langDescent_triD4 hℓ hf hK σ hσ hFr D hΦ
  have hfin : Finite D.model := hd.finite_model
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved TwistTag.D4.tag (AlgebraicClosure K) D
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : AlgebraicClosure K) = 0 :=
    ⟨hℓ.isPrimePow.pow (by omega), (CharP.cast_eq_zero_iff (AlgebraicClosure K) ℓ _).2
      (dvd_pow_self ℓ (by omega))⟩
  have hpq : ¬ 3 ∣ D.q := hq3
  let S : LangSetup TwistTag.D4.tag (AlgebraicClosure K) 3 :=
    D.toSetup 3 ρ hρ Nat.prime_three (Or.inr hq4) hqpow hpq hfin
  have hSq : S.D.q = ℓ ^ f := rfl
  have hΦS : ∃ Fr' : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr' c = c ^ S.D.q) ∧
      S.D.Φ = twistHom TwistTag.D4 (AlgebraicClosure K) Fr' := ⟨Fr, hFr, rfl⟩
  have hAlg : S.IsAlgebraic := S.isAlgebraic_of_algebraic K 3 (by rw [hK, hSq])
  have hrig : SetupRigid S := triD4Three_setupRigid hAK hAF hbig S hΦS hAlg (by rw [hSq]; exact hq4)
  have hC : Function.Injective (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    mulAut_conj_injective_of_center_eq_bot (exceptional_fixed_center_trivial TwistTag.D4 K σ)
  have hι : Function.Injective (triEmb K σ (AlgebraicClosure K)) := triEmb_injective
  have hinj : Function.Injective (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ) :=
    CFSG.HardMathSupport.Timmesfeld.LocalTwo.conj_injective_of_mulEquiv (hd.mulEquiv' hι) hC
  have hbal : FrameBalanced 3 S.Γ S.E :=
    frameBalanced_of_langSetup S hrig hcp.subnormal hcp.inner hcp.suN hcp.twoD hcp.exc hinj
  refine localDeltaIn_eq_bot_of_frameBalanced_mulEquiv hbal (hd.mulEquiv' hι) D₀ hpow hcard
    (fun x hx => ?_) hH
  have hxT : ((hd.mulEquiv' hι x : D.Γ) : ModGL TwistTag.D4.tag (AlgebraicClosure K)) ∈ D.torus := by
    obtain ⟨y, hy, hyx⟩ := hmem x hx
    rw [hd.coe_mulEquiv' hι x]
    have h1 : D.g0⁻¹ * (triEmb K σ (AlgebraicClosure K) x) * D.g0 = y := by
      have h2 : g0 * y * g0⁻¹ = triEmb K σ (AlgebraicClosure K) x := hyx
      rw [← h2]
      change g0⁻¹ * (g0 * y * g0⁻¹) * g0 = y
      group
    rw [h1]
    exact hy
  have hxp : ((hd.mulEquiv' hι x : D.Γ) : ModGL TwistTag.D4.tag (AlgebraicClosure K)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hpow x hx, map_one, Subgroup.coe_one]
  exact (LangDatum.mem_torsion D).2 ⟨⟨hxT, (hd.mulEquiv' hι x).2⟩, hxp⟩

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
