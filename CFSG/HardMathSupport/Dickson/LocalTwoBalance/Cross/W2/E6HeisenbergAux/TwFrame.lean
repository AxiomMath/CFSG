module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.TwFaithful
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.Setup
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.TwNormalForm
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley

set_option linter.unusedSectionVars false


theorem balance_of_frame_tw {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (h3 : ¬ 3 ∣ ℓ ^ f) (hq4 : 4 ≤ ℓ ^ f)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {w' : WeylGroup TwistTag.E6.tag} {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w')
    (a b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ) {w : WeylGroup Tag.E6}
    (ha3 : ∀ i, a i ^ 3 = 1) (hw : w ∈ rootCharStabilizer a)
    (hsh : rootChar a (e6Shift w) ≠ 1)
    (hT : rootDiagUnit Tag.E6 a ∈ twistedTorusOf
      (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w')
      (twistHom TwistTag.E6 (AlgebraicClosure K) Fr))
    {u : ModGL Tag.E6 (AlgebraicClosure K)}
    (hu : u ∈ rootSpan Tag.E6 (AlgebraicClosure K) (rootCharKernel a))
    (g₁ g₂ : ↥(twistedE6InndiagGL K σ))
    (hg₁ : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (g₁ : ModGL TwistTag.E6.tag K) * g0 = rootDiagUnit Tag.E6 a)
    (hg₂ : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (g₂ : ModGL TwistTag.E6.tag K) * g0 =
      u⁻¹ * (rootDiagUnit Tag.E6 b *
        canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w) * u)
    (D : Subgroup (MulAut (twistedE6RootGroup K σ)))
    (hD₁ : twistedE6InndiagConj K σ g₁ ∈ D) (hD₂ : twistedE6InndiagConj K σ g₂ ∈ D)
    (H : Subgroup (MulAut (twistedE6RootGroup K σ))) (hH : innerAut (twistedE6RootGroup K σ) ≤ H) :
    localDeltaIn 3 H D = ⊥ := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  set L := AlgebraicClosure K with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  set ι : K →+* L := algebraMap K L with hι
  let DL : LangDatum TwistTag.E6.tag L :=
    LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr w' hg0C hg0
  have hΦ : DL.Φ = twistHom TwistTag.E6 L Fr := rfl
  have hfin := finite_model_twistedE6 hℓ hf hK hσ hFr DL hΦ
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved TwistTag.E6.tag L DL
  have hqpow : IsPrimePow DL.q ∧ ((DL.q : ℕ) : L) = 0 := by
    refine ⟨hℓ.isPrimePow.pow (by omega), ?_⟩
    change ((ℓ ^ f : ℕ) : L) = 0
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  let S : LangSetup TwistTag.E6.tag L 3 :=
    DL.toSetup 3 ρ hρ Nat.prime_three (Or.inr hq4) hqpow h3 hfin
  have hSq : S.D.q = ℓ ^ f := rfl
  set φ : twistedE6RootGroup K σ ≃* S.Γ := twistedE6EquivΓ hℓ hf hK hσ hFr DL hΦ with hφdef
  have hφ : ∀ h : twistedE6RootGroup K σ, ((φ h : S.Γ) : ModGL TwistTag.E6.tag L) =
      g0⁻¹ * baseChangeGL ι (h : ModGL TwistTag.E6.tag K) * g0 :=
    fun h => coe_twistedE6EquivΓ hℓ hf hK hσ hFr DL hΦ h
  have hdesc : S.DescendsTwE6 := ⟨K, inferInstance, inferInstance, inferInstance, σ, φ, hK,
    fun c => by rw [hσ, map_pow, hSq], hφ⟩
  set θ : ↥(twistedE6InndiagGL K σ) →* ModGL TwistTag.E6.tag L :=
    (MulAut.conj g0⁻¹).toMonoidHom.comp ((baseChangeGL ι).comp (twistedE6InndiagGL K σ).subtype)
    with hθdef
  have hθ : ∀ x : ↥(twistedE6InndiagGL K σ),
      θ x = g0⁻¹ * baseChangeGL ι (x : ModGL TwistTag.E6.tag K) * g0 := fun x => by
    change (MulAut.conj g0⁻¹) (baseChangeGL ι (x : ModGL TwistTag.E6.tag K)) = _
    rw [MulAut.conj_apply, inv_inv]
  have hθ₁ : θ g₁ = rootDiagUnit Tag.E6 a := by rw [hθ]; exact hg₁
  have hθ₂ : θ g₂ = u⁻¹ * (rootDiagUnit Tag.E6 b *
      canonicalRep (coxeterSystem Tag.E6) L w) * u := by rw [hθ]; exact hg₂
  have hθ' : ∀ (x : ↥(twistedE6InndiagGL K σ)) (y : S.Γ),
      ((MulAut.congr φ (twistedE6InndiagConj K σ x) y : S.Γ) : ModGL TwistTag.E6.tag L) =
        θ x * y * (θ x)⁻¹ := by
    intro x y
    obtain ⟨h, rfl⟩ := φ.surjective y
    change ((φ (twistedE6InndiagConj K σ x (φ.symm (φ h))) : S.Γ) :
      ModGL TwistTag.E6.tag L) = _
    rw [MulEquiv.symm_apply_apply, hφ, hφ, twistedE6InndiagConj_apply, map_mul, map_mul, map_inv,
      hθ]
    group
  have hC : Function.Injective
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) :=
    CFSG.LieType.Chevalley.mulAut_conj_injective_of_center_eq_bot
      (CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot σ.surjective)
  have hfaith : ∀ v ∈ adjointGroup TwistTag.E6.tag L,
      (∀ y : S.Γ, Commute v (y : ModGL TwistTag.E6.tag L)) → v = 1 := by
    intro v hv hcomm
    have hc : g0 * v * g0⁻¹ ∈ adjointGroup TwistTag.E6.tag L :=
      mul_mem (mul_mem hg0C hv) (inv_mem hg0C)
    have h1 : g0 * v * g0⁻¹ = 1 := centralizer_twE6_trivial hℓ hf hK σ hσ h3 hq4 hc (fun x => by
      have hx := (hcomm (φ x)).eq
      rw [hφ x] at hx
      show g0 * v * g0⁻¹ * baseChangeGL ι (x : ModGL TwistTag.E6.tag K) =
        baseChangeGL ι (x : ModGL TwistTag.E6.tag K) * (g0 * v * g0⁻¹)
      calc g0 * v * g0⁻¹ * baseChangeGL ι (x : ModGL TwistTag.E6.tag K)
          = g0 * (v * (g0⁻¹ * baseChangeGL ι (x : ModGL TwistTag.E6.tag K) * g0)) * g0⁻¹ := by
            group
        _ = g0 * ((g0⁻¹ * baseChangeGL ι (x : ModGL TwistTag.E6.tag K) * g0) * v) * g0⁻¹ := by
            rw [hx]
        _ = baseChangeGL ι (x : ModGL TwistTag.E6.tag K) * (g0 * v * g0⁻¹) := by group)
    calc v = g0⁻¹ * (g0 * v * g0⁻¹) * g0 := by group
      _ = 1 := by rw [h1]; group
  exact balance_of_setup S (by rw [hSq]; exact hq4) (normalFormAt_of_descendsTw S hdesc)
    (fun v hv h => hfaith v hv h) φ hC (twistedE6InndiagConj K σ)
    (twistedE6InndiagConj_injective hℓ hf hK σ hσ) θ hθ' a b
    ha3 hw hsh hT hu g₁ g₂ hθ₁ hθ₂ D hD₁ hD₂ H hH

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis
