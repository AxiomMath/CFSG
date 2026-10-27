module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.Setup
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagLift
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidSplit

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley

set_option linter.unusedSectionVars false


theorem balance_of_frame {K : Type} [Field K] [Finite K] (h3 : ¬ 3 ∣ Nat.card K)
    (hK4 : 4 ≤ Nat.card K) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {w' : WeylGroup Tag.E6}
    {g0 : ModGL Tag.E6 (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w')
    (a b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ) {w : WeylGroup Tag.E6}
    (ha3 : ∀ i, a i ^ 3 = 1) (hw : w ∈ rootCharStabilizer a)
    (hsh : rootChar a (e6Shift w) ≠ 1)
    (hT : rootDiagUnit Tag.E6 a ∈ twistedTorusOf
      (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w') (Units.map (entrywiseHom Fr)))
    {u : ModGL Tag.E6 (AlgebraicClosure K)}
    (hu : u ∈ rootSpan Tag.E6 (AlgebraicClosure K) (rootCharKernel a))
    (g₁ g₂ : ↥(e6InndiagGL K))
    (hg₁ : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (g₁ : ModGL Tag.E6 K) * g0 =
      rootDiagUnit Tag.E6 a)
    (hg₂ : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (g₂ : ModGL Tag.E6 K) * g0 =
      u⁻¹ * (rootDiagUnit Tag.E6 b *
        canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w) * u)
    (D : Subgroup (MulAut (adjointGroup Tag.E6 K)))
    (hD₁ : e6InndiagConj K g₁ ∈ D) (hD₂ : e6InndiagConj K g₂ ∈ D)
    (H : Subgroup (MulAut (adjointGroup Tag.E6 K))) (hH : innerAut (adjointGroup Tag.E6 K) ≤ H) :
    localDeltaIn 3 H D = ⊥ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  set L := AlgebraicClosure K with hL
  set ι₀ : K →+* L := algebraMap K L with hι₀
  let DL : LangDatum Tag.E6 L := LangDatum.ofFrobenius Fr (Nat.card K) hFr w' hg0C hg0
  have hd : LangDescent DL 7 ((baseChangeGL ι₀).comp (adjointGroup Tag.E6 K).subtype) :=
    langDescent_ofFrobenius (Or.inr (Or.inl rfl)) w' K hFr hg0C hg0
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved Tag.E6 L DL
  have hK0 : ((Nat.card K : ℕ) : L) = 0 := by
    rw [← map_natCast ι₀, Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero K, map_zero]
  have hqpow : IsPrimePow DL.q ∧ ((DL.q : ℕ) : L) = 0 :=
    ⟨by
      rw [show DL.q = Fintype.card K from Nat.card_eq_fintype_card]
      exact FiniteField.isPrimePow_card K, hK0⟩
  let S : LangSetup Tag.E6 L 3 :=
    DL.toSetup 3 ρ hρ Nat.prime_three (Or.inr hK4) hqpow h3 hd.finite_model
  have hSq : S.D.q = Nat.card K := rfl
  have hι : Function.Injective ((baseChangeGL ι₀).comp (adjointGroup Tag.E6 K).subtype) :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  set φ : adjointGroup Tag.E6 K ≃* S.Γ := hd.mulEquiv' hι with hφdef
  have hφ : ∀ h : adjointGroup Tag.E6 K,
      ((φ h : S.Γ) : ModGL Tag.E6 L) = g0⁻¹ * baseChangeGL ι₀ (h : ModGL Tag.E6 K) * g0 :=
    fun h => hd.coe_mulEquiv' hι h
  have hdesc : S.Descends := ⟨K, inferInstance, inferInstance, inferInstance, φ, rfl, hφ⟩
  set θ : ↥(e6InndiagGL K) →* ModGL Tag.E6 L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((baseChangeGL ι₀).comp (e6InndiagGL K).subtype) with hθdef
  have hθ : ∀ x : ↥(e6InndiagGL K), θ x = g0⁻¹ * baseChangeGL ι₀ (x : ModGL Tag.E6 K) * g0 :=
    fun x => by
      change (MulAut.conj g0⁻¹) (baseChangeGL ι₀ (x : ModGL Tag.E6 K)) = _
      rw [MulAut.conj_apply, inv_inv]
  have hθ₁ : θ g₁ = rootDiagUnit Tag.E6 a := by rw [hθ]; exact hg₁
  have hθ₂ : θ g₂ = u⁻¹ * (rootDiagUnit Tag.E6 b *
      canonicalRep (coxeterSystem Tag.E6) L w) * u := by rw [hθ]; exact hg₂
  have hθ' : ∀ (x : ↥(e6InndiagGL K)) (y : S.Γ),
      ((MulAut.congr φ (e6InndiagConj K x) y : S.Γ) : ModGL Tag.E6 L) = θ x * y * (θ x)⁻¹ := by
    intro x y
    obtain ⟨h, rfl⟩ := φ.surjective y
    change ((φ (e6InndiagConj K x (φ.symm (φ h))) : S.Γ) : ModGL Tag.E6 L) = _
    rw [MulEquiv.symm_apply_apply, hφ, hφ, e6InndiagConj_apply, map_mul, map_mul, map_inv, hθ]
    group
  exact balance_of_setup S (by rw [hSq]; exact hK4) (normalFormAt_of_descends S hdesc)
    (fun v hv h => eq_one_of_centralizes_Γ S hdesc (by rw [hSq]; exact hK4) hv h) φ
    (mulAut_conj_injective_adjointGroup (τ := Tag.E6) (K := K)) (e6InndiagConj K)
    (e6InndiagConj_injective K hK4) θ hθ' a b ha3 hw hsh hT hu g₁ g₂ hθ₁ hθ₂ D hD₁ hD₂ H hH

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis
