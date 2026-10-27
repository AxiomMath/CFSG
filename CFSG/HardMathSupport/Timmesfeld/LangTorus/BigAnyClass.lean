module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyHex
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidAssembly
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

set_option linter.unusedSectionVars false

section Class

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

@[expose] def LangSetup.IsWeylClass (S : LangSetup τ L p)
    (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) : Prop :=
  ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr) ∧
    ∃ w : WeylGroup τ, S.D.n = canonicalRep (coxeterSystem τ) L w ∧ (∀ u, w • u = M *ᵥ u) ∧
      S.D.model ≤ S.Γ

theorem LangSetup.bigAnyPBig_of_weylClass_hex (S : LangSetup τ L p) (hτ : SimplyLacedTag τ)
    (hp7 : 7 ≤ p) {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hM : M * M = M - 1)
    (h : S.IsWeylClass M) : BigAnyPBig S := by
  obtain ⟨Fr, hFr, hΦ, w, hn, hw, hMΓ⟩ := h
  refine bigAnyPBig_of_phi6 S hFr hΦ hn hτ (fun δ _ => ?_) hp7 hMΓ
  simp only [hw]
  rw [Matrix.mulVec_mulVec, hM, Matrix.sub_mulVec, Matrix.one_mulVec]

theorem setupRigid_E8_of_pbig
    (S : LangSetup .E8 L p) (hp7 : 7 ≤ p) (hAlg : S.IsAlgebraic)
    (hq4 : 4 ≤ S.D.q) (hP : BigAnyPBig S) (hI : CentralizerTrivialAny .E8)
    (hF : NoFrobeniusInnerAny .E8) : SetupRigid S :=
  setupRigid_E8 S (by omega) hAlg
    (fun D₁ hD₁ hc => hF L p S (by decide) (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hD₁
      (hasBigAnyComponent_of_pbig S hq4 hP hD₁ hc))
    (fun D₁ hD₁ hc => hI L p S (by decide) (by omega) hD₁
      (bigAnyComponentsGenerate_of_pbig S (Or.inr (Or.inr (Or.inr rfl))) hq4 hP hD₁ hc))

end Class

section Restricted

@[expose] def LangTorusAtAlgClass (k : LieFamily) (R : ℕ → ℕ → Prop)
    (C : ∀ (L : Type) [Field L] [IsAlgClosed L] (p : ℕ), LangSetup (excTag k) L p → Prop) : Prop :=
  IsExceptionalFam k → ∀ (q : TauCeti.PrimePower) (hv : (excIndex k q).Valid) (p : ℕ),
    p.Prime → R p q.card → p ≠ q.p →
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (S : LangSetup (excTag k) L p),
      S.D.q = q.card ∧ S.IsAlgebraic ∧ C L p S ∧
      (∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ) ∧
      Nonempty (CatT ⟨excIndex k q, hv⟩ ≃* S.Γ)

@[expose] def LangRigidityForAlgClass (k : LieFamily) (R : ℕ → ℕ → Prop)
    (C : ∀ (L : Type) [Field L] [IsAlgClosed L] (p : ℕ), LangSetup (excTag k) L p → Prop) :
    Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (excIndex k q).Valid) (p : ℕ) (L : Type) [Field L]
    [IsAlgClosed L] (S : LangSetup (excTag k) L p), R p q.card → S.D.q = q.card →
      S.IsAlgebraic → C L p S → Nonempty (CatT ⟨excIndex k q, hv⟩ ≃* S.Γ) → SetupRigid S

theorem innerPlaneBalanceAt_of_lang_rigid_alg_split_class {k : LieFamily} {e : ℕ}
    {C : ∀ (L : Type) [Field L] [IsAlgClosed L] (p : ℕ), LangSetup (excTag k) L p → Prop}
    (hk : IsExceptionalFam k)
    (ha : LangTorusAtAlgClass k (fun p c => 7 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = e) C)
    (hrig : LangRigidityForAlgClass k (fun p c => 7 ≤ p ∧ 4 ≤ c) C)
    (hsmall : InnerPlaneBalanceSmall k e) (hcp : LangComponentPieces)
    (hZ : ∀ (q : TauCeti.PrimePower) (hv : (excIndex k q).Valid),
      Subgroup.center (CatT ⟨excIndex k q, hv⟩) = ⊥) : InnerPlaneBalanceAt k e := by
  intro q hv p hp hp7 _ hpq he
  by_cases h4 : 4 ≤ q.card
  · obtain ⟨L, hF, hA, S, hSq, hAlg, hC, hsyl, ⟨ε⟩⟩ := ha hk q hv p hp ⟨hp7, he⟩ hpq
    have hinj := conj_injective_of_mulEquiv ε (conj_injective_of_center_bot (hZ q hv))
    exact InnerPlaneBalance.of_mulEquiv ε
      (innerPlaneBalance_of_langSetup_rigid S hsyl
        (hrig q hv p L S ⟨hp7, h4⟩ hSq hAlg hC ⟨ε⟩) hcp hinj)
  · exact hsmall q hv p hp hp7 hpq he (by omega)

end Restricted

end CFSG.HardMathSupport.Timmesfeld.LangTorus
