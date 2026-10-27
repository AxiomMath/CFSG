module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodLang
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.ExcFiveToralAux.GoodRootOdd
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodWiring
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyClass

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
  CFSG.RankThree.Lattice


section SylowTorus


theorem perfectCentralizerPlanes_of_sylow_le_torus {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
    (hsyl : ∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ)
    (hbig : ∀ D₁ : Subgroup (ModGL τ L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      (bigComponentSet S D₁).Nonempty) :
    PerfectCentralizerPlanes p S.Γ :=
  perfectCentralizerPlanes_of_langSetup S
    (fun F hF hFp _ => S.exists_conj_le hsyl hF hFp) hbig

end SylowTorus

theorem bigComponentSet_nonempty_of_goodRootsGenerate {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p) (hgen : GoodRootsGenerate S)
    {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E) (hD₁c : Nat.card D₁ = p ^ 2) :
    (bigComponentSet S D₁).Nonempty := by
  obtain ⟨β, hβ⟩ := (hgen _ (isRoot_single τ ⟨0, by cases τ <;> decide⟩)).nonempty
  obtain ⟨Y, hY, -, -⟩ := goodRoot_subset_bigComponentSet S hD₁E hD₁c hβ
  exact ⟨1, hY Y.one_mem⟩

section SylowTorusAlg


theorem perfectCentralizerPlanes_cat_of_langTorusAtAlgM {k : LieFamily}
    (hk : IsExceptionalFam k) {R : ℕ → ℕ → Prop} {M : List (List ℤ)} (ha : LangTorusAtAlgM k R M)
    (hbig : ∀ (L : Type) [Field L] [IsAlgClosed L] (p : ℕ) (S : LangSetup (excTag k) L p)
      (q : ℕ), R p q → S.D.q = q → S.IsAlgebraic → RhoIs S M →
      ∀ D₁ : Subgroup (ModGL (excTag k) L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
        (bigComponentSet S D₁).Nonempty)
    (q : TauCeti.PrimePower)
    (hv : (HardMathSupport.Timmesfeld.LocalTwo.excIndex k q).Valid) {p : ℕ} (hp : p.Prime)
    (hR : R p q.card) (hpq : p ≠ q.p) :
    PerfectCentralizerPlanes p (CatT ⟨HardMathSupport.Timmesfeld.LocalTwo.excIndex k q, hv⟩) := by
  obtain ⟨L, hF, hA, S, hSq, hAlg, hρ, hsyl, ⟨ε⟩⟩ := ha hk q hv p hp hR hpq
  exact PerfectCentralizerPlanes.of_mulEquiv ε.symm
    (perfectCentralizerPlanes_of_sylow_le_torus S hsyl
      (fun D₁ hD₁E hD₁c => hbig L p S q.card hR hSq hAlg hρ D₁ hD₁E hD₁c))

theorem perfectCentralizerPlanes_cat_of_langTorusAtAlgClass {k : LieFamily}
    (hk : IsExceptionalFam k) {R : ℕ → ℕ → Prop}
    {C : ∀ (L : Type) [Field L] [IsAlgClosed L] (p : ℕ), LangSetup (excTag k) L p → Prop}
    (ha : LangTorusAtAlgClass k R C)
    (hbig : ∀ (L : Type) [Field L] [IsAlgClosed L] (p : ℕ) (S : LangSetup (excTag k) L p)
      (q : ℕ), R p q → S.D.q = q → S.IsAlgebraic → C L p S →
      ∀ D₁ : Subgroup (ModGL (excTag k) L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
        (bigComponentSet S D₁).Nonempty)
    (q : TauCeti.PrimePower)
    (hv : (HardMathSupport.Timmesfeld.LocalTwo.excIndex k q).Valid) {p : ℕ} (hp : p.Prime)
    (hR : R p q.card) (hpq : p ≠ q.p) :
    PerfectCentralizerPlanes p (CatT ⟨HardMathSupport.Timmesfeld.LocalTwo.excIndex k q, hv⟩) := by
  obtain ⟨L, hF, hA, S, hSq, hAlg, hC, hsyl, ⟨ε⟩⟩ := ha hk q hv p hp hR hpq
  exact PerfectCentralizerPlanes.of_mulEquiv ε.symm
    (perfectCentralizerPlanes_of_sylow_le_torus S hsyl
      (fun D₁ hD₁E hD₁c => hbig L p S q.card hR hSq hAlg hC D₁ hD₁E hD₁c))

end SylowTorusAlg

theorem bigComponentSet_nonempty_of_classCheck {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p) (hτ : SimplyLacedTag τ)
    {C M : List (List ℤ)} (hC : toMat τ.rank C = τ.cartan) (hρ : RhoIs S M)
    (hq3 : 3 ≤ S.D.q) (hp7 : 7 ≤ p) {e : ℕ}
    (he : orderOf ((S.D.q : ℕ) : ZMod p) = e) {cert : List (ℕ × ℕ × ℕ)}
    (h : classCheck τ.rank C M τ.artifactRoots e cert = true)
    {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E) (hD₁c : Nat.card D₁ = p ^ 2) :
    (bigComponentSet S D₁).Nonempty :=
  bigComponentSet_nonempty_of_goodRootsGenerate S
    (goodRootsGenerate_of_classCheck S hτ hC hρ hq3 hp7 he h) hD₁E hD₁c

theorem bigComponentSet_nonempty_of_classCheck_odd {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p) (hτ : SimplyLacedTag τ)
    {C M : List (List ℤ)} (hC : toMat τ.rank C = τ.cartan) (hρ : RhoIs S M)
    (hq3 : 3 ≤ S.D.q) (hp3 : 3 ≤ p) {e : ℕ}
    (he : orderOf ((S.D.q : ℕ) : ZMod p) = e) {cert : List (ℕ × ℕ × ℕ)}
    (h : classCheck τ.rank C M τ.artifactRoots e cert = true)
    {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E) (hD₁c : Nat.card D₁ = p ^ 2) :
    (bigComponentSet S D₁).Nonempty :=
  bigComponentSet_nonempty_of_goodRootsGenerate S
    (goodRootsGenerate_of_classCheck_odd S hτ hC hρ hq3 hp3 he h) hD₁E hD₁c

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
