module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.GH74.GLS.Stage2.Signalizer (IsMaxParabolicP)

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev gammaIn (k p : ℕ) (R T : Subgroup G) : Subgroup G :=
  (CFSG.Open.rankThreeGamma k p (R.subgroupOf T)).map T.subtype

noncomputable abbrev gammaOver (k p : ℕ) (R T : Subgroup G) : Subgroup G :=
  ⨆ (F : Subgroup G) (_ : F ≤ R) (_ : k ≤ CFSG.Open.pRank p F),
    Subgroup.normalizer (F : Set G) ⊓ T

abbrev oPrimeModPrimeComplement (d : ℕ) (X : Subgroup G) : Type :=
  ↥(oPPrimeHull d (⊤ : Subgroup (modPrimeComplement d X)))

@[expose] def ThreeNine : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E D X₁ : Subgroup X) (p d : ℕ),
    p.Prime → p ≠ 2 →
    CFSG.IsQuasisimple ↥K →
    CFSG.pPrimeCore p ↥K = ⊥ →
    CFSG.SectionRank.IsKGroupCat ↥K →
    K.Normal →
    1 < CFSG.Open.pRank p (⊤ : Subgroup X) →
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3 →
    CFSG.Open.IsElemAbelian p E → Nat.card E = p ^ 2 →
    d.Prime → d ≠ 2 → d ≠ p →
    CFSG.ABGLocalTools.IsSylowOf d D ⊤ → D ≠ ⊥ →
    X₁ < K ⊔ D →
    gammaOver 1 p E (K ⊔ D) ≤ X₁ →
    gammaIn 1 d D (K ⊔ D) ≤ X₁ →
    (∀ Q : Subgroup X, IsPGroup p Q → E ≤ Q →
      Subgroup.normalizer (Q : Set X) ⊓ (K ⊔ D) ≤ X₁) →
    IsCyclic ↥D ∧ D ≤ K ∧
      ((p = 3 ∧ d = 13 ∧ CFSG.Blueprint.ReeTitsModel ↥K .Tits 2 1 ∧
          IsPSLType 3 (ZMod 3) (oPrimeModPrimeComplement d X₁)) ∨
        (p = 5 ∧ d = 7 ∧ CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .HS ∧
          CFSG.Open.StatedClassicalModel (oPrimeModPrimeComplement d X₁) .PSU 3 5 1) ∨
        (p = 5 ∧ d = 7 ∧ CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .Fi22 ∧
          CFSG.Open.StatedClassicalModel (oPrimeModPrimeComplement d X₁) .POmegaPlus 4 2 1) ∨
        (p = 5 ∧ d = 31 ∧ CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .Ly ∧
          CFSG.Blueprint.ChevalleyExceptionalModel (oPrimeModPrimeComplement d X₁) .G2 5 1) ∨
        (p = 7 ∧ d = 19 ∧ CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .ONan ∧
          IsPSLType 3 (ZMod 7) (oPrimeModPrimeComplement d X₁)) ∨
        (p = 7 ∧ d = 17 ∧ CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .Fi24Prime ∧
          CFSG.Blueprint.NativeSporadic.IsSporadic (oPrimeModPrimeComplement d X₁) .He) ∨
        (d ∣ p + 1 ∧ IsPSLType 3 (ZMod p) ↥K ∧
          IsPSLType 2 (ZMod p) (oPrimeModPrimeComplement d X₁)))

@[expose] def ThreeTen : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (I D P Y : Subgroup H) (p d : ℕ),
    p.Prime → p ≠ 2 →
    d.Prime → d ≠ 2 → d ≠ p →
    I = oPPrimeHull p (⊤ : Subgroup H) →
    CFSG.ABGLocalTools.IsSylowOf d D ⊤ → D ≠ ⊥ →
    CFSG.ABGLocalTools.IsSylowOf p P ⊤ →
    Y < I ⊔ D →
    gammaIn 1 d D (I ⊔ D) ≤ Y →
    Subgroup.normalizer (P : Set H) ⊓ I ≤ Y →
    ((IsSLType 2 (ZMod p) ↥I ∨ IsPSLType 2 (ZMod p) ↥I ∨
        IsSLType 3 (ZMod p) ↥I) ∨
      (p = 7 ∧ IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 7)))
        (fun B _ => Nat.card B = 2) ↥I) ∨
      (p = 5 ∧
        (IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 6)))
            (fun B _ => Nat.card B = 2) ↥I ∨
          IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 5)))
            (fun B _ => IsQ8D8Type B) ↥I ∨
          IsExtNotation (fun A _ => Nat.card A = 5) (fun B _ => IsQ8D8Type B) ↥I)) ∨
      (p = 3 ∧
        (IsSLType 2 (ZMod 5) ↥I ∨
          IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 5)))
            (fun B _ => IsQ8D8Type B) ↥I))) →
    IsCyclic ↥D ∧ D ≤ I ∧ IsSLType 3 (ZMod p) ↥I ∧ d ∣ p + 1 ∧
      IsMaxParabolicP p I Y

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
