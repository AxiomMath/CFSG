module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs
public import CFSG.Open.LocalVocabulary
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.Open

@[expose] def IsStepThreeIndex (p : ℕ) : TauCeti.CFSGIndex → Prop
  | .cyclic _ _ => False
  | .alternating n _ => (p = 3 ∧ n = 6) ∨ (p = 5 ∧ n = 10)
  | .lie d =>
    (p = 3 ∧ ((∃ q : TauCeti.PrimePower, q.p = 3 ∧ q.exponent = 1 ∧ d.1 = .twistedA 2 q) ∨
      (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .A 1 q) ∨
      (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ d.1 = .A 2 q))) ∨
    (p = 5 ∧ ((∃ q : TauCeti.PrimePower, q.p = 5 ∧ q.exponent = 2 ∧ d.1 = .A 1 q) ∨
      (∃ q : TauCeti.PrimePower, q.p = 5 ∧ q.exponent = 1 ∧ d.1 = .twistedA 2 q) ∨
      d.1 = .suzuki 2 ∨ d.1 = .tits))
  | .sporadic s => (p = 3 ∧ s = .M11) ∨ (p = 5 ∧ s = .McL)

@[expose] def StepThreeGroup (p : ℕ) (K : Type*) [Group K] : Prop :=
  ∃ i : TauCeti.CFSGIndex, IsStepThreeIndex p i ∧ Nonempty (K ≃* i.Group)

@[expose] def KFactStepThreeIrred : Prop :=
  ∀ (p : ℕ) (K : Type) [Group K] [Finite K], StepThreeGroup p K → ∀ S : Sylow p K,
    (∀ V : Subgroup K, V ≤ S → ¬ V ≤ (frattini ↥(S : Subgroup K)).map (S : Subgroup K).subtype →
      Subgroup.normalizer ((S : Subgroup K) : Set K) ≤ Subgroup.normalizer (V : Set K) →
        V = S) ∧
    (∀ V : Subgroup K, V ≠ ⊥ → (∀ v ∈ V, v ∈ S ∧ v ^ p = 1 ∧ ∀ s ∈ S, v * s = s * v) →
      Subgroup.normalizer ((S : Subgroup K) : Set K) ≤ Subgroup.normalizer (V : Set K) →
        ∀ x ∈ S, x ^ p = 1 → (∀ s ∈ S, x * s = s * x) → x ∈ V)

@[expose] def KFactStepThreeMaximal : Prop :=
  ∀ (p : ℕ) (K : Type) [Group K] [Finite K], StepThreeGroup p K →
    IsEmpty (K ≃* alternatingGroup (Fin 10)) → ∀ S : Sylow p K,
      IsCoatom (Subgroup.normalizer ((S : Subgroup K) : Set K))

@[expose] def KFactAltTenOvergroup : Prop :=
  ∀ S : Sylow 5 (alternatingGroup (Fin 10)), ∃ B : Finset (Fin 10), B.card = 5 ∧
    (∀ s ∈ (S : Subgroup (alternatingGroup (Fin 10))), ∀ i ∈ B,
      (s : Equiv.Perm (Fin 10)) i ∈ B) ∧
    (∃ g ∈ Subgroup.normalizer
        ((S : Subgroup (alternatingGroup (Fin 10))) : Set (alternatingGroup (Fin 10))),
      ∀ i ∈ B, (g : Equiv.Perm (Fin 10)) i ∉ B) ∧
    ∀ Y : Subgroup (alternatingGroup (Fin 10)),
      Subgroup.normalizer
          ((S : Subgroup (alternatingGroup (Fin 10))) : Set (alternatingGroup (Fin 10))) ≤ Y →
        Y ≠ ⊤ → ∀ y ∈ Y, (∀ i ∈ B, (y : Equiv.Perm (Fin 10)) i ∈ B) ∨
          ∀ i ∈ B, (y : Equiv.Perm (Fin 10)) i ∉ B

@[expose] def KFactStepThreeCentNilp : Prop :=
  ∀ (p : ℕ) (A : Type) [Group A] [Finite A] (K S : Subgroup A), K.Normal →
    Subgroup.centralizer (K : Set A) = ⊥ → StepThreeGroup p ↥K →
    CFSG.ABGLocalTools.IsSylowOf p S K →
      HasNormalPComplement p ↥(Subgroup.centralizer (S : Set A))

@[expose] def KFactStepThreeCentSylow : Prop :=
  ∀ (p : ℕ) (A : Type) [Group A] [Finite A] (K S : Subgroup A), K.Normal →
    Subgroup.centralizer (K : Set A) = ⊥ → StepThreeGroup p ↥K →
    CFSG.ABGLocalTools.IsSylowOf p S K → ∀ c ∈ Subgroup.centralizer (S : Set A),
      ∀ n : ℕ, c ^ (p ^ n) = 1 → c ∈ S

@[expose] def KFactStepThreeNormSolv : Prop :=
  ∀ (p : ℕ) (A : Type) [Group A] [Finite A] (K S : Subgroup A), K.Normal →
    Subgroup.centralizer (K : Set A) = ⊥ → StepThreeGroup p ↥K →
    CFSG.ABGLocalTools.IsSylowOf p S K → IsSolvable ↥(Subgroup.normalizer (S : Set A))

@[expose] def KFactFieldAutInvert : Prop :=
  ∀ (p : ℕ) (A : Type) [Group A] [Finite A] (K : Subgroup A), K.Normal →
    Subgroup.centralizer (K : Set A) = ⊥ →
    ((p = 3 ∧ ∃ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), q.p = 2 ∧
        q.exponent = 3 ∧ d.1 = .A 1 q ∧ Nonempty (↥K ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
      (p = 5 ∧ ∃ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 ∧
        Nonempty (↥K ≃* (TauCeti.CFSGIndex.lie d).Group))) →
    ∀ φ : A, orderOf φ = p → φ ∉ K →
      ∀ x ∈ K ⊓ Subgroup.centralizer ({φ} : Set A), orderOf x = p →
        ∃ t ∈ K ⊓ Subgroup.centralizer ({φ} : Set A), orderOf t = 2 ∧ t * x * t⁻¹ = x⁻¹

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
