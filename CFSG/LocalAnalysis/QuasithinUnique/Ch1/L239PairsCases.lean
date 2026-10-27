
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedInputs

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin CFSG.Blueprint

@[expose] def PairConclusion {G : Type} [Group G] (L R : Subgroup G) : Prop :=
  ∃ K₁ K₂ : Subgroup G, K₁ ≤ L ∧ K₂ ≤ L ∧ K₁ ≠ L ∧ K₂ ≠ L ∧ K₁ ⊔ K₂ = L ∧
    R ≤ Subgroup.normalizer (K₁ : Set G) ∧ R ≤ Subgroup.normalizer (K₂ : Set G) ∧
    CharTwo K₁ ∧ CharTwo K₂ ∧ ¬ HasChi0Block K₁ ∧ ¬ HasChi0Block K₂

@[expose] def PairsFor (T : ∀ {G : Type} [Group G], Subgroup G → Subgroup G → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L R : Subgroup G), CFSG.IsQuasisimple ↥L → T L R →
    IsPGroup 2 R → R ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf (R ⊓ L) L →
    PairConclusion L R

@[expose] def TypeG2 {G : Type} [Group G] (L _R : Subgroup G) : Prop :=
  ∃ f : ℕ, 2 ≤ f ∧ ChevalleyExceptionalModel ↥L .G2 2 f

@[expose] def Type3D4 {G : Type} [Group G] (L _R : Subgroup G) : Prop :=
  ∃ f : ℕ, 1 ≤ f ∧ ChevalleyExceptionalModel ↥L .trialityD4 2 f

@[expose] def Type2F4 {G : Type} [Group G] (L _R : Subgroup G) : Prop :=
  ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel ↥L .twistedF4 2 f

@[expose] def TypeTits {G : Type} [Group G] (L _R : Subgroup G) : Prop :=
  ReeTitsModel ↥L .Tits 2 1

@[expose] def TypeL52In {G : Type} [Group G] (L R : Subgroup G) : Prop :=
  StatedClassicalModel ↥L .PSL 5 2 1 ∧ ¬ ∃ s ∈ R, InducesOuter s L

@[expose] def TypeL52Out {G : Type} [Group G] (L R : Subgroup G) : Prop :=
  StatedClassicalModel ↥L .PSL 5 2 1 ∧ ∃ s ∈ R, InducesOuter s L

@[expose] def TypeU33 {G : Type} [Group G] (L _R : Subgroup G) : Prop :=
  StatedClassicalModel ↥L .PSU 3 3 1

@[expose] def TypeG24 {G : Type} [Group G] (L _R : Subgroup G) : Prop :=
  IsG24Quot L

@[expose] def TypeSporadic (s : TauCeti.SporadicName) {G : Type} [Group G] (L _R : Subgroup G) :
    Prop :=
  Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* NativeSporadic.Carrier s)

@[expose] def TypeL42 {G : Type} [Group G] (L R : Subgroup G) : Prop :=
  StatedClassicalModel ↥L .PSL 4 2 1 ∧ ¬ ∃ s ∈ R, InducesOuter s L

theorem l239ParabolicPairs_of_cases
    (hG2 : PairsFor TypeG2) (h3D4 : PairsFor Type3D4) (h2F4 : PairsFor Type2F4)
    (hTits : PairsFor TypeTits) (hL52In : PairsFor TypeL52In) (hL52Out : PairsFor TypeL52Out)
    (hU33 : PairsFor TypeU33)
    (hG24 : PairsFor TypeG24) (hM12 : PairsFor (TypeSporadic .M12))
    (hM24 : PairsFor (TypeSporadic .M24)) (hJ2 : PairsFor (TypeSporadic .J2))
    (hJ4 : PairsFor (TypeSporadic .J4)) (hHS : PairsFor (TypeSporadic .HS))
    (hHe : PairsFor (TypeSporadic .He)) (hRu : PairsFor (TypeSporadic .Ru))
    (hL42 : PairsFor TypeL42) : L239ParabolicPairs := by
  intro G _ _ L R hq hty hR hRN hS
  rcases hty with ((⟨f, ⟨hf, hmod⟩ | ⟨hf, hmod⟩ | ⟨hodd, hf, hmod⟩⟩ | hmod | hmod | hmod) |
    hmod | ⟨s, hs, hmod⟩ | hmod)
  · exact hG2 G L R hq ⟨f, hf, hmod⟩ hR hRN hS
  · exact h3D4 G L R hq ⟨f, hf, hmod⟩ hR hRN hS
  · exact h2F4 G L R hq ⟨f, hodd, hf, hmod⟩ hR hRN hS
  · exact hTits G L R hq hmod hR hRN hS
  · by_cases hout : ∃ s ∈ R, InducesOuter s L
    · exact hL52Out G L R hq ⟨hmod, hout⟩ hR hRN hS
    · exact hL52In G L R hq ⟨hmod, hout⟩ hR hRN hS
  · exact hU33 G L R hq hmod hR hRN hS
  · exact hG24 G L R hq hmod hR hRN hS
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hM12 G L R hq hmod hR hRN hS
    · exact hM24 G L R hq hmod hR hRN hS
    · exact hJ2 G L R hq hmod hR hRN hS
    · exact hJ4 G L R hq hmod hR hRN hS
    · exact hHS G L R hq hmod hR hRN hS
    · exact hHe G L R hq hmod hR hRN hS
    · exact hRu G L R hq hmod hR hRN hS
  · exact hL42 G L R hq hmod hR hRN hS

end CFSG.QuasithinUnique.Vol2Native.L239
