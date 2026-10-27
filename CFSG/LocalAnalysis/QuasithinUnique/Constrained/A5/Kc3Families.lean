module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Inputs25

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.Assembly.LowTwoRank

@[expose] def Kc3For (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K L S₀ T₀ : Subgroup G),
    CFSG.IsQuasisimple ↥K → P (↥K ⧸ Subgroup.center ↥K) → IsPGroup 2 ↥(Subgroup.center ↥K) →
    L ≤ K → IsShort2 L → IsAltType L 5 → S₀ ≤ Subgroup.normalizer (L : Set G) → IsPGroup 2 S₀ →
    IsPGroup 2 T₀ → S₀ ≤ T₀ → T₀ ≤ Subgroup.normalizer (K : Set G) → IsSylowTwoOf T₀ (K ⊔ T₀) →
    ∃ X S₁ : Subgroup G, CharTwo X ∧ L ⊔ S₀ ≤ X ∧ X ≤ K ⊔ T₀ ∧ IsSylowTwoOf S₁ X ∧ S₀ ≤ S₁ ∧
      ¬ quasithinIsLocal S₁ L

theorem kc3Inspection_iff : Kc3Inspection ↔ Kc3For Kc3Group := Iff.rfl

theorem Kc3For.mono {P Q : ∀ (X : Type) [Group X], Prop}
    (hPQ : ∀ (X : Type) [Group X], P X → Q X) (h : Kc3For Q) : Kc3For P :=
  fun G _ _ K L S₀ T₀ hq hP hZ => h G K L S₀ T₀ hq (hPQ _ hP) hZ

theorem Kc3For.or {P Q : ∀ (X : Type) [Group X], Prop} (hP : Kc3For P) (hQ : Kc3For Q) :
    Kc3For (fun X _ => P X ∨ Q X) := by
  intro G _ _ K L S₀ T₀ hq hPQ hZ
  rcases hPQ with h | h
  · exact hP G K L S₀ T₀ hq h hZ
  · exact hQ G K L S₀ T₀ hq h hZ

@[expose] def Kc3PSL3 (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel X .PSL 3 2 f

@[expose] def Kc3PSp4 (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel X .PSp 2 2 f

@[expose] def Kc3G2 (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, 2 ≤ f ∧ CFSG.Blueprint.ChevalleyExceptionalModel X .G2 2 f

@[expose] def Kc3D4 (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, 1 ≤ f ∧ CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 2 f

@[expose] def Kc3F4 (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ CFSG.Blueprint.ReeTitsModel X .twistedF4 2 f

@[expose] def Kc3Tits (X : Type) [Group X] : Prop :=
  CFSG.Blueprint.ReeTitsModel X .Tits 2 1

@[expose] def Kc3L4 (X : Type) [Group X] : Prop := StatedClassicalModel X .PSL 4 2 1

@[expose] def Kc3L5 (X : Type) [Group X] : Prop := StatedClassicalModel X .PSL 5 2 1

@[expose] def Kc3Spor (s : TauCeti.SporadicName) (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier s)

structure Kc3Families : Prop where
  psl3 : Kc3For Kc3PSL3
  psp4 : Kc3For Kc3PSp4
  g2 : Kc3For Kc3G2
  d4 : Kc3For Kc3D4
  f4 : Kc3For Kc3F4
  tits : Kc3For Kc3Tits
  l4 : Kc3For Kc3L4
  l5 : Kc3For Kc3L5
  m22 : Kc3For (Kc3Spor .M22)
  m23 : Kc3For (Kc3Spor .M23)
  m24 : Kc3For (Kc3Spor .M24)
  j4 : Kc3For (Kc3Spor .J4)
  hs : Kc3For (Kc3Spor .HS)
  he : Kc3For (Kc3Spor .He)
  ru : Kc3For (Kc3Spor .Ru)

theorem kc3Inspection_of_families (h : Kc3Families) : Kc3Inspection := by
  intro G _ _ K L S₀ T₀ hq hK hZ hLK hL h5 hSL hS hT hST hTK hTS
  rcases hK with ⟨f, hf, hm | hm⟩ | ⟨f, ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hodd, hf, hm⟩⟩ | hm |
    ⟨n, hn, hm⟩ | ⟨s, hs, hm⟩
  · exact h.psl3 G K L S₀ T₀ hq ⟨f, hf, hm⟩ hZ hLK hL h5 hSL hS hT hST hTK hTS
  · exact h.psp4 G K L S₀ T₀ hq ⟨f, hf, hm⟩ hZ hLK hL h5 hSL hS hT hST hTK hTS
  · exact h.g2 G K L S₀ T₀ hq ⟨f, hf, hm⟩ hZ hLK hL h5 hSL hS hT hST hTK hTS
  · exact h.d4 G K L S₀ T₀ hq ⟨f, hf, hm⟩ hZ hLK hL h5 hSL hS hT hST hTK hTS
  · exact h.f4 G K L S₀ T₀ hq ⟨f, hodd, hf, hm⟩ hZ hLK hL h5 hSL hS hT hST hTK hTS
  · exact h.tits G K L S₀ T₀ hq hm hZ hLK hL h5 hSL hS hT hST hTK hTS
  · rcases hn with rfl | rfl
    · exact h.l4 G K L S₀ T₀ hq hm hZ hLK hL h5 hSL hS hT hST hTK hTS
    · exact h.l5 G K L S₀ T₀ hq hm hZ hLK hL h5 hSL hS hT hST hTK hTS
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h.m22 G K L S₀ T₀ hq hm hZ hLK hL h5 hSL hS hT hST hTK hTS
    · exact h.m23 G K L S₀ T₀ hq hm hZ hLK hL h5 hSL hS hT hST hTK hTS
    · exact h.m24 G K L S₀ T₀ hq hm hZ hLK hL h5 hSL hS hT hST hTK hTS
    · exact h.j4 G K L S₀ T₀ hq hm hZ hLK hL h5 hSL hS hT hST hTK hTS
    · exact h.hs G K L S₀ T₀ hq hm hZ hLK hL h5 hSL hS hT hST hTK hTS
    · exact h.he G K L S₀ T₀ hq hm hZ hLK hL h5 hSL hS hT hST hTK hTS
    · exact h.ru G K L S₀ T₀ hq hm hZ hLK hL h5 hSL hS hT hST hTK hTS

end CFSG.QuasithinUnique.A5
