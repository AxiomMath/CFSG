module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltAssembly

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.AGLEmbedding

@[expose] def IdxPlusA (p : ℕ) : TauCeti.LieTypeIndex → Prop
  | .twistedA _ q => q.p = 2 ∧ q.card ≠ 2 ∧ p ∣ q.card + 1
  | _ => False

@[expose] def IdxPlusD (p : ℕ) : TauCeti.LieTypeIndex → Prop
  | .twistedD _ q => q.p = 2 ∧ q.card ≠ 2 ∧ p ∣ q.card + 1
  | _ => False

@[expose] def AltPlusCellA : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y) (p : ℕ) (x : Y), CompParabE L J →
    (p = 5 ∨ p = 7) → PerfectSectionsAltSq p J → x ∈ L → x ^ p = 1 →
    x ∉ Subgroup.centralizer (L : Set Y) → (∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) →
    IsLieOf (IdxPlusA p) (↥L ⧸ Subgroup.center ↥L) →
    (∃ E : Subgroup Y, E ≤ L ⊓ Subgroup.centralizer ({x} : Set Y) ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ 3) → False

@[expose] def AltPlusCellD : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y) (p : ℕ) (x : Y), CompParabE L J →
    (p = 5 ∨ p = 7) → PerfectSectionsAltSq p J → x ∈ L → x ^ p = 1 →
    x ∉ Subgroup.centralizer (L : Set Y) → (∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) →
    IsLieOf (IdxPlusD p) (↥L ⧸ Subgroup.center ↥L) →
    (∃ E : Subgroup Y, E ≤ L ⊓ Subgroup.centralizer ({x} : Set Y) ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ 3) → False

theorem isLieOf_plus_cases {p : ℕ} {X : Type} [Group X] (h : IsLieOf (IdxPlus p) X) :
    IsLieOf (IdxPlusA p) X ∨ IsLieOf (IdxPlusD p) X := by
  obtain ⟨⟨d, hv⟩, hd, he⟩ := h
  cases d <;> simp only [IdxPlus] at hd
  · exact Or.inl ⟨⟨_, hv⟩, hd, he⟩
  · exact Or.inr ⟨⟨_, hv⟩, hd, he⟩

theorem altPlusCell_of (hA : AltPlusCellA) (hD : AltPlusCellD) : AltPlusCell := by
  intro Y _ _ L J p x hC hp hAlt hxL hxp hxC hfix hX hE
  rcases isLieOf_plus_cases hX with h | h
  · exact hA Y L J p x hC hp hAlt hxL hxp hxC hfix h hE
  · exact hD Y L J p x hC hp hAlt hxL hxp hxC hfix h hE

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
