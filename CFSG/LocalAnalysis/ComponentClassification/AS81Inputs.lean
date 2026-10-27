module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Defs

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Matrix
open scoped MatrixGroups

section Tim77

variable {H : Type} [Group H]

abbrev tim77L (Q : Subgroup H) (h : H) : Subgroup H := Q ⊔ rightConjugate Q h

abbrev tim77B (Q : Subgroup H) (h : H) : Subgroup H :=
  Q ⊓ normalizer (rightConjugate Q h : Set H)

abbrev tim77D (Q : Subgroup H) (h : H) : Subgroup H :=
  rightConjugate Q h ⊓ normalizer (Q : Set H)

abbrev tim77I (Q : Subgroup H) (h : H) : Subgroup H := Q ⊓ rightConjugate Q h

abbrev tim77M (Q : Subgroup H) (h : H) : Subgroup H := tim77B Q h ⊔ tim77D Q h

@[expose] def Tim77NaturalSL2 (Q : Subgroup H) (h : H) (F : Type) [Field F]
    (ψ : ↥(tim77L Q h) →* SL(2, F)) : Prop :=
  ∃ (n : ℕ) (θ : (Fin n → Fin 2 → F) → H),
    (∀ v, θ v ∈ tim77M Q h) ∧
    (∀ v v', θ (v + v') * (θ v * θ v')⁻¹ ∈ tim77I Q h) ∧
    (∀ v, θ v ∈ tim77I Q h → v = 0) ∧
    (∀ m ∈ tim77M Q h, ∃ v, θ v * m⁻¹ ∈ tim77I Q h) ∧
    ∀ (x : ↥(tim77L Q h)) (v : Fin n → Fin 2 → F),
      θ (fun j => (ψ x : Matrix (Fin 2) (Fin 2) F) *ᵥ v j) *
        ((x : H) * θ v * (x : H)⁻¹)⁻¹ ∈ tim77I Q h

@[expose] def Tim77NaturalSz (Q : Subgroup H) (h : H) (a : ℕ)
    (ψ : ↥(tim77L Q h) →* GL (Fin 4) (GaloisField 2 (2 * a + 1))) : Prop :=
  ∃ (n : ℕ) (θ : (Fin n → Fin 4 → GaloisField 2 (2 * a + 1)) → H),
    (∀ v, θ v ∈ tim77M Q h) ∧
    (∀ v v', θ (v + v') * (θ v * θ v')⁻¹ ∈ tim77I Q h) ∧
    (∀ v, θ v ∈ tim77I Q h → v = 0) ∧
    (∀ m ∈ tim77M Q h, ∃ v, θ v * m⁻¹ ∈ tim77I Q h) ∧
    ∀ (x : ↥(tim77L Q h)) (v : Fin n → Fin 4 → GaloisField 2 (2 * a + 1)),
      θ (fun j => ((ψ x : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ v j) *
        ((x : H) * θ v * (x : H)⁻¹)⁻¹ ∈ tim77I Q h

@[expose] def Tim77Irreducible (Q : Subgroup H) (h : H) : Prop :=
  ∃ s : Finset (Subgroup H),
    (∀ W ∈ s, tim77I Q h ≤ W ∧ W ≤ tim77M Q h ∧
      tim77L Q h ≤ normalizer (W : Set H) ∧ W ≠ tim77I Q h ∧
      ∀ U : Subgroup H, tim77I Q h ≤ U → U ≤ W → tim77L Q h ≤ normalizer (U : Set H) →
        U = tim77I Q h ∨ U = W) ∧
    (⨆ W ∈ s, W) ⊔ tim77I Q h = tim77M Q h ∧
    ∀ W ∈ s, W ⊓ ((⨆ (W' ∈ s) (_ : W' ≠ W), W') ⊔ tim77I Q h) = tim77I Q h

structure Tim77Conclusion (Q : Subgroup H) (h : H) : Prop where
  isPGroup : IsPGroup 2 (tim77M Q h)
  normal : tim77L Q h ≤ normalizer (tim77M Q h : Set H)
  elem : ∀ x ∈ tim77M Q h, ∀ y ∈ tim77M Q h,
    x * y * x⁻¹ * y⁻¹ ∈ tim77I Q h ∧ x * x ∈ tim77I Q h
  lt_D : tim77I Q h < tim77D Q h
  le_center : tim77I Q h ≤ centralizer (tim77L Q h : Set H)
  fix : ∀ x ∈ Q, x ∉ tim77B Q h → ∀ m ∈ tim77M Q h,
    x * m * x⁻¹ * m⁻¹ ∈ tim77I Q h → m ∈ tim77B Q h
  cases :
    (∃ (f : ℕ) (F : Type) (_ : Field F) (_ : Finite F), 2 ≤ f ∧ Nat.card F = 2 ^ f ∧
      ∃ ψ : ↥(tim77L Q h) →* SL(2, F), Function.Surjective ψ ∧
        ψ.ker = (tim77M Q h).subgroupOf (tim77L Q h) ∧ Tim77NaturalSL2 Q h F ψ) ∨
    (∃ a : ℕ, 1 ≤ a ∧ ∃ ψ : ↥(tim77L Q h) →* GL (Fin 4) (GaloisField 2 (2 * a + 1)),
      ψ.range = Sz a ∧ ψ.ker = (tim77M Q h).subgroupOf (tim77L Q h) ∧
        Tim77NaturalSz Q h a ψ) ∨
    (∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ ∃ _ : ((tim77M Q h).subgroupOf (tim77L Q h)).Normal,
      Nonempty (↥(tim77L Q h) ⧸ (tim77M Q h).subgroupOf (tim77L Q h) ≃* DihedralGroup m) ∧
        Tim77Irreducible Q h)

structure Tim77Facts (Q : Subgroup H) (h : H) : Prop where
  normal : tim77L Q h ≤ normalizer (tim77M Q h : Set H)
  elem : ∀ x ∈ tim77M Q h, ∀ y ∈ tim77M Q h,
    x * y * x⁻¹ * y⁻¹ ∈ tim77I Q h ∧ x * x ∈ tim77I Q h
  lt_D : tim77I Q h < tim77D Q h
  lt_B : tim77B Q h < Q
  le_center : tim77I Q h ≤ centralizer (tim77L Q h : Set H)
  fix : ∀ x ∈ Q, x ∉ tim77B Q h → ∀ m ∈ tim77M Q h,
    x * m * x⁻¹ * m⁻¹ ∈ tim77I Q h → m ∈ tim77B Q h
  fixD : ∀ d ∈ tim77D Q h, d ∉ tim77I Q h → ∀ x ∈ Q,
    x * d * x⁻¹ * d⁻¹ ∈ tim77I Q h → x ∈ tim77B Q h
  card_eq : Nat.card (tim77B Q h) = Nat.card (tim77D Q h)
  cases : 2 * Nat.card (tim77B Q h) = Nat.card Q ∨
    4 * Nat.card (tim77I Q h) ≤ Nat.card (tim77D Q h)

end Tim77

@[expose] def Tim77Lemma24 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (S Q : Subgroup H), IsSylowOf 2 S ⊤ → Q ≤ S →
    IsElemAbelian 2 Q → (∀ h : H, rightConjugate Q h ≤ S → rightConjugate Q h = Q) →
    (∃ x ∈ Q, ∃ h : H, h⁻¹ * x * h ∈ S ∧ h⁻¹ * x * h ∉ Q) →
    ∃ h : H, Tim77Facts Q h

structure IsAffinePlane (P : Type) (lines : Set (Set P)) : Prop where
  line_unique : ∀ p q : P, p ≠ q → ∃! ℓ, ℓ ∈ lines ∧ p ∈ ℓ ∧ q ∈ ℓ
  parallel : ∀ ℓ ∈ lines, ∀ p : P, p ∉ ℓ → ∃! m, m ∈ lines ∧ p ∈ m ∧ Disjoint ℓ m
  nondegenerate : ∃ p q r : P, ¬ ∃ ℓ ∈ lines, p ∈ ℓ ∧ q ∈ ℓ ∧ r ∈ ℓ

@[expose] def OstromWagnerAG24 : Prop :=
  ∀ (P : Type) [Finite P] (lines : Set (Set P)), IsAffinePlane P lines → Nat.card P = 16 →
    ∀ G : Subgroup (Equiv.Perm P), (∀ g ∈ G, ∀ ℓ ∈ lines, (g : P → P) '' ℓ ∈ lines) →
      (∀ p₁ p₂ q₁ q₂ : P, p₁ ≠ p₂ → q₁ ≠ q₂ → ∃ g ∈ G, g p₁ = q₁ ∧ g p₂ = q₂) →
      ∃ T : Subgroup (Equiv.Perm P), T ≤ G ∧ G ≤ normalizer (T : Set (Equiv.Perm P)) ∧
        IsElemAbelian 2 T ∧ Nat.card T = 16 ∧ ∀ p q : P, ∃ t ∈ T, t p = q

@[expose] def AlternatingNoL34Component : Prop :=
  ∀ (n : ℕ) (t : alternatingGroup (Fin n)), orderOf t = 2 →
    ∀ A' : Subgroup (alternatingGroup (Fin n)), A' ≤ centralizer ({t} : Set _) →
      centralizer ({t} : Set _) ≤ normalizer (A' : Set (alternatingGroup (Fin n))) →
      Open.IsQuasisimple ↥A' → ¬ TypeL34 (↥A' ⧸ center ↥A')

end CFSG.ComponentClassification.AS81
