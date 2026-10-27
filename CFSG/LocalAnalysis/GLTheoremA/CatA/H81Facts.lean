module

public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsProp65

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

@[expose] def H81Choice (p : ℕ) {H : Type} [Group H] [Finite H] (P : Subgroup H)
    (JType : Subgroup H → Prop) : Prop :=
  ∃ yy ∈ P, yy ≠ 1 ∧ ∃ JH : Subgroup H,
    GLAPComponent p (Subgroup.centralizer ({yy} : Set H)) JH ∧
    (∀ K : Subgroup H, GLAPComponent p (Subgroup.centralizer ({yy} : Set H)) K → K = JH) ∧
    JType JH ∧
    (∃ zz ∈ P, zz ∉ Subgroup.zpowers yy ∧
      GLAPLayer p (JH ⊓ Subgroup.centralizer ({zz} : Set H)) ≠ ⊥) ∧
    (∀ α : MulAut H, α ^ p = 1 → (∀ j ∈ JH, α j * j⁻¹ ∈ GLAPPrimeCoreOf p JH) →
      ∃ k : ℤ, α = MulAut.conj (yy ^ k))

@[expose] def H81FactA3 : Prop :=
  ∀ (p : ℕ) (Q : TauCeti.PrimePower), p.Prime → p ≠ 2 → Q.p ≠ 2 → p ∣ Q.card - 1 →
    ∀ (H : Type) [Group H] [Finite H], catalogIs H (onLie fun d => d = .A 3 Q) →
      ∀ P : Subgroup H, IsElemAbelian p P → Nat.card P = p ^ 3 →
        H81Choice p P (IsSL3Type p Q.p)

@[expose] def H81FactTwA3 : Prop :=
  ∀ (p : ℕ) (Q : TauCeti.PrimePower), p.Prime → p ≠ 2 → Q.p ≠ 2 → p ∣ Q.card + 1 →
    ∀ (H : Type) [Group H] [Finite H], catalogIs H (onLie fun d => d = .twistedA 3 Q) →
      ∀ P : Subgroup H, IsElemAbelian p P → Nat.card P = p ^ 3 →
        H81Choice p P (IsSL3Type p Q.p)

@[expose] def H81FactB3 : Prop :=
  ∀ (p : ℕ) (Q : TauCeti.PrimePower), p.Prime → p ≠ 2 → Q.p ≠ 2 → p ∣ Q.card ^ 2 - 1 →
    ∀ (H : Type) [Group H] [Finite H], catalogIs H (onLie fun d => d = .B 3 Q) →
      ∀ P : Subgroup H, IsElemAbelian p P → Nat.card P = p ^ 3 →
        H81Choice p P (IsOmegaType p Q.p)

@[expose] def H81FactTwD4 : Prop :=
  ∀ (p : ℕ) (Q : TauCeti.PrimePower), p.Prime → p ≠ 2 → Q.p ≠ 2 → p ∣ Q.card ^ 2 - 1 →
    ∀ (H : Type) [Group H] [Finite H], catalogIs H (onLie fun d => d = .twistedD 4 Q) →
      ∀ P : Subgroup H, IsElemAbelian p P → Nat.card P = p ^ 3 →
        H81Choice p P (IsOmegaType p Q.p)

@[expose] def H81FactD4 : Prop :=
  ∀ (p : ℕ) (Q : TauCeti.PrimePower), p.Prime → p ≠ 2 → Q.p ≠ 2 → p ∣ Q.card ^ 2 - 1 →
    ∀ (H : Type) [Group H] [Finite H], catalogIs H (onLie fun d => d = .D 4 Q) →
      ∀ P : Subgroup H, IsElemAbelian p P → Nat.card P = p ^ 4 →
        H81Choice p P (IsOmegaType p Q.p)

@[expose] def H81FamilyDisjoint : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (Q Q' : TauCeti.PrimePower),
    ¬ ((catalogIs H (onLie fun d => d = .A 3 Q) ∨ catalogIs H (onLie fun d => d = .twistedA 3 Q)) ∧
      (catalogIs H (onLie fun d => d = .B 3 Q') ∨ catalogIs H (onLie fun d => d = .twistedD 4 Q') ∨
        catalogIs H (onLie fun d => d = .D 4 Q')))

end CFSG.LocalAnalysis.GLTheoremA
