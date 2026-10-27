module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

@[expose] def S2019Omega (p : ℕ) {Ω : Type} [Group Ω] [Finite Ω] (S B D J : Subgroup Ω) : Prop :=
  B ⊓ centModSubgroup p S ≠ ⊥ → D ≤ B → B ⊓ centModSubgroup p S ≤ D →
    (B ⊓ centModSubgroup p S).relIndex D = p → p ^ 2 * Nat.card D ≤ Nat.card B →
    GLAPComponent p (S ⊓ Subgroup.centralizer (D : Set Ω)) J →
    B ≤ Subgroup.normalizer (J : Set Ω) → (∀ b ∈ B, CentMod p J b ↔ b ∈ D) →
    ∀ T : Subgroup Ω, T ≤ S → IsPGroup 2 T → J ≤ Subgroup.normalizer (T : Set Ω) → ⁅T, J⁆ = ⊥

@[expose] def S2019IsA1 : TauCeti.LieTypeIndex → Prop
  | .A 1 _ => True
  | _ => False

@[expose] def S2019FactClassical : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B D J : Subgroup Ω), S.Normal →
      CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
      catalogIs (PSimple p S)
        (onLie fun d => d.characteristic = q ∧
          CFSG.LocalAnalysis.GLTheoremA.S267.S267ClassicalIdx d ∧ ¬ S2019IsA1 d) →
      IsElemAbelian p B → S ⊔ B = ⊤ → p ^ GLATwoLocalRank p Ω ≤ Nat.card B →
      S2019Omega p S B D J

@[expose] def S2019FactA1 : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B D J : Subgroup Ω), S.Normal →
      CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
      catalogIs (PSimple p S) (onLie fun d => d.characteristic = q ∧ S2019IsA1 d) →
      IsElemAbelian p B → S ⊔ B = ⊤ → p ^ GLATwoLocalRank p Ω ≤ Nat.card B →
      S2019Omega p S B D J

@[expose] def S2019FactExceptional : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B D J : Subgroup Ω), S.Normal →
      CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
      catalogIs (PSimple p S)
        (onLie fun d => d.characteristic = q ∧ ¬ CFSG.LocalAnalysis.GLTheoremA.S267.S267ClassicalIdx d) →
      IsElemAbelian p B → S ⊔ B = ⊤ → p ^ GLATwoLocalRank p Ω ≤ Nat.card B →
      S2019Omega p S B D J

@[expose] def S2019FactAmbAut : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (S : Type) [Group S], catalogIs S (ambiguousChev q) →
      ∀ A : Subgroup (MulAut S), IsElemAbelian p A → Nat.card A < p ^ 2

@[expose] def S2019FactAmbiguous : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B D J : Subgroup Ω), S.Normal →
      CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
      catalogIs (PSimple p S) (ambiguousChev q) →
      IsElemAbelian p B → S ⊔ B = ⊤ → p ^ GLATwoLocalRank p Ω ≤ Nat.card B →
      S2019Omega p S B D J

end CFSG.LocalAnalysis.GLTheoremA.S2019

end
