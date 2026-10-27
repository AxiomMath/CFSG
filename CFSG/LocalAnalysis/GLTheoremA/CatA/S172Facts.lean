module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

structure Cfg172 (p : ℕ) {Ω : Type} [Group Ω] [Finite Ω] (S B D K : Subgroup Ω) (x : Ω) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  normal : S.Normal
  qs : CFSG.Open.IsQuasisimple ↥S
  elem : IsElemAbelian p B
  top : S ⊔ B = ⊤
  rank : p ^ GLATwoLocalRank p Ω ≤ Nat.card B
  four : p ^ 4 ≤ Nat.card B
  mem : x ∈ B
  ne_one : x ≠ 1
  cent : ∀ b ∈ B, b ∈ Subgroup.centralizer (S : Set Ω) ↔ b ∈ Subgroup.zpowers x
  idiag : InnerDiagMarking B S
  std : GLAStdSubPre p B x S D K
  e3 : ∃ E : Subgroup Ω, IsE3 p B E ∧ D ≤ E ∧ GLAPLayer p (K ⊓ cs E) ≠ ⊥

@[expose] def S172FactA : Prop :=
  ∀ n : ℕ, Odd n →
    ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B D K : Subgroup Ω) (x : Ω), Cfg172 3 S B D K x →
      catalogIs (PSimple 3 S) (isLnA n 2) → catalogIs (PSimple 3 K) (isLnA ((n - 1) / 2) 4) →
      ∃ D₁ K₁ : Subgroup Ω, GLAStdSubPre 3 B x S D₁ K₁ ∧
        catalogIs (PSimple 3 K₁) (isLnA (n - 2) 2) ∧
        catalogIs (PSimple 3 (GLALayer (S ⊓ cs (D ⊔ D₁)))) (isLnA ((n - 3) / 2) 4)

@[expose] def S172FactB : Prop :=
  ∀ n : ℕ, Odd n →
    ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B D K : Subgroup Ω) (x : Ω), Cfg172 3 S B D K x →
      catalogIs (PSimple 3 S) (isOmPA n 2) → catalogIs (PSimple 3 K) (isUnA (n - 1) 2) →
      ∃ D₁ K₁ : Subgroup Ω, GLAStdSubPre 3 B x S D₁ K₁ ∧
        catalogIs (PSimple 3 K₁) (isOmMA (n - 1) 2) ∧
        catalogIs (PSimple 3 (GLALayer (S ⊓ cs (D ⊔ D₁)))) (isUnA (n - 2) 2)

@[expose] def S172FactC : Prop :=
  ∀ (p n k : ℕ), Even n → 1 ≤ k → p ∣ 2 ^ k + 1 →
    ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B D K : Subgroup Ω) (x : Ω), Cfg172 p S B D K x →
      catalogIs (PSimple p S) (isOmMA n (2 ^ k)) → catalogIs (PSimple p K) (isUnA (n - 1) (2 ^ k)) →
      ∃ D₁ K₁ : Subgroup Ω, GLAStdSubPre p B x S D₁ K₁ ∧
        catalogIs (PSimple p K₁) (isOmPA (n - 1) (2 ^ k)) ∧
        catalogIs (PSimple p (GLALayer (S ⊓ cs (D ⊔ D₁)))) (isUnA (n - 2) (2 ^ k))

end CFSG.LocalAnalysis.GLTheoremA.S172

end
