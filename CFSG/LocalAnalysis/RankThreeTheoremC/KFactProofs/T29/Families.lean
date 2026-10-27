module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Alt

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def T29Concl (X : Type) [Group X] (L : Subgroup X) (x : X) : Prop :=
  (CFSG.HardMathSupport.Solomon.UniquenessMaximal.IsLThreeEps (↥L ⧸ center ↥L) ∧
      Nat.card (center ↥L) ∣ 3 ∧ InducesInnDiagNonInner L x ∧
      HasNormalPComplement 3 ↥(centralizer ({x} : Set X)) ∧
      ((∃ y : X, IsPGroup 3 (zpowers y) ∧ InducesNontrivialFieldAut L y) ∨
        9 ≤ Nat.card (CFSG.pCore 3 X))) ∨
    InducesFieldAutL227 L x

@[expose] def T29Spor : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) (x : X), T29Setup X L x →
    (∃ s : TauCeti.SporadicName,
      Nonempty ((↥L ⧸ center ↥L) ≃* (TauCeti.CFSGIndex.sporadic s).Group)) → T29Concl X L x

@[expose] def T29Chev3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) (x : X), T29Setup X L x →
    (∃ m : TauCeti.ValidLieTypeIndex, m.1.characteristic = 3 ∧
      Nonempty ((↥L ⧸ center ↥L) ≃* (TauCeti.CFSGIndex.lie m).Group)) → T29Concl X L x

@[expose] def T29ChevOther : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) (x : X), T29Setup X L x →
    (∃ m : TauCeti.ValidLieTypeIndex, m.1.characteristic ≠ 3 ∧
      Nonempty ((↥L ⧸ center ↥L) ≃* (TauCeti.CFSGIndex.lie m).Group)) → T29Concl X L x

theorem gl83I291Three_of_families (hN1 : NoncyclicCentreRank) (hA : AltTripleCoverAbelianBound)
    (hS : T29Spor) (h3 : T29Chev3) (ho : T29ChevOther) : GL83I291Three := by
  intro X _ _ hcat hcore L hL huniq hrank x hxo hcent
  have hset : T29Setup X L x := ⟨hcat, hcore, hL, huniq, hrank, hxo, hcent⟩
  obtain ⟨hcyc, hle, hr3⟩ := hset.step0 hN1
  refine ⟨hcyc, hle, hr3, ?_⟩
  obtain ⟨i, ⟨e⟩⟩ := hset.isCatalogGroup_quotient
  have hnonab : ∃ a b : ↥L ⧸ center ↥L, a * b ≠ b * a :=
    ((CFSG.isComponent_iff_open L).mpr hL).1.2.2
  cases i with
  | cyclic p hp =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn5 =>
    exfalso
    by_cases hZ : center ↥L = ⊥
    · exact hset.false_of_alt_center_bot hZ hn5 e
    · exact hset.false_of_alt_center_ne_bot hN1 hA hZ hn5 e
  | lie m =>
    by_cases hch : m.1.characteristic = 3
    · exact h3 X L x hset ⟨m, hch, ⟨e⟩⟩
    · exact ho X L x hset ⟨m, hch, ⟨e⟩⟩
  | sporadic s => exact hS X L x hset ⟨s, ⟨e⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29
