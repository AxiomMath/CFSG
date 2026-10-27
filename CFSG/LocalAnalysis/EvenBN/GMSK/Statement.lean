module

public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open CFSG.Blueprint

@[expose] def LayerOutcome (G : Type) [Group G] (A : Subgroup G) (n : ℕ) : Prop :=
  Nonempty (CFSG.layer G ≃* A × A) ∨
  (LieModel (CFSG.layer G) .PSL 2 2 (2 * n) ∨ LieModel (CFSG.layer G) .PSU 3 2 n ∨
    LieModel (CFSG.layer G) .PSL 3 2 n) ∨
  (n = 2 ∧
    (Nonempty (CFSG.layer G ≃* NativeSporadic.M12) ∨
      Nonempty (CFSG.layer G ≃* NativeSporadic.J1) ∨
      Nonempty (CFSG.layer G ≃* NativeSporadic.J2) ∨
      Nonempty (CFSG.layer G ≃* alternatingGroup (Fin 9)) ∨
      Nonempty (CFSG.layer G ≃* alternatingGroup (Fin 7)) ∨
      LieModel (CFSG.layer G) .PSL 2 5 2 ∨ LieModel (CFSG.layer G) .PSL 3 5 1 ∨
      LieModel (CFSG.layer G) .PSU 3 5 1)) ∨
  (n = 3 ∧ LieModel (CFSG.layer G) .G2 0 3 1)

@[expose] def StdLinearData (G : Type) [Group G] (A : Subgroup G) (n : ℕ) : Prop :=
  2 ≤ n ∧ CFSG.Open.standardComponentIsStandard A ∧ ¬ A.Normal ∧
    ∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ n ∧
      Nonempty (A ≃* Matrix.SpecialLinearGroup (Fin 2) k)

@[expose] def GMSLinearStandardLayerListKRankOneStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.SectionRank.IsKGroupCat G →
    CFSG.Open.standardComponentOddCore G = ⊥ → ∀ (n : ℕ) (A : Subgroup G), StdLinearData G A n →
      (∀ S : Sylow 2 (Subgroup.centralizer (A : Set G)), Nat.card S = 2) → LayerOutcome G A n

end CFSG.LocalAnalysis.EvenBN.GMSK
