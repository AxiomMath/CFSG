module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofFrameRecog
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4FrameC3
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofAdjointRoots

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
open scoped MatrixGroups

@[expose] def e8Node (i : Fin 8) : Fin (Tag.rank .E8) := i

theorem exists_e8_chevalleyExtras
    (K : Type) [Field K] :
    ∃ (O : CommOrder (RootSystem.ofCartan (e8Datum K).isFiniteType (e8Datum K).divisible))
      (C : (Fin (Tag.rank .E8) → ℤ) → (Fin (Tag.rank .E8) → ℤ) → ℕ × ℕ → ℤ),
      ChevalleyExtras (e8Datum K) K (e8Par K) C O := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (e8Datum K).isFiniteType
    (Dv := (e8Datum K).divisible) rfl
  obtain ⟨C, -, hC⟩ := e8_commutatorFormula K O
  exact ⟨O, C, e8_chevalleyExtras K O C hC⟩

@[expose] def e8E7Node (k : Fin 7) : Fin (Tag.rank .E8) := e8Node k.castSucc

theorem e8E7_adj : ∀ i j : Fin 7, edgeE 7 i j → e8E7Node i ≠ e8E7Node j ∧
    Tag.cartan .E8 (e8E7Node i) (e8E7Node j) = -1 ∧
    Tag.cartan .E8 (e8E7Node j) (e8E7Node i) = -1 ∧
    ∃ l : Fin 8,
      ¬ (3 : ℤ) ∣ Tag.cartan .E8 (e8E7Node i) l + 2 * Tag.cartan .E8 (e8E7Node j) l := by
  decide

theorem e8E7_nadj : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
    e8E7Node i ≠ e8E7Node j ∧ Tag.cartan .E8 (e8E7Node i) (e8E7Node j) = 0 ∧
    Tag.cartan .E8 (e8E7Node j) (e8E7Node i) = 0 := by
  decide

theorem exists_psi_E7_E8
    {p f : ℕ} [Fact p.Prime] (hadm : StatedLieAdmissible .E7 0 p f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = p ^ f) :
    ∃ Ψ : (Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField p f)) →* adjointGroup .E8 K,
      Ψ.ker ≤ Subgroup.center _ ∧
      Ψ.range = ⨆ k, rankOne (e8Datum K).rootGroup (e8E7Node k) ∧
      IsQuasisimple ↥(⨆ k, rankOne (e8Datum K).rootGroup (e8E7Node k)) ∧
      Blueprint.LieModel (↥(⨆ k, rankOne (e8Datum K).rootGroup (e8E7Node k)) ⧸
        Subgroup.center ↥(⨆ k, rankOne (e8Datum K).rootGroup (e8E7Node k))) .E7 0 p f := by
  obtain ⟨O, C, hE⟩ := exists_e8_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := exists_levi_frame hE rfl e8E7Node e8E7_adj e8E7_nadj
  exact e7_frame_subgroup hadm hK hcomm hρ hψ

@[expose] def e8LeviE7 : Set (Fin (Tag.rank .E8)) := Set.range e8E7Node

theorem e8_levi_E7_recognition
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    IsQuasisimple ↥(subsystemGroup .E8 K e8LeviE7) ∧
      Blueprint.LieModel (↥(subsystemGroup .E8 K e8LeviE7) ⧸
        Subgroup.center ↥(subsystemGroup .E8 K e8LeviE7)) .E7 0 p f := by
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, -, hqs, hlie⟩ := exists_psi_E7_E8 (p := p) (f := f) ⟨hp, hf, rfl⟩ hK
  set U := ⨆ k, rankOne (e8Datum K).rootGroup (e8E7Node k) with hU
  let e : U ≃* subsystemGroup .E8 K e8LeviE7 :=
    (U.equivMapOfInjective _ (adjointGroup .E8 K).subtype_injective).trans
      (MulEquiv.subgroupCongr (map_subtype_iSup_rankOne e8E7Node))
  exact ⟨LocalCores.isQuasisimple_of_mulEquiv e hqs,
    lieModel_of_mulEquiv (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)) hlie⟩

end CFSG.ComponentClassification.CatLeafProof
