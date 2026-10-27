module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofFrameRecog
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofAdjointRoots
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4FrameC3

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
open scoped MatrixGroups

@[expose] def e6Node (i : Fin 6) : Fin (Tag.rank .E6) := i

theorem e6_neighbour : ∀ i : Fin (Tag.rank .E6), ∃ l,
    Tag.cartan .E6 i l = -1 ∧ Tag.cartan .E6 l i = -1 := by
  intro i
  fin_cases i <;> decide

theorem exists_e6_chevalleyExtras
    (K : Type) [Field K] :
    ∃ (O : CommOrder (RootSystem.ofCartan (adjDatum (rootOperatorFamily .E6) K).isFiniteType
        (adjDatum (rootOperatorFamily .E6) K).divisible))
      (C : (Fin (Tag.rank .E6) → ℤ) → (Fin (Tag.rank .E6) → ℤ) → ℕ × ℕ → ℤ),
      ChevalleyExtras (adjDatum (rootOperatorFamily .E6) K) K (xPar (rootOperatorFamily .E6))
        C O := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (adjDatum (rootOperatorFamily .E6) K).isFiniteType
    (Dv := (adjDatum (rootOperatorFamily .E6) K).divisible) rfl
  exact ⟨O, _, adjDatum_chevalleyExtras _ K e6AdjData_valid noG2_E6 e6_neighbour O
    (commC (rootOperatorFamily .E6) e6AdjData_valid)
    (commutatorFormula_commC e6AdjData_valid noG2_E6 _ (adjDatum_roots _ K) O)⟩

@[expose] def e6D5Node : Fin 5 → Fin (Tag.rank .E6) :=
  ![e6Node 5, e6Node 4, e6Node 3, e6Node 2, e6Node 1]

theorem e6D5_adj : ∀ i j : Fin 5, edgeD 5 i j → e6D5Node i ≠ e6D5Node j ∧
    Tag.cartan .E6 (e6D5Node i) (e6D5Node j) = -1 ∧
    Tag.cartan .E6 (e6D5Node j) (e6D5Node i) = -1 ∧
    ∃ l : Fin 6,
      ¬ (3 : ℤ) ∣ Tag.cartan .E6 (e6D5Node i) l + 2 * Tag.cartan .E6 (e6D5Node j) l := by
  decide

theorem e6D5_nadj : ∀ i j : Fin 5, i ≠ j → ¬ edgeD 5 i j → ¬ edgeD 5 j i →
    e6D5Node i ≠ e6D5Node j ∧ Tag.cartan .E6 (e6D5Node i) (e6D5Node j) = 0 ∧
    Tag.cartan .E6 (e6D5Node j) (e6D5Node i) = 0 := by
  decide

@[expose] def e6A5Node : Fin 5 → Fin (Tag.rank .E6) :=
  ![e6Node 0, e6Node 2, e6Node 3, e6Node 4, e6Node 5]

theorem e6A5_adj : ∀ i j : Fin 5, j.val = i.val + 1 → e6A5Node i ≠ e6A5Node j ∧
    Tag.cartan .E6 (e6A5Node i) (e6A5Node j) = -1 ∧
    Tag.cartan .E6 (e6A5Node j) (e6A5Node i) = -1 ∧
    ∃ l : Fin 6,
      ¬ (3 : ℤ) ∣ Tag.cartan .E6 (e6A5Node i) l + 2 * Tag.cartan .E6 (e6A5Node j) l := by
  decide

theorem e6A5_nadj : ∀ i j : Fin 5, i ≠ j → ¬ j.val = i.val + 1 → ¬ i.val = j.val + 1 →
    e6A5Node i ≠ e6A5Node j ∧ Tag.cartan .E6 (e6A5Node i) (e6A5Node j) = 0 ∧
    Tag.cartan .E6 (e6A5Node j) (e6A5Node i) = 0 := by
  decide

theorem exists_psi_D5_E6
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    ∃ Ψ : spinGroup (Spin.quadPlus 5 K) →* adjointGroup .E6 K,
      Ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus 5 K)) ∧
      Ψ.range = ⨆ k, rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup (e6D5Node k) ∧
      IsQuasisimple ↥(⨆ k, rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup (e6D5Node k)) ∧
      Blueprint.LieModel
        (↥(⨆ k, rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup (e6D5Node k)) ⧸
          Subgroup.center
            ↥(⨆ k, rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup (e6D5Node k)))
        .POmegaPlus 5 p f := by
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have hadm : StatedLieAdmissible .POmegaPlus 5 p f := ⟨hp, hf, by norm_num⟩
  obtain ⟨O, C, hE⟩ := exists_e6_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := exists_levi_frame hE rfl e6D5Node e6D5_adj e6D5_nadj
  exact spinPlus_frame_subgroup hadm (by norm_num) hK hcomm hρ hψ

theorem exists_psi_A5_E6
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    ∃ Ψ : SL(6, K) →* adjointGroup .E6 K, Ψ.ker ≤ Subgroup.center SL(6, K) ∧
      Ψ.range = ⨆ k, rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup (e6A5Node k) ∧
      IsQuasisimple ↥(⨆ k, rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup (e6A5Node k)) ∧
      Blueprint.LieModel
        (↥(⨆ k, rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup (e6A5Node k)) ⧸
          Subgroup.center
            ↥(⨆ k, rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup (e6A5Node k)))
        .PSL 6 p f := by
  obtain ⟨hf, h3⟩ := one_le_and_three_le_of_card hp hp2 hK
  have hadm : StatedLieAdmissible .PSL 6 p f := ⟨hp, hf, by norm_num, by simp, by simp⟩
  obtain ⟨O, C, hE⟩ := exists_e6_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := exists_levi_frame hE rfl e6A5Node e6A5_adj e6A5_nadj
  exact specialLinear_frame_subgroup (m := 5) hadm (by norm_num) hK hcomm hρ hψ

@[expose] def e6LeviD5 : Set (Fin (Tag.rank .E6)) := Set.range e6D5Node

@[expose] def e6LeviA5 : Set (Fin (Tag.rank .E6)) := Set.range e6A5Node

theorem e6_levi_D5_recognition
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    IsQuasisimple ↥(subsystemGroup .E6 K e6LeviD5) ∧
      Blueprint.LieModel (↥(subsystemGroup .E6 K e6LeviD5) ⧸
        Subgroup.center ↥(subsystemGroup .E6 K e6LeviD5)) .POmegaPlus 5 p f := by
  obtain ⟨-, -, -, hqs, hlie⟩ := exists_psi_D5_E6 hp hp2 hK
  set U := ⨆ k, rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup (e6D5Node k) with hU
  let e : U ≃* subsystemGroup .E6 K e6LeviD5 :=
    (U.equivMapOfInjective _ (adjointGroup .E6 K).subtype_injective).trans
      (MulEquiv.subgroupCongr (map_subtype_iSup_rankOne e6D5Node))
  exact ⟨LocalCores.isQuasisimple_of_mulEquiv e hqs,
    lieModel_of_mulEquiv (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)) hlie⟩

theorem e6_levi_A5_recognition
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    IsQuasisimple ↥(subsystemGroup .E6 K e6LeviA5) ∧
      Blueprint.LieModel (↥(subsystemGroup .E6 K e6LeviA5) ⧸
        Subgroup.center ↥(subsystemGroup .E6 K e6LeviA5)) .PSL 6 p f := by
  obtain ⟨-, -, -, hqs, hlie⟩ := exists_psi_A5_E6 hp hp2 hK
  set U := ⨆ k, rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup (e6A5Node k) with hU
  let e : U ≃* subsystemGroup .E6 K e6LeviA5 :=
    (U.equivMapOfInjective _ (adjointGroup .E6 K).subtype_injective).trans
      (MulEquiv.subgroupCongr (map_subtype_iSup_rankOne e6A5Node))
  exact ⟨LocalCores.isQuasisimple_of_mulEquiv e hqs,
    lieModel_of_mulEquiv (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)) hlie⟩

end CFSG.ComponentClassification.CatLeafProof
