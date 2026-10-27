module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofTwE6Kernel

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
open scoped MatrixGroups

theorem e6_adj : ∀ i j : Fin 6, edgeE 6 i j → e6Node i ≠ e6Node j ∧
    Tag.cartan .E6 (e6Node i) (e6Node j) = -1 ∧ Tag.cartan .E6 (e6Node j) (e6Node i) = -1 ∧
    ∃ l : Fin 6,
      ¬ (3 : ℤ) ∣ Tag.cartan .E6 (e6Node i) l + 2 * Tag.cartan .E6 (e6Node j) l := by
  decide

theorem e6_nadj : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i →
    e6Node i ≠ e6Node j ∧ Tag.cartan .E6 (e6Node i) (e6Node j) = 0 ∧
    Tag.cartan .E6 (e6Node j) (e6Node i) = 0 := by
  decide

theorem lieModel_pairSpan_e6Simple
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    Blueprint.LieModel (↥(pairSpan .E6 K (Set.range e6SimpleRoot)) ⧸
      Subgroup.center ↥(pairSpan .E6 K (Set.range e6SimpleRoot))) .E6 0 p f := by
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : Fact p.Prime := ⟨hp⟩
  have hadm : StatedLieAdmissible .E6 0 p f := ⟨hp, hf, rfl⟩
  obtain ⟨O, C, hE⟩ := exists_e6_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := exists_levi_frame hE rfl e6Node e6_adj e6_nadj
  obtain ⟨-, -, -, -, hlie⟩ := e6_frame_subgroup hadm hK hcomm hρ hψ
  exact lieModel_pairSpan_of_frame e6SimpleRoot (fun k => isRoot_single _ _) hlie

@[expose] def e6D5TwWord : List (Fin (Tag.rank .E6)) :=
  ([4, 5, 3, 4, 1, 3, 2, 0] : List (Fin 6)).map e6Node

theorem wordReflect_e6D5TwWord : ∀ k : Fin 5,
    CatLeafProof.wordReflect .E6 e6D5TwWord (Pi.single (e6D5Node k) 1) = e6D5TwRoot k := by
  decide

theorem lieModel_pairSpan_e6D5Tw
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    Blueprint.LieModel (↥(pairSpan .E6 K (Set.range e6D5TwRoot)) ⧸
      Subgroup.center ↥(pairSpan .E6 K (Set.range e6D5TwRoot))) .POmegaPlus 5 p f := by
  obtain ⟨-, -, -, -, hlie⟩ := exists_psi_D5_E6 hp hp2 hK
  set U := ⨆ k, rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup (e6D5Node k) with hU
  set W := ⨆ k, ((adjDatum (rootOperatorFamily .E6) K).rootGroup (e6D5TwRoot k) ⊔
    (adjDatum (rootOperatorFamily .E6) K).rootGroup (-e6D5TwRoot k)) with hW
  have hmap : U.map (MulAut.conj (weylWordElt .E6 K e6D5TwWord)).toMonoidHom = W := by
    rw [hU, hW, Subgroup.map_iSup]
    refine iSup_congr fun k => ?_
    rw [← wordReflect_e6D5TwWord k]
    exact map_conj_weylWordElt_rootPair e6D5TwWord (isRoot_single _ _)
  let e : U ≃* W :=
    (U.equivMapOfInjective _ (MulAut.conj (weylWordElt .E6 K e6D5TwWord)).injective).trans
      (MulEquiv.subgroupCongr hmap)
  refine lieModel_pairSpan_of_frame e6D5TwRoot (fun k => ?_)
    (lieModel_of_mulEquiv (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)) hlie)
  rw [← wordReflect_e6D5TwWord k]
  exact isRoot_wordReflect _ (isRoot_single _ _)

theorem lieModel_pairSpan_e6A5
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    Blueprint.LieModel (↥(pairSpan .E6 K (Set.range e6A5Root)) ⧸
      Subgroup.center ↥(pairSpan .E6 K (Set.range e6A5Root))) .PSL 6 p f := by
  obtain ⟨-, -, -, -, hlie⟩ := exists_psi_A5_E6 hp hp2 hK
  exact lieModel_pairSpan_of_frame e6A5Root (fun k => isRoot_single _ _) hlie

theorem oddLieCentralQuotient_pairSpan_hiE6
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hq : IsQuasisimple (pairSpan .E6 K {hiE6})) :
    OddLieCentralQuotient p (pairSpan .E6 K {hiE6}) := by
  obtain ⟨hf, h3⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨-, ⟨eQ⟩, -, hfin⟩ := odd_arbitrary_root_pair_SL2_p_components .E6 K hK2 isRoot_hiE6
  let e₀ : pairSpan .E6 K {hiE6} ≃*
      (rootSubgroup .E6 K hiE6 ⊔ rootSubgroup .E6 K (-hiE6) : Subgroup (ModGL .E6 K)) :=
    MulEquiv.subgroupCongr (pairSpan_singleton .E6 K hiE6)
  by_cases h5 : 5 ≤ Nat.card K
  · let e : pairSpan .E6 K {hiE6} ≃* SL2 K := e₀.trans eQ.symm
    exact oddLieCentralQuotient_of_equiv_psl_two hp hf hK (by omega) (by omega)
      (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e))
  · exfalso
    have h3' : Nat.card K = 3 := by
      have hodd : Odd (Nat.card K) := by
        rw [hK]
        exact (hp.eq_two_or_odd'.resolve_left hp2).pow
      obtain ⟨k, hk⟩ := hodd
      omega
    have := (hfin.1 h3').1
    exact LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hq
      (Group.isSolvable_of_isSolvable_injective (f := e₀.toMonoidHom) e₀.injective)

end CFSG.ComponentClassification.CatLeafProof
