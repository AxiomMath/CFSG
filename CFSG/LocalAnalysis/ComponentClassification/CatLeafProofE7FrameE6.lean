module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7FrameA7
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6Frame

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (exists_sl3Levi)
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

@[expose] def e7GammaRoot : Fin (Tag.rank .E7) → ℤ := ![1, 1, 1, 1, 0, 0, 0]

theorem isRoot_e7GammaRoot :
    IsRoot .E7 e7GammaRoot := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E7)]
  decide +kernel

@[expose] def e7GammaWord : List (Fin (Tag.rank .E7)) :=
  ([0, 2, 1] : List (Fin 7)).map e7Node

theorem wordReflect_e7GammaWord :
    wordReflect .E7 e7GammaWord (Pi.single (e7Node 3) 1) = e7GammaRoot := by
  decide

theorem e7GammaWord_orth : ∀ i ∈ e7GammaWord, i ≠ e7Node 4 ∧ Tag.cartan .E7 i (e7Node 4) = 0 ∧
    Tag.cartan .E7 (e7Node 4) i = 0 := by
  decide

@[expose] def e7E6Node : Fin 6 → Fin (Tag.rank .E7) :=
  ![e7Node 2, e7Node 3, e7Node 3, e7Node 4, e7Node 5, e7Node 6]

@[expose] def e7E6Root (k : Fin 6) : Fin (Tag.rank .E7) → ℤ :=
  if k = 1 then e7GammaRoot else Pi.single (e7E6Node k) 1

theorem e7E6_adj : ∀ i j : Fin 6, edgeE 6 i j → i ≠ 1 → e7E6Node i ≠ e7E6Node j ∧
    Tag.cartan .E7 (e7E6Node i) (e7E6Node j) = -1 ∧
    Tag.cartan .E7 (e7E6Node j) (e7E6Node i) = -1 ∧
    ∃ l : Fin 7,
      ¬ (3 : ℤ) ∣ Tag.cartan .E7 (e7E6Node i) l + 2 * Tag.cartan .E7 (e7E6Node j) l := by
  decide

theorem e7E6_nadj : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i → i ≠ 1 → j ≠ 1 →
    e7E6Node i ≠ e7E6Node j ∧ Tag.cartan .E7 (e7E6Node i) (e7E6Node j) = 0 ∧
    Tag.cartan .E7 (e7E6Node j) (e7E6Node i) = 0 := by
  decide

theorem e7E6_edge_one : ∀ j : Fin 6, edgeE 6 1 j → j = 3 := by decide

theorem e7E6_not_edge_to_one : ∀ i : Fin 6, ¬ edgeE 6 i 1 := by decide

theorem e7E6_ne_three_of_nadj : ∀ j : Fin 6, ¬ edgeE 6 1 j → j ≠ 3 := by decide

theorem e7E6_root_orth :
    ∀ j : Fin 6, j ≠ 1 → j ≠ 3 →
      e7GammaRoot ≠ Pi.single (e7E6Node j) 1 ∧ e7GammaRoot ≠ -Pi.single (e7E6Node j) 1 ∧
      iform e7GammaRoot (Pi.single (e7E6Node j) 1) = 0 ∧
      ¬ IsRoot .E7 (e7GammaRoot + Pi.single (e7E6Node j) 1) ∧
      ¬ IsRoot .E7 (e7GammaRoot + -Pi.single (e7E6Node j) 1) := by
  simp only [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E7)]
  decide +kernel

theorem lieModel_pairSpan_E6
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    Blueprint.LieModel (↥(pairSpan .E7 K (Set.range e7E6Root)) ⧸
      Subgroup.center ↥(pairSpan .E7 K (Set.range e7E6Root))) .E6 0 p f := by
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : Fact p.Prime := ⟨hp⟩
  have hadm : StatedLieAdmissible .E6 0 p f := ⟨hp, hf, rfl⟩
  obtain ⟨O, C, hE⟩ := exists_e7_chevalleyExtras K
  choose ρF hρFi hρFr hρFv using exists_rankOne_param hE
  set n := weylWordElt .E7 K e7GammaWord with hn
  set U : Fin 6 → Subgroup (adjointGroup .E7 K) := fun k =>
    (e7AdjointDatum K).rootGroup (e7E6Root k) ⊔ (e7AdjointDatum K).rootGroup (-e7E6Root k)
      with hU_def
  let ρ : Fin 6 → SL(2, K) →* adjointGroup .E7 K := fun k =>
    if k = 1 then (MulAut.conj n).toMonoidHom.comp (ρF (e7Node 3)) else ρF (e7E6Node k)
  have hρ1 : ρ 1 = (MulAut.conj n).toMonoidHom.comp (ρF (e7Node 3)) := by simp [ρ]
  have hρk : ∀ k, k ≠ 1 → ρ k = ρF (e7E6Node k) := fun k hk => by simp [ρ, hk]
  have hU1 : U 1 =
      (e7AdjointDatum K).rootGroup e7GammaRoot ⊔ (e7AdjointDatum K).rootGroup (-e7GammaRoot) := by
    simp [hU_def, e7E6Root]
  have hUk : ∀ k, k ≠ 1 → U k = rankOne (e7AdjointDatum K).rootGroup (e7E6Node k) := fun k hk => by
    have h : e7E6Root k = Pi.single (e7E6Node k) 1 := by simp [e7E6Root, hk]
    simp only [hU_def, h]
    rfl
  have hr1 : (ρ 1).range = U 1 := by
    rw [hρ1, hU1, MonoidHom.range_comp, hρFr]
    change ((e7AdjointDatum K).rootGroup (Pi.single (e7Node 3) 1) ⊔
      (e7AdjointDatum K).rootGroup (-Pi.single (e7Node 3) 1)).map _ = _
    rw [map_conj_weylWordElt_rootPair e7GammaWord (isRoot_single _ _), wordReflect_e7GammaWord]
  have hρ' : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k := by
    intro k
    by_cases hk : k = 1
    · subst hk
      refine ⟨?_, hr1⟩
      rw [hρ1]
      exact (MulAut.conj n).injective.comp (hρFi _)
    · rw [hρk k hk, hUk k hk]
      exact ⟨hρFi _, hρFr _⟩
  have h1 : ∀ j : Fin 6, j ≠ 1 → j ≠ 3 → Commutes (U 1) (U j) := by
    intro j hj1 hj3
    rw [hU1, hUk j hj1]
    obtain ⟨h1, h2, h3, h4, h5⟩ := e7E6_root_orth j hj1 hj3
    exact commutes_rootPair_of_noG2 noG2_E7 isRoot_e7GammaRoot (isRoot_single _ _) h1 h2 h3 h4
      h5
  have hcomm : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i →
      ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u := by
    intro i j hij hij' hji u hu v hv
    by_cases hi : i = 1
    · subst hi
      exact h1 j (fun h => hij h.symm) (e7E6_ne_three_of_nadj j hij') u hu v hv
    · by_cases hj : j = 1
      · subst hj
        exact (h1 i hi (e7E6_ne_three_of_nadj i hji) v hv u hu).symm
      · rw [hUk i hi] at hu
        rw [hUk j hj] at hv
        obtain ⟨hne, hc1, hc2⟩ := e7E6_nadj i j hij hij' hji hi hj
        exact commutes_rankOne_of_cartan_eq_zero hE rfl hne hc1 hc2 u hu v hv
  have hψ : ∀ i j : Fin 6, edgeE 6 i j → ∃ ψ : SL(3, K) →* adjointGroup .E7 K,
      ψ.comp (ClassicalInvolution.WeakCT.blk K 0) = ρ i ∧
        ψ.comp (ClassicalInvolution.WeakCT.blk K 1) = ρ j := by
    intro i j hij
    have hj1 : j ≠ 1 := fun h => e7E6_not_edge_to_one i (h ▸ hij)
    by_cases hi : i = 1
    · subst hi
      obtain rfl := e7E6_edge_one j hij
      obtain ⟨emb, -, -, hv⟩ := exists_sl3Levi hE rfl (k := e7Node 2) e7Node_three_ne_four
        e7_cartan_34 e7_cartan_43 e7_sl3_witness_34
      obtain ⟨h0', h1'⟩ := sl3_comp_blk hv (hρFv (e7Node 3)) (hρFv (e7Node 4))
      refine ⟨(MulAut.conj n).toMonoidHom.comp emb, ?_, ?_⟩
      · rw [hρ1, MonoidHom.comp_assoc, h0']
      · rw [hρk 3 (by decide), MonoidHom.comp_assoc, h1']
        refine MonoidHom.ext fun A => ?_
        have hA : ρF (e7Node 4) A ∈ rankOne (e7AdjointDatum K).rootGroup (e7Node 4) := by
          rw [← hρFr]
          exact ⟨A, rfl⟩
        rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          (commute_weylWordElt hE e7GammaWord e7GammaWord_orth hA).eq, mul_inv_cancel_right]
        rfl
    · obtain ⟨hne, hc1, hc2, l, hl⟩ := e7E6_adj i j hij hi
      obtain ⟨emb, -, -, hv⟩ := exists_sl3Levi hE rfl hne hc1 hc2 hl
      rw [hρk i hi, hρk j hj1]
      exact ⟨emb, sl3_comp_blk hv (hρFv _) (hρFv _)⟩
  obtain ⟨-, -, -, -, hlie⟩ := e6_frame_subgroup hadm hK hcomm hρ' hψ
  refine lieModel_pairSpan_of_frame e7E6Root (fun k => ?_) hlie
  by_cases hk : k = 1
  · rw [hk, show e7E6Root 1 = e7GammaRoot by simp [e7E6Root]]
    exact isRoot_e7GammaRoot
  · rw [show e7E6Root k = Pi.single (e7E6Node k) 1 by simp [e7E6Root, hk]]
    exact isRoot_single _ _

theorem oddLieCentralQuotient_pairSpan_E6
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    OddLieCentralQuotient p (pairSpan .E7 K (Set.range e7E6Root)) := by
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have hadm : StatedLieAdmissible .E6 0 p f := ⟨hp, hf, rfl⟩
  exact ⟨.E6, 0, f, hadm, lieModel_pairSpan_E6 hp hp2 hK⟩

end CFSG.ComponentClassification.CatLeafProof
