module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7Frame
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofWeylWord

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (exists_sl3Levi)
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

abbrev e7AdjointDatum
    (K : Type) [Field K] : UniversalRootDatum (adjointGroup .E7 K) :=
  adjDatum (rootOperatorFamily .E7) K

theorem e7Node_five_ne_six : e7Node 5 ≠ e7Node 6 := by decide

theorem e7Node_three_ne_four : e7Node 3 ≠ e7Node 4 := by decide

theorem e7_cartan_56 : Tag.cartan .E7 (e7Node 5) (e7Node 6) = -1 := by decide

theorem e7_cartan_65 : Tag.cartan .E7 (e7Node 6) (e7Node 5) = -1 := by decide

theorem e7_cartan_34 : Tag.cartan .E7 (e7Node 3) (e7Node 4) = -1 := by decide

theorem e7_cartan_43 : Tag.cartan .E7 (e7Node 4) (e7Node 3) = -1 := by decide

theorem e7_sl3_witness_56 : ¬ (3 : ℤ) ∣ Tag.cartan .E7 (e7Node 5) (e7Node 4) +
    2 * Tag.cartan .E7 (e7Node 6) (e7Node 4) := by
  decide

theorem e7_sl3_witness_34 : ¬ (3 : ℤ) ∣ Tag.cartan .E7 (e7Node 3) (e7Node 2) +
    2 * Tag.cartan .E7 (e7Node 4) (e7Node 2) := by
  decide

@[expose] def e7BetaRoot : Fin (Tag.rank .E7) → ℤ := ![1, 2, 2, 3, 2, 1, 0]

theorem isRoot_e7BetaRoot :
    IsRoot .E7 e7BetaRoot := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E7)]
  decide +kernel

@[expose] def e7BetaWord : List (Fin (Tag.rank .E7)) :=
  ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4] : List (Fin 7)).map e7Node

theorem wordReflect_e7BetaWord :
    wordReflect .E7 e7BetaWord (Pi.single (e7Node 5) 1) = e7BetaRoot := by
  decide

theorem e7BetaWord_orth : ∀ i ∈ e7BetaWord, i ≠ e7Node 6 ∧ Tag.cartan .E7 i (e7Node 6) = 0 ∧
    Tag.cartan .E7 (e7Node 6) i = 0 := by
  decide

@[expose] def e7A7Node : Fin 7 → Fin (Tag.rank .E7) :=
  ![e7Node 5, e7Node 6, e7Node 5, e7Node 4, e7Node 3, e7Node 2, e7Node 0]

@[expose] def e7A7Root (k : Fin 7) : Fin (Tag.rank .E7) → ℤ :=
  if k = 0 then e7BetaRoot else Pi.single (e7A7Node k) 1

theorem e7A7_adj : ∀ i j : Fin 7, j.val = i.val + 1 → i ≠ 0 → e7A7Node i ≠ e7A7Node j ∧
    Tag.cartan .E7 (e7A7Node i) (e7A7Node j) = -1 ∧
    Tag.cartan .E7 (e7A7Node j) (e7A7Node i) = -1 ∧
    ∃ l : Fin 7,
      ¬ (3 : ℤ) ∣ Tag.cartan .E7 (e7A7Node i) l + 2 * Tag.cartan .E7 (e7A7Node j) l := by
  decide

theorem e7A7_nadj : ∀ i j : Fin 7, i ≠ j → ¬ j.val = i.val + 1 → ¬ i.val = j.val + 1 →
    i ≠ 0 → j ≠ 0 → e7A7Node i ≠ e7A7Node j ∧ Tag.cartan .E7 (e7A7Node i) (e7A7Node j) = 0 ∧
      Tag.cartan .E7 (e7A7Node j) (e7A7Node i) = 0 := by
  decide

theorem e7A7_ne_one : ∀ j : Fin 7, ¬ j.val = (0 : Fin 7).val + 1 → j ≠ 1 := by decide

theorem e7A7_root_orth :
    ∀ j : Fin 7, j ≠ 0 → j ≠ 1 →
      e7BetaRoot ≠ Pi.single (e7A7Node j) 1 ∧ e7BetaRoot ≠ -Pi.single (e7A7Node j) 1 ∧
      iform e7BetaRoot (Pi.single (e7A7Node j) 1) = 0 ∧
      ¬ IsRoot .E7 (e7BetaRoot + Pi.single (e7A7Node j) 1) ∧
      ¬ IsRoot .E7 (e7BetaRoot + -Pi.single (e7A7Node j) 1) := by
  simp only [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E7)]
  decide +kernel

theorem lieModel_pairSpan_A7
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    Blueprint.LieModel (↥(pairSpan .E7 K (Set.range e7A7Root)) ⧸
      Subgroup.center ↥(pairSpan .E7 K (Set.range e7A7Root))) .PSL 8 p f := by
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have hadm : StatedLieAdmissible .PSL 8 p f := ⟨hp, hf, by norm_num, by simp, by simp⟩
  obtain ⟨O, C, hE⟩ := exists_e7_chevalleyExtras K
  choose ρF hρFi hρFr hρFv using exists_rankOne_param hE
  set n := weylWordElt .E7 K e7BetaWord with hn
  set U : Fin 7 → Subgroup (adjointGroup .E7 K) := fun k =>
    (e7AdjointDatum K).rootGroup (e7A7Root k) ⊔ (e7AdjointDatum K).rootGroup (-e7A7Root k)
      with hU_def
  let ρ : Fin 7 → SL(2, K) →* adjointGroup .E7 K := fun k =>
    if k = 0 then (MulAut.conj n).toMonoidHom.comp (ρF (e7Node 5)) else ρF (e7A7Node k)
  have hρ0 : ρ 0 = (MulAut.conj n).toMonoidHom.comp (ρF (e7Node 5)) := by simp [ρ]
  have hρk : ∀ k, k ≠ 0 → ρ k = ρF (e7A7Node k) := fun k hk => by simp [ρ, hk]
  have hU0 : U 0 =
      (e7AdjointDatum K).rootGroup e7BetaRoot ⊔ (e7AdjointDatum K).rootGroup (-e7BetaRoot) := by
    simp [hU_def, e7A7Root]
  have hUk : ∀ k, k ≠ 0 → U k = rankOne (e7AdjointDatum K).rootGroup (e7A7Node k) := fun k hk => by
    have h : e7A7Root k = Pi.single (e7A7Node k) 1 := by simp [e7A7Root, hk]
    simp only [hU_def, h]
    rfl
  have hr0 : (ρ 0).range = U 0 := by
    rw [hρ0, hU0, MonoidHom.range_comp, hρFr]
    change ((e7AdjointDatum K).rootGroup (Pi.single (e7Node 5) 1) ⊔
      (e7AdjointDatum K).rootGroup (-Pi.single (e7Node 5) 1)).map _ = _
    rw [map_conj_weylWordElt_rootPair e7BetaWord (isRoot_single _ _), wordReflect_e7BetaWord]
  have hρ' : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k := by
    intro k
    by_cases hk : k = 0
    · subst hk
      refine ⟨?_, hr0⟩
      rw [hρ0]
      exact (MulAut.conj n).injective.comp (hρFi _)
    · rw [hρk k hk, hUk k hk]
      exact ⟨hρFi _, hρFr _⟩
  have h0 : ∀ j : Fin 7, j ≠ 0 → j ≠ 1 → Commutes (U 0) (U j) := by
    intro j hj0 hj1
    rw [hU0, hUk j hj0]
    obtain ⟨h1, h2, h3, h4, h5⟩ := e7A7_root_orth j hj0 hj1
    exact commutes_rootPair_of_noG2 noG2_E7 isRoot_e7BetaRoot (isRoot_single _ _) h1 h2 h3 h4 h5
  have hcomm : ∀ i j : Fin 7, i ≠ j → ¬ j.val = i.val + 1 → ¬ i.val = j.val + 1 →
      ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u := by
    intro i j hij h1 h2 u hu v hv
    by_cases hi : i = 0
    · subst hi
      exact h0 j (fun h => hij h.symm) (e7A7_ne_one j h1) u hu v hv
    · by_cases hj : j = 0
      · subst hj
        exact (h0 i hi (e7A7_ne_one i h2) v hv u hu).symm
      · rw [hUk i hi] at hu
        rw [hUk j hj] at hv
        obtain ⟨hne, hc1, hc2⟩ := e7A7_nadj i j hij h1 h2 hi hj
        exact commutes_rankOne_of_cartan_eq_zero hE rfl hne hc1 hc2 u hu v hv
  have hψ : ∀ i j : Fin 7, j.val = i.val + 1 → ∃ ψ : SL(3, K) →* adjointGroup .E7 K,
      ψ.comp (ClassicalInvolution.WeakCT.blk K 0) = ρ i ∧
        ψ.comp (ClassicalInvolution.WeakCT.blk K 1) = ρ j := by
    intro i j hij
    have hj0 : j ≠ 0 := fun h => by subst h; simp at hij
    by_cases hi : i = 0
    · subst hi
      obtain rfl : j = 1 := Fin.ext (by simpa using hij)
      obtain ⟨emb, -, -, hv⟩ := exists_sl3Levi hE rfl (k := e7Node 4) e7Node_five_ne_six
        e7_cartan_56 e7_cartan_65 e7_sl3_witness_56
      obtain ⟨h0', h1'⟩ := sl3_comp_blk hv (hρFv (e7Node 5)) (hρFv (e7Node 6))
      refine ⟨(MulAut.conj n).toMonoidHom.comp emb, ?_, ?_⟩
      · rw [hρ0, MonoidHom.comp_assoc, h0']
      · rw [hρk 1 (by decide), MonoidHom.comp_assoc, h1']
        refine MonoidHom.ext fun A => ?_
        have hA : ρF (e7Node 6) A ∈ rankOne (e7AdjointDatum K).rootGroup (e7Node 6) := by
          rw [← hρFr]
          exact ⟨A, rfl⟩
        rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          (commute_weylWordElt hE e7BetaWord e7BetaWord_orth hA).eq, mul_inv_cancel_right]
        rfl
    · obtain ⟨hne, hc1, hc2, l, hl⟩ := e7A7_adj i j hij hi
      obtain ⟨emb, -, -, hv⟩ := exists_sl3Levi hE rfl hne hc1 hc2 hl
      rw [hρk i hi, hρk j hj0]
      exact ⟨emb, sl3_comp_blk hv (hρFv _) (hρFv _)⟩
  obtain ⟨-, -, -, -, hlie⟩ := specialLinear_frame_subgroup (m := 7) hadm (by norm_num) hK hcomm
    hρ' hψ
  refine lieModel_pairSpan_of_frame e7A7Root (fun k => ?_) hlie
  by_cases hk : k = 0
  · rw [hk, show e7A7Root 0 = e7BetaRoot by simp [e7A7Root]]
    exact isRoot_e7BetaRoot
  · rw [show e7A7Root k = Pi.single (e7A7Node k) 1 by simp [e7A7Root, hk]]
    exact isRoot_single _ _

theorem oddLieCentralQuotient_pairSpan_A7
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    OddLieCentralQuotient p (pairSpan .E7 K (Set.range e7A7Root)) := by
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have hadm : StatedLieAdmissible .PSL 8 p f := ⟨hp, hf, by norm_num, by simp, by simp⟩
  exact ⟨.PSL, 8, f, hadm, lieModel_pairSpan_A7 hp hp2 hK⟩

end CFSG.ComponentClassification.CatLeafProof
