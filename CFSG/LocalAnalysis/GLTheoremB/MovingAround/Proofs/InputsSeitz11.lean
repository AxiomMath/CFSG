module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz10b

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz11

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal

set_option linter.unusedSectionVars false

section RotMinus

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.OmMinus (IsRotPair)
open CFSG.LieType.Universal.Spin (quadMinus quadMinus_apply polar_quadMinus)

variable {K : Type} [Field K] [CharP K 2]

theorem exists_five_rotPairs_quadMinus_gen_orthOut {n : ℕ} (hn : 5 ≤ n) {b c : K} (hb : b ≠ 0) {α : K}
    (hα : α ^ 2 + α + c / b ^ 2 = 1) :
    ∃ (c' : Fin 5 → K) (u v : Fin 5 → Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K),
      (∀ i, IsRotPair (quadMinus n K b c) (c' i) (u i) (v i)) ∧
      ∀ i j, i ≠ j → polar (quadMinus n K b c) (u i) (u j) = 0 ∧
        polar (quadMinus n K b c) (u i) (v j) = 0 ∧ polar (quadMinus n K b c) (v i) (u j) = 0 ∧
        polar (quadMinus n K b c) (v i) (v j) = 0 := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hQ := InputsSeitz10.quadMinus_hyp_orthEight (K := K) (n := n) b c
  have hP := InputsSeitz10.polar_quadMinus_hyp_orthEight (K := K) (n := n) b c
  let a : ℕ → Fin (n - 1) := fun k => ⟨k % 4, by omega⟩
  have ha : ∀ k l, k < 4 → l < 4 → (a k = a l ↔ k = l) := by
    intro k l hk hl
    simp only [a, Fin.mk.injEq]
    rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hl]
  obtain ⟨p1, p2, o1, o2, o3, o4⟩ := InputsSeitz10.rotPairs_block_orthEight (fun f g => Sum.elim f (Sum.elim g 0)) hQ hP
    (a := a 0) (b := a 1) (by rw [Ne, ha 0 1 (by norm_num) (by norm_num)]; norm_num)
  obtain ⟨p3, p4, o5, o6, o7, o8⟩ := InputsSeitz10.rotPairs_block_orthEight (fun f g => Sum.elim f (Sum.elim g 0)) hQ hP
    (a := a 2) (b := a 3) (by rw [Ne, ha 2 3 (by norm_num) (by norm_num)]; norm_num)
  obtain ⟨s, hs⟩ : ∃ s : ℕ → Fin (n - 1) → K, ∀ k, s k = Pi.single (a k) 1 := ⟨_, fun _ => rfl⟩
  rw [← hs 0, ← hs 1] at p1 p2 o1 o2 o3 o4
  rw [← hs 2, ← hs 3] at p3 p4 o5 o6 o7 o8
  have hss : ∀ k l, k < 4 → l < 4 → ∑ i, s k i * s l i = if k = l then (1 : K) else 0 := by
    intro k l hk hl
    rw [hs k, hs l, InputsSeitz10.sum_single_mul_single_orthEight]
    by_cases hkl : k = l
    · rw [if_pos ((ha k l hk hl).2 hkl), if_pos hkl]
    · rw [if_neg (fun h => hkl ((ha k l hk hl).1 h)), if_neg hkl]
  obtain ⟨z₁, hz₁⟩ : ∃ z : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K,
      z = Sum.elim (0 : Fin (n - 1) → K) (Sum.elim (0 : Fin (n - 1) → K) ![(1 : K), 0]) := ⟨_, rfl⟩
  obtain ⟨z₂, hz₂⟩ : ∃ z : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K,
      z = Sum.elim (0 : Fin (n - 1) → K) (Sum.elim (0 : Fin (n - 1) → K) ![α, b⁻¹]) := ⟨_, rfl⟩
  have p5 : IsRotPair (quadMinus n K b c) 1 z₁ z₂ := by
    refine ⟨one_ne_zero, ?_, ?_, ?_⟩
    · rw [hz₁, InputsSeitz10.quadMinus_aniso_orthEight]
      simp
    · rw [hz₂, InputsSeitz10.quadMinus_aniso_orthEight]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← hα]
      field_simp
    · rw [hz₁, hz₂, InputsSeitz10.polar_quadMinus_aniso_orthEight, CharTwo.neg_eq]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mul_zero, add_zero, one_mul,
        zero_mul, mul_inv_cancel₀ hb]
      linear_combination α * h2
  have hza : ∀ f g : Fin (n - 1) → K, ∀ z ∈ ({z₁, z₂} : Set _),
      polar (quadMinus n K b c) (Sum.elim f (Sum.elim g 0)) z = 0 ∧
        polar (quadMinus n K b c) z (Sum.elim f (Sum.elim g 0)) = 0 := by
    intro f g z hz
    rcases hz with rfl | rfl
    · rw [polar_comm (quadMinus n K b c) _ (Sum.elim f (Sum.elim g 0)), hz₁]
      exact ⟨InputsSeitz10.polar_quadMinus_hyp_aniso_orthEight b c f g _,
        InputsSeitz10.polar_quadMinus_hyp_aniso_orthEight b c f g _⟩
    · rw [polar_comm (quadMinus n K b c) _ (Sum.elim f (Sum.elim g 0)), hz₂]
      exact ⟨InputsSeitz10.polar_quadMinus_hyp_aniso_orthEight b c f g _,
        InputsSeitz10.polar_quadMinus_hyp_aniso_orthEight b c f g _⟩
  have hz₁a := fun f g => hza f g z₁ (Or.inl rfl)
  have hz₂a := fun f g => hza f g z₂ (Or.inr rfl)
  let u : Fin 5 → Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K :=
    ![Sum.elim (s 0) (Sum.elim (s 0) 0), Sum.elim (s 0 + s 1) (Sum.elim (s 0) 0),
      Sum.elim (s 2) (Sum.elim (s 2) 0), Sum.elim (s 2 + s 3) (Sum.elim (s 2) 0), z₁]
  let v : Fin 5 → Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K :=
    ![Sum.elim (s 0 + s 1) (Sum.elim (s 1) 0), Sum.elim (s 0) (Sum.elim (s 0 + s 1) 0),
      Sum.elim (s 2 + s 3) (Sum.elim (s 3) 0), Sum.elim (s 2) (Sum.elim (s 2 + s 3) 0), z₂]
  refine ⟨fun _ => 1, u, v, fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i
    · exact p1
    · exact p2
    · exact p3
    · exact p4
    · exact p5
  · have key : ∀ f g f' g' : Fin (n - 1) → K,
        polar (quadMinus n K b c) (Sum.elim f (Sum.elim g 0)) (Sum.elim f' (Sum.elim g' 0)) =
          ∑ i, f i * g' i + ∑ i, f' i * g i := fun f g f' g' => by
      rw [hP, Finset.sum_add_distrib]
    fin_cases i <;> fin_cases j <;> (try exact absurd rfl hij) <;>
      simp [u, v, key, hss, add_mul, mul_add, Finset.sum_add_distrib, (hz₁a _ _).1, (hz₁a _ _).2,
        (hz₂a _ _).1, (hz₂a _ _).2] <;> linear_combination h2

end RotMinus

section SubfieldFive

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.OmMinus (IsRotPair)
open CFSG.LieType.Universal.Spin (quadPlus quadMinus coe_quadPlus coe_quadMinus
  nondegenerate_polarBilin_quadPlus nondegenerate_polarBilin_quadMinus_of_finite)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance (statedProjectiveReindexEquiv)

variable {k : Type} [Field k] [Finite k] [CharP k 2]

theorem eq_one_of_ne_zero_of_card_two_orthOut (hk : Nat.card k = 2) {x : k} (hx : x ≠ 0) : x = 1 := by
  classical
  haveI := Fintype.ofFinite k
  have h := FiniteField.pow_card_sub_one_eq_one x hx
  rwa [← Nat.card_eq_fintype_card, hk, show 2 - 1 = 1 from rfl, pow_one] at h

theorem tail_facts_of_card_two_orthOut (hk : Nat.card k = 2) {b c : k} (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    b ≠ 0 ∧ (0 : k) ^ 2 + 0 + c / b ^ 2 = 1 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hc0 : c ≠ 0 := fun h => hirr 0 (by rw [h]; ring)
  have hc1 : c = 1 := eq_one_of_ne_zero_of_card_two_orthOut hk hc0
  have hb0 : b ≠ 0 := fun h => hirr 1 (by rw [h, hc1]; linear_combination h2)
  have hb1 : b = 1 := eq_one_of_ne_zero_of_card_two_orthOut hk hb0
  refine ⟨hb0, ?_⟩
  rw [hb1, hc1]
  ring

theorem quadMinus_first_ne_zero_orthOut {n : ℕ} (hn : 2 ≤ n) (b c : k) :
    quadMinus n k b c (Sum.elim (Pi.single (⟨0, by omega⟩ : Fin (n - 1)) (1 : k))
      (Sum.elim (Pi.single (⟨0, by omega⟩ : Fin (n - 1)) (1 : k)) 0)) ≠ 0 := by
  rw [InputsSeitz10.quadMinus_hyp_orthEight, InputsSeitz10.sum_single_mul_single_orthEight, if_pos rfl]
  exact one_ne_zero

theorem quadPlus_first_ne_zero_orthOut {n : ℕ} (hn : 1 ≤ n) :
    quadPlus n k (Sum.elim (Pi.single (⟨0, by omega⟩ : Fin n) (1 : k))
      (Pi.single (⟨0, by omega⟩ : Fin n) (1 : k))) ≠ 0 := by
  rw [InputsSeitz10.quadPlus_elim_orthEight, InputsSeitz10.sum_single_mul_single_orthEight, if_pos rfl]
  exact one_ne_zero

noncomputable def matrixMinusEquivElementary_orthOut {n : ℕ} (hn : 2 ≤ n) (hn1 : 1 ≤ n) (b c : k)
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    matrixProjectiveDerived (coordinateQuadMinus n k hn1 b c) ≃* ↥(elementaryGroup (quadMinus n k b c)) :=
  (statedProjectiveReindexEquiv (minusIndexEquiv n hn1) (quadMinus n k b c) (coe_quadMinus n k b c)).symm.trans
    ((statedProjEquiv (coe_quadMinus n k b c) (commutator_orthogonalGroup_quadMinus_of_two_le hn hirr)).trans
      ((QuotientGroup.quotientMulEquivOfEq
        (InputsSeitz10.subgroupOf_scalars_eq_bot_orthEight (quadMinus_first_ne_zero_orthOut hn b c))).trans
        QuotientGroup.quotientBot))

noncomputable def matrixPlusEquivElementary_orthOut {n : ℕ} (hn : 3 ≤ n) :
    matrixProjectiveDerived (coordinateQuadPlus n k) ≃* ↥(elementaryGroup (quadPlus n k)) :=
  (statedProjectiveReindexEquiv (plusIndexEquiv n) (quadPlus n k) (coe_quadPlus n k)).symm.trans
    ((statedProjEquiv (coe_quadPlus n k) (commutator_orthogonalGroup_quadPlus hn)).trans
      ((QuotientGroup.quotientMulEquivOfEq
        (InputsSeitz10.subgroupOf_scalars_eq_bot_orthEight (quadPlus_first_ne_zero_orthOut (by omega)))).trans
        QuotientGroup.quotientBot))

theorem exists_elemAbelian_of_equiv_elementary_orthOut {V : Type} [AddCommGroup V] [Module k V] {Q : QuadraticForm k V}
    {S : Type} [Group S] (φ : S ≃* ↥(elementaryGroup Q))
    (h5 : ∃ A : Subgroup (V ≃ₗ[k] V), A ≤ elementaryGroup Q ∧ IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 5) :
    ∃ E : Subgroup S, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 := by
  obtain ⟨A, hAE, hAel, hAc⟩ := h5
  refine ⟨(A.subgroupOf (elementaryGroup Q)).map φ.symm.toMonoidHom,
    CFSG.SectionRank.isElemAbelian_map (CFSG.Open.IsElemAbelian.subgroupOf hAel _) _, ?_⟩
  rw [Subgroup.card_map_of_injective φ.symm.injective, ← hAc]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAE).toEquiv

theorem exists_elemAbelian_five_matrixMinus_two (hk : Nat.card k = 2) {n : ℕ} (hn : 5 ≤ n) (hn1 : 1 ≤ n)
    (b c : k) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    ∃ E : Subgroup (matrixProjectiveDerived (coordinateQuadMinus n k hn1 b c)),
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 := by
  have hFin : ∀ {m : ℕ} (i j : ℕ) (hi : i < m) (hj : j < m), i ≠ j → (⟨i, hi⟩ : Fin m) ≠ ⟨j, hj⟩ :=
    fun i j _ _ hij h => hij (congrArg Fin.val h)
  refine exists_elemAbelian_of_equiv_elementary_orthOut (matrixMinusEquivElementary_orthOut (by omega) hn1 b c hirr) ?_
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite n k hirr
  obtain ⟨hb, hα⟩ := tail_facts_of_card_two_orthOut hk hirr
  obtain ⟨c', u, v, hp, ho⟩ := exists_five_rotPairs_quadMinus_gen_orthOut hn hb hα
  have hT := exists_totallySingular_of_hypPairs
    (minusPair_orth (K := k) (b := b) (c := c) (hFin (m := n - 1) 0 1 (by omega) (by omega) (by norm_num)))
    (minusPair_orth (K := k) (b := b) (c := c) (hFin (m := n - 1) 0 2 (by omega) (by omega) (by norm_num)))
    (minusPair_orth (K := k) (b := b) (c := c) (hFin (m := n - 1) 1 2 (by omega) (by omega) (by norm_num)))
  exact InputsSeitz10.exists_elemAbelian_five_orthEight hQ hT
    (commutator_orthogonalGroup_quadMinus_of_two_le (by omega) hirr) hp ho

theorem exists_elemAbelian_five_matrixPlus_two {n : ℕ} (hn : 6 ≤ n) :
    ∃ E : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n k)),
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 := by
  have hFin : ∀ {m : ℕ} (i j : ℕ) (hi : i < m) (hj : j < m), i ≠ j → (⟨i, hi⟩ : Fin m) ≠ ⟨j, hj⟩ :=
    fun i j _ _ hij h => hij (congrArg Fin.val h)
  refine exists_elemAbelian_of_equiv_elementary_orthOut (matrixPlusEquivElementary_orthOut (k := k) (by omega)) ?_
  have hQ := nondegenerate_polarBilin_quadPlus n k
  obtain ⟨c', u, v, hp, ho⟩ := InputsSeitz10.exists_five_rotPairs_quadPlus_orthEight (K := k) hn
  have hT := exists_totallySingular_of_hypPairs
    (plusPair_orth (K := k) (hFin (m := n) 0 1 (by omega) (by omega) (by norm_num)))
    (plusPair_orth (K := k) (hFin (m := n) 0 2 (by omega) (by omega) (by norm_num)))
    (plusPair_orth (K := k) (hFin (m := n) 1 2 (by omega) (by omega) (by norm_num)))
  exact InputsSeitz10.exists_elemAbelian_five_orthEight hQ hT (commutator_orthogonalGroup_quadPlus (by omega)) hp ho

end SubfieldFive

section Descent

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.PartOne.KCOrthogonalDescent
  CFSG.RankThree.Classical.SteinbergBY
open CFSG.RankThree.PartOne.CTP (IsOuterOfOrder)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem fixed_of_transport_orthOut {G P P' : Type*} [Group G] [Group P] [Group P'] (ψ : G ≃* P) (Θ : P ≃* P')
    {α : MulAut G} {a : MulAut P} {δ : MulAut P'} (ha : MulAut.congr ψ α = a)
    (hΘ : ∀ x, Θ (a x) = δ (Θ x)) {F : Subgroup P'} (hF : ∀ t ∈ F, δ t = t) :
    ∀ x ∈ (F.map Θ.symm.toMonoidHom).map ψ.symm.toMonoidHom, α x = x := by
  rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  have h1 : a (Θ.symm t) = Θ.symm t := by
    apply Θ.injective
    rw [hΘ, MulEquiv.apply_symm_apply, hF t ht]
  have h2 : α (ψ.symm (Θ.symm t)) = ψ.symm (MulAut.congr ψ α (Θ.symm t)) := by
    simp [MulAut.congr_apply]
  simp only [MulEquiv.coe_toMonoidHom]
  rw [h2, ha, h1]

theorem card_transport_orthOut {G P P' Q₀ : Type*} [Group G] [Group P] [Group P'] [Group Q₀] (ψ : G ≃* P)
    (Θ : P ≃* P') {ι : Q₀ →* P'} (hι : Function.Injective ι) {E₀ : Subgroup Q₀} (hE₀ : IsElemAbelian 3 E₀) :
    IsElemAbelian 3 (((E₀.map ι).map Θ.symm.toMonoidHom).map ψ.symm.toMonoidHom) ∧
      Nat.card (((E₀.map ι).map Θ.symm.toMonoidHom).map ψ.symm.toMonoidHom) = Nat.card E₀ := by
  refine ⟨CFSG.SectionRank.isElemAbelian_map (CFSG.SectionRank.isElemAbelian_map
    (CFSG.SectionRank.isElemAbelian_map hE₀ _) _) _, ?_⟩
  rw [Subgroup.card_map_of_injective ψ.symm.injective, Subgroup.card_map_of_injective Θ.symm.injective,
    Subgroup.card_map_of_injective hι]

theorem exists_fixed_five_of_outer_minus_orthOut {G : Type} [Group G] {n : ℕ} (hn : 5 ≤ n)
    (hM : StatedClassicalModel G .POmegaMinus n 2 3) {α : MulAut G} (hα : IsOuterOfOrder 3 α) :
    ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 ∧ ∀ x ∈ E, α x = x := by
  classical
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hn1 : 1 ≤ n := by omega
  obtain ⟨-, K, _, _, hK, b₁, c₁, hirr₁, ⟨e₁⟩⟩ := id hM
  have hg : OrthogonalGates (coordinateQuadMinus n K hn1 b₁ c₁) 3 :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
      (Or.inr (Or.inr rfl)) n 2 3 hM hn1 K hK b₁ c₁ hirr₁ e₁
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n (by omega)
    b₁ c₁ hirr₁
  set ψ₁ := coordinateMinusWitnessEquiv K hn1 b₁ c₁ e₁ with hψ₁
  have ha := CFSG.LieType.SeitzGeneration.isOuterOfOrder_congr ψ₁ hα
  obtain ⟨haE, haD⟩ := CFSG.LieType.SeitzGeneration.outer_mem_E_not_D_of_top hg htop hp hp2 ha
  have hdesc := CFSG.HardMathSupport.Lang.Proving.orthogonal_prime_semilinear_actual_fixed_form_descent' G
    .POmegaMinus (Or.inr (Or.inr rfl)) n 2 3 3 hM hp hp2 hn1 K hK b₁ c₁ hirr₁ e₁ _ haE haD ha.1
  obtain ⟨g, hg'⟩ := haE
  obtain ⟨-, hrest⟩ := hdesc
  obtain ⟨-, hcard, V, cc, Q₀, hVκ, hVr, -, hDisp⟩ := hrest g.val.right ⟨g, hg', rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, -, -, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  set σ := V.val.right with hσ
  have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have hk2 : Nat.card (semilinearFixedSubfield σ) = 2 := by
    rw [hVr, hcard]
    norm_num
  haveI : Finite (semilinearFixedSubfield σ) := Subtype.finite
  haveI : CharP (semilinearFixedSubfield σ) 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) (by rw [hk2]; norm_num : Nat.card (semilinearFixedSubfield σ) = 2 ^ 1)
  have hext := coordinateQuadMinus_isExtension (semilinearFixedSubfield σ) n hn1 b' c'
  have hQσ := coordinateQuadMinus_fieldAut (semilinearFixedSubfield σ) n hn1 hσk b' c'
  have hg'eq : g' = fieldPair (coordinateQuadMinus n K hn1 (b' : K) (c' : K)) σ hQσ :=
    Subtype.ext (SemidirectProduct.ext hg'l hg'r)
  obtain ⟨E₀, hE₀el, hE₀c⟩ := exists_elemAbelian_five_matrixMinus_two hk2 hn hn1 b' c' hirr'
  obtain ⟨hEel, hEc⟩ := card_transport_orthOut ψ₁ Θ (incl_injective _ hext (by omega)) hE₀el
  refine ⟨_, hEel, hEc.trans hE₀c, fixed_of_transport_orthOut ψ₁ Θ hVκ.symm (fun x => hΘ x) ?_⟩
  rintro _ ⟨y, -, rfl⟩
  rw [hg'eq]
  exact fieldAutT_fixes_J _ _ σ hQσ hext hσk ⟨y, rfl⟩

theorem exists_fixed_five_of_outer_plus_orthOut {G : Type} [Group G] {n : ℕ} (hn : 6 ≤ n)
    (hM : StatedClassicalModel G .POmegaPlus n 2 3) {α : MulAut G} (hα : IsOuterOfOrder 3 α) :
    ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 ∧ ∀ x ∈ E, α x = x := by
  classical
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨-, K, _, _, hK, ⟨e₁⟩⟩ := id hM
  have hg : OrthogonalGates (coordinateQuadPlus n K) 3 :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
      (Or.inr (Or.inl rfl)) n 2 3 hM K hK e₁
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n (by omega)
  set ψ₁ := coordinatePlusWitnessEquiv K e₁ with hψ₁
  have ha := CFSG.LieType.SeitzGeneration.isOuterOfOrder_congr ψ₁ hα
  obtain ⟨haE, haD⟩ := CFSG.LieType.SeitzGeneration.outer_mem_E_not_D_of_top hg htop hp hp2 ha
  have hdesc := CFSG.HardMathSupport.Lang.Proving.orthogonal_prime_semilinear_actual_fixed_form_descent' G
    .POmegaPlus (Or.inr (Or.inl rfl)) n 2 3 3 hM hp hp2 K hK e₁ _ haE haD ha.1
  obtain ⟨g, hg'⟩ := haE
  obtain ⟨-, hrest⟩ := hdesc
  obtain ⟨-, hcard, V, cc, Q₀, hVκ, hVr, -, hDisp⟩ := hrest g.val.right ⟨g, hg', rfl⟩
  obtain ⟨ν, S₀, -, -, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  set σ := V.val.right with hσ
  have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have hk2 : Nat.card (semilinearFixedSubfield σ) = 2 := by
    rw [hVr, hcard]
    norm_num
  haveI : Finite (semilinearFixedSubfield σ) := Subtype.finite
  haveI : CharP (semilinearFixedSubfield σ) 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) (by rw [hk2]; norm_num : Nat.card (semilinearFixedSubfield σ) = 2 ^ 1)
  have hext := coordinateQuadPlus_isExtension (semilinearFixedSubfield σ) n
  have hQσ := coordinateQuadPlus_fieldAut n σ
  have hg'eq : g' = fieldPair (coordinateQuadPlus n K) σ hQσ :=
    Subtype.ext (SemidirectProduct.ext hg'l hg'r)
  obtain ⟨E₀, hE₀el, hE₀c⟩ := exists_elemAbelian_five_matrixPlus_two (k := semilinearFixedSubfield σ) hn
  obtain ⟨hEel, hEc⟩ := card_transport_orthOut ψ₁ Θ (incl_injective _ hext (by omega)) hE₀el
  refine ⟨_, hEel, hEc.trans hE₀c, fixed_of_transport_orthOut ψ₁ Θ hVκ.symm (fun x => hΘ x) ?_⟩
  rintro _ ⟨y, -, rfl⟩
  rw [hg'eq]
  exact fieldAutT_fixes_J _ _ σ hQσ hext hσk ⟨y, rfl⟩

end Descent

section Index

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.Classical.SteinbergBY
open CFSG.ComponentClassification (OuterAutomorphisms.inner OuterAutomorphisms.inner_normal)

theorem card_le_three_mul_inf_conj_matrix_orthOut {K : Type} [Field K] [Finite K] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {f : ℕ} (hg : OrthogonalGates Q f) (htop : matrixProjectiveImage Q = ⊤)
    (A : Subgroup (MulAut (matrixProjectiveDerived Q))) (hA : IsElemAbelian 3 A) :
    Nat.card A ≤ 3 * Nat.card ↥(A ⊓
      (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)).range) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, ⟨ψ, -, hψker, -⟩, ⟨-, k₂, hk₂⟩, -⟩ := hg
  set D := (CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter.linearConjugationHom Q).range with hDdef
  set H := OuterAutomorphisms.inner (matrixProjectiveDerived Q) with hHdef
  have : H.Normal := OuterAutomorphisms.inner_normal _
  have : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have hAE : A ≤ matrixProjectiveImage Q := htop ▸ le_top
  have hADH : A ⊓ D ≤ H := by
    rintro x ⟨hxA, hxD⟩
    exact CFSG.RankThree.PartOne.KCOrthogonalNoninner.mem_of_pow_eq_one_of_relIndex_eq_two_pow
      hk₂ Nat.prime_three (by norm_num) hxD (hA.2 x hxA)
  set φ : A →* (K ≃+* K) := ψ.comp (Subgroup.inclusion hAE) with hφ
  have hφker : φ.ker = D.subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hφ, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      hψker, Subgroup.mem_subgroupOf]
    rfl
  have hφ3 : ∀ a : A, φ a ^ 3 = 1 := by
    intro a
    rw [← map_pow]
    have ha : a ^ 3 = 1 := Subtype.ext (hA.2 a a.2)
    rw [ha, map_one]
  have hrange_dvd : Nat.card φ.range ∣ 3 := by
    rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun σ => ?_
    obtain ⟨a, ha⟩ := σ.2
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← ha, hφ3, OneMemClass.coe_one]
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker] at h1
  have hAD : Nat.card ↥(A ⊓ D) = Nat.card ↥(D.subgroupOf A) := by
    rw [inf_comm, ← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective A.subtype_injective]
  have hker : Nat.card φ.ker ≤ Nat.card ↥(A ⊓ H) := by
    rw [hφker, ← hAD]
    exact Subgroup.card_le_of_le (le_inf inf_le_left hADH)
  have hr : Nat.card φ.range ≤ 3 := Nat.le_of_dvd (by norm_num) hrange_dvd
  calc Nat.card A = Nat.card φ.ker * Nat.card φ.range := h1.symm
    _ ≤ Nat.card ↥(A ⊓ H) * 3 := Nat.mul_le_mul hker hr
    _ = 3 * Nat.card ↥(A ⊓ H) := mul_comm _ _

theorem card_le_three_mul_inf_conj_of_equiv_orthOut {G P : Type*} [Group G] [Group P] [Finite (MulAut P)] (ψ : G ≃* P)
    (h : ∀ A : Subgroup (MulAut P), IsElemAbelian 3 A →
      Nat.card A ≤ 3 * Nat.card ↥(A ⊓ (MulAut.conj : P →* MulAut P).range))
    (A : Subgroup (MulAut G)) (hA : IsElemAbelian 3 A) :
    Nat.card A ≤ 3 * Nat.card ↥(A ⊓ (MulAut.conj : G →* MulAut G).range) := by
  set c := MulAut.congr ψ with hc
  have h1 := h (A.map c.toMonoidHom) (CFSG.SectionRank.isElemAbelian_map hA _)
  rw [Subgroup.card_map_of_injective c.injective] at h1
  have h2 : A.map c.toMonoidHom ⊓ (MulAut.conj : P →* MulAut P).range ≤
      (A ⊓ (MulAut.conj : G →* MulAut G).range).map c.toMonoidHom := by
    rintro x ⟨⟨a, ha, rfl⟩, ⟨t, ht⟩⟩
    refine ⟨a, ⟨ha, ψ.symm t, ?_⟩, rfl⟩
    apply c.injective
    rw [hc, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
    exact ht
  have h3 := Subgroup.card_le_of_le h2
  rw [Subgroup.card_map_of_injective c.injective] at h3
  omega

theorem card_le_three_mul_inf_conj_minus_orthOut {G : Type} [Group G] {n ℓ f : ℕ} (hn : 4 ≤ n)
    (hM : StatedClassicalModel G .POmegaMinus n ℓ f) (A : Subgroup (MulAut G)) (hA : IsElemAbelian 3 A) :
    Nat.card A ≤ 3 * Nat.card ↥(A ⊓ (MulAut.conj : G →* MulAut G).range) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨-, K, _, _, hK, b₁, c₁, hirr₁, ⟨e₁⟩⟩ := id hM
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f hM hn1 K hK b₁ c₁ hirr₁ e₁
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn b₁ c₁ hirr₁
  exact card_le_three_mul_inf_conj_of_equiv_orthOut (coordinateMinusWitnessEquiv K hn1 b₁ c₁ e₁)
    (fun A' hA' => card_le_three_mul_inf_conj_matrix_orthOut hg htop A' hA') A hA

theorem card_le_three_mul_inf_conj_plus_orthOut {G : Type} [Group G] {n ℓ f : ℕ} (hn : 5 ≤ n)
    (hM : StatedClassicalModel G .POmegaPlus n ℓ f) (A : Subgroup (MulAut G)) (hA : IsElemAbelian 3 A) :
    Nat.card A ≤ 3 * Nat.card ↥(A ⊓ (MulAut.conj : G →* MulAut G).range) := by
  obtain ⟨-, K, _, _, hK, ⟨e₁⟩⟩ := id hM
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f hM K hK e₁
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn
  exact card_le_three_mul_inf_conj_of_equiv_orthOut (coordinatePlusWitnessEquiv K e₁)
    (fun A' hA' => card_le_three_mul_inf_conj_matrix_orthOut hg htop A' hA') A hA

end Index

section InnerSub

theorem le_glbCore_of_inner_sub_orthOut {X : Type} [Group X] [Finite X] {B B₁ : Subgroup X}
    (hB₁B : B₁ ≤ B) (hB₁ : IsElemAbelian 3 B₁) {K : Subgroup X} (hZ : Subgroup.center ↥K = ⊥)
    (hperf : commutator ↥K = ⊤) (hBN : B₁ ≤ Subgroup.normalizer (K : Set X))
    (hC : B₁ ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    (hinn : InputsSeitz3.autIm B₁ K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range) (hB5 : 3 ^ 5 ≤ Nat.card B₁)
    {F V : Type} [Field F] [Finite F] [CharP F 2] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {Q : QuadraticForm F V} (hQ : (polarBilin Q).Nondegenerate)
    (φ : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(elementaryGroup Q)) :
    K ≤ GLBCore 3 2 B := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (V ≃ₗ[F] V) := by
    have : Finite V := Module.finite_of_finite F
    exact Finite.of_injective (fun f : V ≃ₗ[F] V => (f : V → V)) DFunLike.coe_injective
  set E := elementaryGroup Q with hEdef
  have hconj : Function.Injective (MulAut.conj : ↥K →* MulAut ↥K) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [← hZ, Subgroup.mem_center_iff]
    intro h
    have h1 := congrArg (fun ψ : MulAut ↥K => ψ h) (MonoidHom.mem_ker.1 hg)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc h * g = g * h * g⁻¹ * g := by rw [h1]
      _ = g * h := by group
  let α : ↥B₁ →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  have hαmem : ∀ b : ↥B₁, α b ∈ (MulAut.conj : ↥K →* MulAut ↥K).range := fun b =>
    hinn ⟨⟨b, hBN b.2⟩, Subgroup.mem_subgroupOf.2 b.2, rfl⟩
  let β : ↥B₁ →* ↥(MulAut.conj : ↥K →* MulAut ↥K).range := α.codRestrict _ hαmem
  let κ : ↥B₁ →* ↥K := (MonoidHom.ofInjective hconj).symm.toMonoidHom.comp β
  have hκ : ∀ b : ↥B₁, MulAut.conj (κ b) = α b := fun b => by
    have h1 : MonoidHom.ofInjective hconj (κ b) = β b := MulEquiv.apply_symm_apply _ _
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  let Yh : ↥B₁ →* ↥E := (φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))).comp κ
  have hrel : ∀ (b : ↥B₁) (k : ↥K),
      φ (QuotientGroup.mk (α b k)) = Yh b * φ (QuotientGroup.mk k) * (Yh b)⁻¹ := by
    intro b k
    rw [← hκ b, MulAut.conj_apply]
    simp only [Yh, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]
  have hαapp : ∀ (b : ↥B₁) (k : ↥K), ((α b k : ↥K) : X) = (b : X) * k * (b : X)⁻¹ := fun b k =>
    Subgroup.normalizerMonoidHom_apply_apply_coe K _ k
  have hmk : ∀ k k' : ↥K, (QuotientGroup.mk k : ↥K ⧸ Subgroup.center ↥K) = QuotientGroup.mk k' →
      k = k' := by
    intro k k' h
    have h' := QuotientGroup.eq.1 h
    rw [hZ, Subgroup.mem_bot] at h'
    exact inv_mul_eq_one.1 h'
  have hYhinj : Function.Injective Yh := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    have hcen : (b : X) ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 := hrel b ⟨k, hk⟩
      rw [hb, one_mul, inv_one, mul_one] at h1
      have h3 := congrArg Subtype.val (hmk _ _ (φ.injective h1))
      rw [hαapp] at h3
      calc k * (b : X) = (b : X) * k * (b : X)⁻¹ * b := by rw [h3]
        _ = (b : X) * k := by group
    have hbC : (b : X) ∈ B₁ ⊓ Subgroup.centralizer (K : Set X) := ⟨b.2, hcen⟩
    rw [hC, Subgroup.mem_bot] at hbC
    exact Subgroup.mem_bot.2 (Subtype.ext hbC)
  let ρ : ↥B₁ →* (V ≃ₗ[F] V) := E.subtype.comp Yh
  have hρinj : Function.Injective ρ := E.subtype_injective.comp hYhinj
  set D := ρ.range with hD
  have hDO : D ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨b, rfl⟩
    exact elementaryGroup_le_orthogonalGroup Q (Yh b).2
  have hDel : IsElemAbelian 3 D := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun g hg => ?_⟩
    · obtain ⟨_, a, rfl⟩ := x
      obtain ⟨_, b, rfl⟩ := y
      apply Subtype.ext
      show ρ a * ρ b = ρ b * ρ a
      rw [← map_mul, ← map_mul, hB₁.1.is_comm.comm a b]
    · obtain ⟨b, rfl⟩ := hg
      rw [← map_pow]
      have : b ^ 3 = 1 := Subtype.ext (hB₁.2 b b.2)
      rw [this, map_one]
  have hD5 : 3 ^ 5 ≤ Nat.card D := by
    rw [hD, ← Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv]
    exact hB5
  obtain ⟨F₀, hF₀D, hF₀c, P, hP⟩ := InputsSeitz10.exists_fix_hypPair_orthEight hQ hDO hDel hD5
  have hF₀r : F₀ ≤ ρ.range := hF₀D
  set E' : Subgroup X := (F₀.comap ρ).map B₁.subtype with hE'
  have hE'B : E' ≤ B₁ := Subgroup.map_subtype_le _
  have hE'c : Nat.card E' = Nat.card F₀ := by
    rw [hE', Subgroup.card_map_of_injective B₁.subtype_injective, ← Subgroup.card_map_of_injective hρinj,
      Subgroup.map_comap_eq_self hF₀r]
  have hE'el : IsElemAbelian 3 E' := GL83.CompFam.elem_mono hB₁ hE'B
  have hmemE' : ∀ a : ↥E', ρ (Subgroup.inclusion hE'B a) ∈ F₀ := by
    rintro ⟨_, ⟨b, hb, rfl⟩⟩
    have : Subgroup.inclusion hE'B ⟨B₁.subtype b, ⟨b, hb, rfl⟩⟩ = b := Subtype.ext rfl
    rw [this]
    exact hb
  have hgen : K ≤ GL83.CompFam.centGenI 3 E' K := by
    refine InputsSeitz10.le_centGenI_of_lift_orthEight hperf (by rw [hZ, Subgroup.card_bot]; decide) hE'el
      (hE'B.trans hBN) hQ φ (Yh.comp (Subgroup.inclusion hE'B)) (fun a k => ?_) P
      (fun a => hP _ (hmemE' a))
    exact hrel (Subgroup.inclusion hE'B a) k
  exact InputsSeitz3.le_glbCore_of_centGenI Nat.prime_three (hE'B.trans hB₁B) hE'el (hE'c.trans hF₀c).ge
    hgen

end InnerSub

section Outer

open CFSG.RankThree.PartOne.CTP (IsOuterOfOrder)
open CFSG.LieType.Universal.Spin (nondegenerate_polarBilin_quadPlus nondegenerate_polarBilin_quadMinus_of_finite)

variable {X : Type} [Group X] [Finite X]

theorem isOuterOfOrder_of_not_mem_inner_orthOut {B K : Subgroup X} (hB : IsElemAbelian 3 B) {b : X} (hbB : b ∈ B)
    (hbN : b ∈ Subgroup.normalizer (K : Set X))
    (hout : K.normalizerMonoidHom ⟨b, hbN⟩ ∉ (MulAut.conj : ↥K →* MulAut ↥K).range) :
    IsOuterOfOrder 3 (K.normalizerMonoidHom ⟨b, hbN⟩) ∧ b ∉ K := by
  have h3 : K.normalizerMonoidHom ⟨b, hbN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨b, hbN⟩ : Subgroup.normalizer (K : Set X)) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hB.2 b hbB)
    rw [this, map_one]
  have h1 : K.normalizerMonoidHom ⟨b, hbN⟩ ≠ 1 := fun h => hout ⟨1, by rw [h, map_one]⟩
  refine ⟨⟨orderOf_eq_prime h3 h1, fun g hg => hout ⟨g, hg.symm⟩⟩, fun hbK => hout ⟨⟨b, hbK⟩, ?_⟩⟩
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
  simp

theorem le_glbCore_of_outer_of_data_orthOut {B : Subgroup X} (hB : IsElemAbelian 3 B)
    (hrk : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X)) {K : Subgroup X}
    (hZ : Subgroup.center ↥K = ⊥) (hperf : commutator ↥K = ⊤)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    (hout : ¬ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range)
    (hidx : ∀ A : Subgroup (MulAut ↥K), IsElemAbelian 3 A →
      Nat.card A ≤ 3 * Nat.card ↥(A ⊓ (MulAut.conj : ↥K →* MulAut ↥K).range))
    (hfix : ∀ α : MulAut ↥K, IsOuterOfOrder 3 α →
      ∃ E : Subgroup ↥K, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 ∧ ∀ x ∈ E, α x = x)
    {F V : Type} [Field F] [Finite F] [CharP F 2] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {Q : QuadraticForm F V} (hQ : (polarBilin Q).Nondegenerate)
    (φ : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(elementaryGroup Q)) :
    K ≤ GLBCore 3 2 B := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  set A := InputsSeitz3.autIm B K with hAdef
  have hAel : IsElemAbelian 3 A := InputsSeitz3.isElemAbelian_autIm hB K
  have hAc : Nat.card A = 3 ^ CFSG.Open.pRank 3 B :=
    (InputsSeitz3.card_autIm hBN hC).trans (GL83.PiGen.card_eq_pow_pRank hB)
  set I := (MulAut.conj : ↥K →* MulAut ↥K).range with hIdef
  obtain ⟨x, hxA, hxI⟩ := SetLike.not_le_iff_exists.1 hout
  obtain ⟨n, hn, rfl⟩ := hxA
  have hnB : (n : X) ∈ B := Subgroup.mem_subgroupOf.1 hn
  obtain ⟨hαo, hbK⟩ := isOuterOfOrder_of_not_mem_inner_orthOut hB hnB n.2 hxI
  set b : X := (n : X) with hbdef
  obtain ⟨E, hEel, hEc, hEfix⟩ := hfix _ hαo
  have hb3 : b ^ 3 = 1 := hB.2 b hnB
  have hb1 : b ≠ 1 := fun h => hbK (h ▸ K.one_mem)
  have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hZel : IsElemAbelian 3 (Subgroup.zpowers b) :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.F4InnerExAux.isElemAbelian_zpowers hb3
  have hZc : Nat.card (Subgroup.zpowers b) = 3 ^ 1 := by rw [Nat.card_zpowers, hbo, pow_one]
  have hEXel : IsElemAbelian 3 (E.map K.subtype) := CFSG.SectionRank.isElemAbelian_map hEel _
  have hEXc : Nat.card (E.map K.subtype) = 3 ^ 5 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hEc]
  have hcomm : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ E.map K.subtype, x * y = y * x := by
    rintro x hx _ ⟨y, hy, rfl⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hyb : Commute b (y : X) := by
      have h1 := congrArg Subtype.val (hEfix y hy)
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
      show b * y = y * b
      calc b * (y : X) = (b * y * b⁻¹) * b := by group
        _ = y * b := by rw [h1]
    exact (hyb.zpow_left i).eq
  have hdisj : Subgroup.zpowers b ⊓ E.map K.subtype = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers b ⊓ E.map K.subtype) ∣ 3 := by
      rw [← pow_one 3, ← hZc]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Subgroup.zpowers b ⊓ E.map K.subtype = Subgroup.zpowers b :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hZc, h3, pow_one])
      have hbE : b ∈ Subgroup.zpowers b ⊓ E.map K.subtype := by
        rw [heq]
        exact Subgroup.mem_zpowers b
      obtain ⟨y, -, hy⟩ := hbE.2
      exact hbK (hy ▸ y.2)
  have h6 : 6 ≤ CFSG.Open.pRank 3 B := by
    have h := InputsSeitz.add_le_pRank_of_commute hp hZel hEXel hcomm hdisj hZc hEXc
    rw [hrk]
    exact h
  set B₁ := InputsSeitz3.autPre B K (A ⊓ I) with hB₁def
  have hB₁B : B₁ ≤ B := InputsSeitz3.autPre_le B K _
  have hB₁el : IsElemAbelian 3 B₁ := GL83.CompFam.elem_mono hB hB₁B
  have hB₁N : B₁ ≤ Subgroup.normalizer (K : Set X) := by
    rintro _ ⟨m, -, rfl⟩
    exact m.2
  have hB₁C : B₁ ⊓ Subgroup.centralizer (K : Set X) = ⊥ :=
    le_bot_iff.1 ((inf_le_inf_right _ hB₁B).trans hC.le)
  have hB₁c : Nat.card B₁ = Nat.card ↥(A ⊓ I) := InputsSeitz3.card_autPre hC inf_le_left
  have hinn : InputsSeitz3.autIm B₁ K ≤ I := by
    rintro _ ⟨m, hm, rfl⟩
    have hm' : (m : X) ∈ InputsSeitz3.autPre B K (A ⊓ I) := Subgroup.mem_subgroupOf.1 hm
    unfold InputsSeitz3.autPre at hm'
    obtain ⟨m', hm'', hmm'⟩ := Subgroup.mem_map.1 hm'
    have hm'm : m' = m := Subtype.ext hmm'
    rw [← hm'm]
    exact ((Subgroup.mem_inf.1 hm'').2 : _).2
  have hB₁5 : 3 ^ 5 ≤ Nat.card B₁ := by
    have h1 := hidx A hAel
    rw [hAc, ← hB₁c] at h1
    set r := CFSG.Open.pRank 3 B with hr
    have h2 : 3 ^ r = 3 ^ (r - 1) * 3 := by rw [← pow_succ]; congr 1; omega
    rw [h2] at h1
    have h3 : 3 ^ (r - 1) ≤ Nat.card B₁ := by
      rw [mul_comm 3] at h1
      exact Nat.le_of_mul_le_mul_right h1 (by norm_num)
    exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans h3
  exact le_glbCore_of_inner_sub_orthOut hB₁B hB₁el hZ hperf hB₁N hB₁C hinn hB₁5 hQ φ

theorem le_glbCore_of_orthEight_outer (hcore : GLAPPrimeCore 3 X = ⊥) {B : Subgroup X} (hB : IsElemAbelian 3 B)
    (hrk : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X)) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (d : TauCeti.ValidLieTypeIndex)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) (hd : InputsSeitz10.IsOrthEightIndex d)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    (hout : ¬ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range) :
    K ≤ GLBCore 3 2 B := by
  have hZ : Subgroup.center ↥K = ⊥ := by
    by_contra hZ
    exact InputsSeitz7.cen_ne_bot_of_center_ne_bot hcore hB hrk hK hZ hBN hC
  have hperf : commutator ↥K = ⊤ := hK.2.2.1
  let eK : ↥K ≃* (TauCeti.CFSGIndex.lie d).Group := (InputsSeitz3.equivCenterQuot hZ).trans e
  obtain ⟨n, q, hqp, hqe, ⟨hn, hdq⟩ | ⟨hn, hdq⟩⟩ := hd
  · obtain ⟨d0, hv⟩ := d
    simp only at hdq
    subst hdq
    have hM : StatedClassicalModel ↥K .POmegaPlus n 2 3 := by
      have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even n q hv hqp eK
      rwa [hqp, hqe] at h
    obtain ⟨F, _, _, _, hF, ⟨φ⟩⟩ :=
      InputsSeitz10.nonempty_equiv_elementaryGroup_plus_orthEight (by omega) hv hqp hqe e
    exact le_glbCore_of_outer_of_data_orthOut hB hrk hZ hperf hBN hC hout
      (card_le_three_mul_inf_conj_plus_orthOut (by omega) hM)
      (fun α hα => exists_fixed_five_of_outer_plus_orthOut hn hM hα)
      (nondegenerate_polarBilin_quadPlus n F) φ
  · obtain ⟨d0, hv⟩ := d
    simp only at hdq
    subst hdq
    have hM : StatedClassicalModel ↥K .POmegaMinus n 2 3 := by
      have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even n q hv hqp eK
      rwa [hqp, hqe] at h
    obtain ⟨F, _, _, _, b, c, hF, hirr, ⟨φ⟩⟩ :=
      InputsSeitz10.nonempty_equiv_elementaryGroup_minus_orthEight (by omega) hv hqp hqe e
    exact le_glbCore_of_outer_of_data_orthOut hB hrk hZ hperf hBN hC hout
      (card_le_three_mul_inf_conj_minus_orthOut (by omega) hM)
      (fun α hα => exists_fixed_five_of_outer_minus_orthOut hn hM hα)
      (nondegenerate_polarBilin_quadMinus_of_finite n F hirr) φ

end Outer


end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz11

end
