module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FGraphC
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432BD4Lin

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420.BD4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three
open scoped commutatorElement

private def bd4O (j : Fin 3) : D4Idx := bd4OuterIdx j

private theorem outer_mem : ∀ j : Fin 3, bd4O j ∈ ({0, 1, 3} : Finset D4Idx) := by decide

private theorem outer_or : ∀ j : Fin 3, bd4O j = 0 ∨ bd4O j = 1 ∨ bd4O j = 3 := by decide

private theorem outer_ne_two : ∀ j : Fin 3, bd4O j ≠ 2 := by decide

private theorem outer_inj : ∀ j j' : Fin 3, bd4O j = bd4O j' → j = j' := by decide

private def bd4R3 : Fin 3 → D4Vec := ![rC 1 3, rC 0 3, rC 0 1]

private theorem r3_mem : ∀ j : Fin 3, bd4R3 j ∈ rootFinset Tag.D4 ∧ height (bd4R3 j) = 3 := by
  decide +kernel

private theorem r3_inj : ∀ j j' : Fin 3, bd4R3 j = bd4R3 j' → j = j' := by decide +kernel

private theorem roots_sum : ∀ j j' : Fin 3, rA 2 + rA (bd4O j) ∈ rootFinset Tag.D4 ∧
    (j ≠ j' → rA (bd4O j) + rB (bd4O j') ∈ rootFinset Tag.D4) ∧
    rA (bd4O j) + bd4R3 j ∈ rootFinset Tag.D4 ∧
    rB (bd4O j) + bd4R3 j ∈ rootFinset Tag.D4 := by decide +kernel

private theorem roots_ne : ∀ j j' : Fin 3, rA (bd4O j) ≠ rB (bd4O j') ∧
    rA (bd4O j) ≠ bd4R3 j' ∧ rB (bd4O j) ≠ bd4R3 j' := by decide +kernel

private theorem cover0 : ∀ γ ∈ d4RootsAt 1, ∃ i : D4Idx, γ = rA i := by decide +kernel

private theorem cover1 : ∀ γ ∈ d4RootsAt 2, ∃ j : Fin 3, γ = rB (bd4O j) := by
  decide +kernel

private theorem cover2 : ∀ γ ∈ d4RootsAt 3, ∃ j : Fin 3, γ = bd4R3 j := by decide +kernel

private theorem pairs12 : ∀ j j' : Fin 3, j ≠ j' →
    d4Pairs 1 2 (rC (bd4O j) (bd4O j')) =
      {(rA (bd4O j), rB (bd4O j')), (rA (bd4O j'), rB (bd4O j))} := by
  decide +kernel

private theorem pairs13 :
    d4Pairs 1 3 rT4 = Finset.univ.image fun j : Fin 3 => (rA (bd4O j), bd4R3 j) := by
  decide +kernel

private theorem pairs23 :
    d4Pairs 2 3 rT5 = Finset.univ.image fun j : Fin 3 => (rB (bd4O j), bd4R3 j) := by
  decide +kernel

variable {K : Type} [Field K] [Finite K]


set_option linter.unusedSectionVars false

private theorem pair11 {u u' : ModGL Tag.D4 K} (hu : u ∈ heightSeries Tag.D4 K 1)
    (hu' : u' ∈ heightSeries Tag.D4 K 1) (h1 : ⁅u, u'⁆ = 1) (j : Fin 3) :
    cc (K := K) (rA (bd4O j)) (rA 2) * pc (rA (bd4O j)) u * pc (rA 2) u' +
      cc (K := K) (rA 2) (rA (bd4O j)) * pc (rA 2) u * pc (rA (bd4O j)) u' = 0 := by
  have ho := outer_mem j
  have hne : ((rA (bd4O j), rA 2) : D4Vec × D4Vec) ≠ (rA 2, rA (bd4O j)) :=
    fun h => outer_ne_two j ((rA_inj _ _).1 (congrArg Prod.fst h))
  have e := rootCoord_pairs_two (by norm_num) (by norm_num) hu hu' (rB_pos ho)
    (by rw [(isPos_rB _ ho).2]; norm_num) (d4Pairs_11_gen _ (outer_or j)) hne
  rw [h1, rootCoord_one] at e
  exact e.symm

private theorem pair12 {u w : ModGL Tag.D4 K} (hu : u ∈ heightSeries Tag.D4 K 1)
    (hw : w ∈ heightSeries Tag.D4 K 2) (h1 : ⁅u, w⁆ = 1) {j j' : Fin 3} (hjj : j ≠ j') :
    cc (K := K) (rA (bd4O j)) (rB (bd4O j')) * pc (rA (bd4O j)) u *
        pc (rB (bd4O j')) w +
      cc (K := K) (rA (bd4O j')) (rB (bd4O j)) * pc (rA (bd4O j')) u *
        pc (rB (bd4O j)) w = 0 := by
  have hC := isPos_rC _ (outer_mem j) _ (outer_mem j') fun h => hjj (outer_inj _ _ h)
  have hne : ((rA (bd4O j), rB (bd4O j')) : D4Vec × D4Vec) ≠
      (rA (bd4O j'), rB (bd4O j)) :=
    fun h => hjj (outer_inj _ _ ((rA_inj _ _).1 (congrArg Prod.fst h)))
  have e := rootCoord_pairs_two (by norm_num) (by norm_num) hu hw
    ⟨hC.1, by rw [hC.2]; norm_num⟩ (by rw [hC.2]; norm_num) (pairs12 j j' hjj) hne
  rw [h1, rootCoord_one] at e
  exact e.symm

private theorem pair13 {u z : ModGL Tag.D4 K} (hu : u ∈ heightSeries Tag.D4 K 1)
    (hz : z ∈ heightSeries Tag.D4 K 3) (h1 : ⁅u, z⁆ = 1) :
    ∑ j, cc (K := K) (rA (bd4O j)) (bd4R3 j) * pc (rA (bd4O j)) u *
      pc (bd4R3 j) z = 0 := by
  have e := rootCoord_commutator_pairs (by norm_num) (by norm_num) hu hz
    ⟨isPos_rT4.1, by rw [isPos_rT4.2]; norm_num⟩ (by rw [isPos_rT4.2]; norm_num)
  rw [h1, rootCoord_one, pairs13,
    Finset.sum_image fun j _ j' _ h => r3_inj j j' (congrArg Prod.snd h)] at e
  exact e.symm

private theorem pair23 {w z : ModGL Tag.D4 K} (hw : w ∈ heightSeries Tag.D4 K 2)
    (hz : z ∈ heightSeries Tag.D4 K 3) (h1 : ⁅w, z⁆ = 1) :
    ∑ j, cc (K := K) (rB (bd4O j)) (bd4R3 j) * pc (rB (bd4O j)) w *
      pc (bd4R3 j) z = 0 := by
  have e := rootCoord_commutator_pairs (by norm_num) (by norm_num) hw hz
    ⟨isPos_rT5.1, by rw [isPos_rT5.2]; norm_num⟩ (by rw [isPos_rT5.2]; norm_num)
  rw [h1, rootCoord_one, pairs23,
    Finset.sum_image fun j _ j' _ h => r3_inj j j' (congrArg Prod.snd h)] at e
  exact e.symm

private def layerSet (A : Subgroup ↥(adjointGroup Tag.D4 K)) (k : ℕ) {n : ℕ}
    (R : Fin n → D4Vec) : Set (Fin n → K) :=
  {v | ∃ x ∈ A, x ∈ unitN Tag.D4 K k ∧ v = fun j => pc (R j) (x : ModGL Tag.D4 K)}

private theorem card_layer_le (A : Subgroup ↥(adjointGroup Tag.D4 K)) (k : ℕ) {n : ℕ}
    (R : Fin n → D4Vec) (hR : ∀ j, IsRoot Tag.D4 (R j) ∧ height (R j) = ((k + 1 : ℕ) : ℤ))
    (hcov : ∀ γ ∈ d4RootsAt ((k + 1 : ℕ) : ℤ), ∃ j, γ = R j) :
    Nat.card (layerImage A k) ≤ Nat.card (layerSet A k R) := by
  refine Nat.card_le_card_of_injective
    (fun q => ⟨fun j => Multiplicative.toAdd q.1 ⟨R j, hR j⟩, ?_⟩) fun q q' h => ?_
  · obtain ⟨x, hxA, hxq⟩ := q.2
    refine ⟨x.1, hxA, x.2, funext fun j => ?_⟩
    rw [← hxq]
    exact coord_unitPhi x ⟨R j, hR j⟩
  · refine Subtype.ext (Multiplicative.toAdd.injective (funext fun δ => ?_))
    obtain ⟨j, hj⟩ := hcov δ.1 (unitRoot_mem_at δ)
    obtain rfl : δ = ⟨R j, hR j⟩ := Subtype.ext hj
    exact congrFun (congrArg Subtype.val h) j

private theorem card_set_le {n : ℕ} (S : Set (Fin n → K)) : Nat.card S ≤ Nat.card K ^ n := by
  calc Nat.card S ≤ Nat.card (Fin n → K) := Finite.card_subtype_le _
    _ = Nat.card K ^ n := by rw [Nat.card_fun, Nat.card_fin]

theorem card_le_pow_seven_of_comm (A : Subgroup ↥(adjointGroup Tag.D4 K))
    (hA0 : A ≤ unitN Tag.D4 K 0) (hcomm : ∀ u ∈ A, ∀ w ∈ A, u * w = w * u) :
    Nat.card A ≤ Nat.card K ^ 7 := by
  have hd : (maxHeight Tag.D4).toNat = 5 := by rw [maxHeight_D4]; rfl
  have hbot : unitN Tag.D4 K 5 = ⊥ := by
    have := unitN_bot Tag.D4 (K := K)
    rwa [hd] at this
  have hprod := card_le_prod_of_filtration (unitN Tag.D4 K) (unitPhi Tag.D4 K) 5
    hbot (unitN_chain Tag.D4) unitPhi_eq_one_iff A hA0
    (fun k => Nat.card (layerImage A k)) (fun k _ => le_rfl)
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul] at hprod
  have hr3 : ∀ j, IsRoot Tag.D4 (bd4R3 j) ∧ 0 < height (bd4R3 j) :=
    fun j => ⟨mem_rootFinset.1 (r3_mem j).1, by rw [(r3_mem j).2]; norm_num⟩
  have h0 := card_layer_le A 0 rA (fun i => ⟨(isPos_rA i).1, (height_rA i).trans rfl⟩) cover0
  have h1 := card_layer_le A 1 (fun j => rB (bd4O j))
    (fun j => ⟨(isPos_rB _ (outer_mem j)).1, (isPos_rB _ (outer_mem j)).2.trans rfl⟩) cover1
  have h2 := card_layer_le A 2 bd4R3
    (fun j => ⟨mem_rootFinset.1 (r3_mem j).1, (r3_mem j).2.trans rfl⟩) cover2
  have h3 := (card_layer_le A 3 (fun _ : Fin 1 => rT4)
    (fun _ => ⟨isPos_rT4.1, isPos_rT4.2.trans rfl⟩) fun γ hγ => ⟨0, single4 γ hγ⟩).trans
      (card_set_le _)
  have h4 := (card_layer_le A 4 (fun _ : Fin 1 => rT5)
    (fun _ => ⟨isPos_rT5.1, isPos_rT5.2.trans rfl⟩) fun γ hγ => ⟨0, single5 γ hγ⟩).trans
      (card_set_le _)
  have h5 := card_mul_le_pow_five (S₁ := layerSet A 0 rA)
    (S₂ := layerSet A 1 fun j => rB (bd4O j)) (S₃ := layerSet A 2 bd4R3)
    (fun j => cc (rA (bd4O j)) (rA 2)) (fun j => cc (rA 2) (rA (bd4O j)))
    (fun j => cc_ne_zero (isPos_rA 2) (isPos_rA _) (rA_ne_rA (outer_ne_two j).symm)
      (mem_rootFinset.1 (roots_sum j j).1))
    (fun x hx x' hx' j => by
      obtain ⟨g, hg, -, rfl⟩ := hx
      obtain ⟨g', hg', -, rfl⟩ := hx'
      exact pair11 (mem_hs_one (hA0 hg)) (mem_hs_one (hA0 hg')) (coe_comm_eq_one hcomm hg hg') j)
    (fun j j' => cc (rA (bd4O j)) (rB (bd4O j')))
    (fun j j' => cc (rA (bd4O j')) (rB (bd4O j)))
    (fun j j' hjj => cc_ne_zero (isPos_rA _) (rB_pos (outer_mem j')) (roots_ne j j').1
      (mem_rootFinset.1 ((roots_sum j j').2.1 hjj)))
    (fun x hx w hw j j' hjj => by
      obtain ⟨g, hg, -, rfl⟩ := hx
      obtain ⟨g', hg', hg'1, rfl⟩ := hw
      exact pair12 (mem_hs_one (hA0 hg)) (mem_hs_two hg'1) (coe_comm_eq_one hcomm hg hg') hjj)
    (fun j => cc (rA (bd4O j)) (bd4R3 j))
    (fun j => cc_ne_zero (isPos_rA _) (hr3 j) (roots_ne j j).2.1
      (mem_rootFinset.1 (roots_sum j j).2.2.1))
    (fun x hx v hv => by
      obtain ⟨g, hg, -, rfl⟩ := hx
      obtain ⟨g', hg', hg'2, rfl⟩ := hv
      exact pair13 (mem_hs_one (hA0 hg)) hg'2 (coe_comm_eq_one hcomm hg hg'))
    (fun j => cc (rB (bd4O j)) (bd4R3 j))
    (fun j => cc_ne_zero (rB_pos (outer_mem j)) (hr3 j) (roots_ne j j).2.2
      (mem_rootFinset.1 (roots_sum j j).2.2.2))
    (fun w hw v hv => by
      obtain ⟨g, hg, hg1, rfl⟩ := hw
      obtain ⟨g', hg', hg'2, rfl⟩ := hv
      exact pair23 (mem_hs_two hg1) hg'2 (coe_comm_eq_one hcomm hg hg'))
  have hL : Nat.card (layerImage A 0) * Nat.card (layerImage A 1) * Nat.card (layerImage A 2) ≤
      Nat.card K ^ 5 := (Nat.mul_le_mul (Nat.mul_le_mul h0 h1) h2).trans h5
  calc Nat.card A ≤ _ := hprod
    _ ≤ Nat.card K ^ 5 * Nat.card K ^ 1 * Nat.card K ^ 1 := Nat.mul_le_mul (Nat.mul_le_mul hL h3) h4
    _ = Nat.card K ^ 7 := by ring

end CFSG.LocalAnalysis.GLTheoremA.H1420.BD4

end
