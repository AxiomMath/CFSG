module

public import CFSG.ClassicalInvolution.Sp62Rec.I1.WrModel
public import CFSG.ClassicalInvolution.Q3.AE.Bar
import CFSG.ClassicalInvolution.Q3.AE.PermElt

public section

namespace CFSG.ClassicalInvolution.Sp62Rec.I1

open Equiv CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

@[expose] def ι₀ : Fin 4 ↪ Fin 6 :=
  ⟨fun i => Fin.castLE (by norm_num) i, fun _ _ h => Fin.castLE_injective _ h⟩

theorem mem_range_ι₀ {x : Fin 6} : x ∈ Set.range ι₀ ↔ x.val < 4 := by
  constructor
  · rintro ⟨i, rfl⟩; exact i.2
  · intro h; exact ⟨⟨x.val, h⟩, Fin.ext rfl⟩

theorem embed_vec_ι₀ (a : Wr 4) (x : Fin 6) :
    (embed ι₀ a).vec x = if h : x.val < 4 then a.vec ⟨x.val, h⟩ else 0 := by
  rw [embed_vec]
  by_cases hx : x.val < 4
  · rw [dif_pos hx]
    have : x = ι₀ ⟨x.val, hx⟩ := Fin.ext rfl
    conv_lhs => rw [this]
    exact embedVec_apply ι₀ a.vec _
  · rw [dif_neg hx]
    exact embedVec_of_not_mem ι₀ _ (fun h => hx (mem_range_ι₀.mp h))

theorem embed_perm_ι₀ (a : Wr 4) (x : Fin 6) :
    (embed ι₀ a).perm x = if h : x.val < 4 then ι₀ (a.perm ⟨x.val, h⟩) else x := by
  rw [embed_perm]
  by_cases hx : x.val < 4
  · rw [dif_pos hx]
    have : x = ι₀ ⟨x.val, hx⟩ := Fin.ext rfl
    conv_lhs => rw [this]
    exact embedPerm_apply ι₀ a.perm _
  · rw [dif_neg hx]
    exact embedPerm_of_not_mem ι₀ _ (fun h => hx (mem_range_ι₀.mp h))

@[expose] def d1 : Perm (Fin 6) := swap 0 1 * swap 2 3
@[expose] def d2 : Perm (Fin 6) := swap 0 2 * swap 1 3
@[expose] def gi : Wr 6 := ⟨v6 [0, 2], d1⟩
@[expose] def gj : Wr 6 := ⟨v6 [0, 3], d2⟩
@[expose] def gis : Wr 6 := ⟨v6 [0, 3], d1⟩
@[expose] def gjs : Wr 6 := ⟨v6 [0, 1], d2⟩

theorem embed_iQ : embed ι₀ iQ = gi := by
  refine Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
  · rw [embed_vec_ι₀]; revert x; decide
  · rw [embed_perm_ι₀]; revert x; decide

theorem embed_jQ : embed ι₀ jQ = gj := by
  refine Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
  · rw [embed_vec_ι₀]; revert x; decide
  · rw [embed_perm_ι₀]; revert x; decide

theorem embed_iQStar : embed ι₀ iQStar = gis := by
  refine Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
  · rw [embed_vec_ι₀]; revert x; decide
  · rw [embed_perm_ι₀]; revert x; decide

theorem embed_jQStar : embed ι₀ jQStar = gjs := by
  refine Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
  · rw [embed_vec_ι₀]; revert x; decide
  · rw [embed_perm_ι₀]; revert x; decide

set_option maxRecDepth 100000 in
theorem mfw_std : ∀ w : Wr 6, w * gi = gi * w → w * gj = gj * w → w * gis = gis * w →
    w * gjs = gjs * w → Equiv.Perm.sign w.perm = -1 →
    (w * w) * ⟨v6 [0, 1], 1⟩ = ⟨v6 [0, 1], 1⟩ * (w * w) →
    (w * w) * ⟨v6 [0, 2], 1⟩ = ⟨v6 [0, 2], 1⟩ * (w * w) →
    (w * w) * ⟨v6 [0, 3], 1⟩ = ⟨v6 [0, 3], 1⟩ * (w * w) →
    (w * w) * ⟨v6 [0, 4], 1⟩ = ⟨v6 [0, 4], 1⟩ * (w * w) →
    (w * w) * ⟨v6 [0, 5], 1⟩ = ⟨v6 [0, 5], 1⟩ * (w * w) →
    (w * w) * ⟨0, swap 0 1 * swap 1 2⟩ = ⟨0, swap 0 1 * swap 1 2⟩ * (w * w) →
    (w * w) * ⟨0, swap 1 2 * swap 2 3⟩ = ⟨0, swap 1 2 * swap 2 3⟩ * (w * w) →
    (w * w) * ⟨0, swap 2 3 * swap 3 4⟩ = ⟨0, swap 2 3 * swap 3 4⟩ * (w * w) →
    (w * w) * ⟨0, swap 3 4 * swap 4 5⟩ = ⟨0, swap 3 4 * swap 4 5⟩ * (w * w) →
    w * w = 1 ∧ wsum w = 0 := by
  decide +kernel

theorem exists_perm_extend (ι : Fin 4 ↪ Fin 6) : ∃ π : Perm (Fin 6), ∀ i, π (ι₀ i) = ι i := by
  classical
  let e : ↥(Set.range ι₀) ≃ ↥(Set.range ι) := ι₀.toEquivRange.symm.trans ι.toEquivRange
  refine ⟨Equiv.extendSubtype (p := fun x => x ∈ Set.range ι₀) (q := fun x => x ∈ Set.range ι) e,
    fun i => ?_⟩
  have hmem : ι₀ i ∈ Set.range ι₀ := Set.mem_range_self i
  rw [Equiv.extendSubtype_apply_of_mem _ _ hmem]
  have h1 : (⟨ι₀ i, hmem⟩ : ↥(Set.range ι₀)) = ι₀.toEquivRange i := rfl
  rw [h1]
  simp [e]

theorem ofPerm_conj_embed_move {ι : Fin 4 ↪ Fin 6} {π : Perm (Fin 6)} (hπ : ∀ i, π (ι₀ i) = ι i)
    (a : Wr 4) : ofPerm π * embed ι₀ a * (ofPerm π)⁻¹ = embed ι a := by
  classical
  have hπs : ∀ i, π.symm (ι i) = ι₀ i := fun i => (Equiv.symm_apply_eq _).mpr (hπ i).symm
  have hnot : ∀ x, x ∉ Set.range ι → π.symm x ∉ Set.range ι₀ := by
    rintro x hx ⟨j, hj⟩
    exact hx ⟨j, by rw [← hπ j, hj]; simp⟩
  refine Wr.ext (funext fun x => ?_) ?_
  · rw [ofPerm_conj_vec, embed_vec, embed_vec]
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      rw [hπs, embedVec_apply, embedVec_apply]
    · rw [embedVec_of_not_mem ι _ hx, embedVec_of_not_mem ι₀ _ (hnot x hx)]
  · rw [ofPerm_conj_perm, embed_perm, embed_perm]
    refine Equiv.ext fun x => ?_
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      simp only [Perm.mul_apply, Perm.inv_def, hπs, embedPerm_apply, hπ]
    · simp only [Perm.mul_apply, Perm.inv_def]
      rw [embedPerm_of_not_mem ι _ hx, embedPerm_of_not_mem ι₀ _ (hnot x hx)]
      simp

theorem wsum_ofPerm (π : Perm (Fin 6)) : wsum (ofPerm π) = 0 := by
  unfold wsum ofPerm; simp

theorem conj_ofPerm_mem_aeSub {t : Wr 6} (ht : t ∈ aeSub 6) (π : Perm (Fin 6)) :
    ofPerm π * t * (ofPerm π)⁻¹ ∈ aeSub 6 := by
  refine ⟨?_, ?_⟩
  · simp only [wsum_mul, wsum_inv, wsum_ofPerm, zero_add, add_zero, ht.1]
  · have := ht.2
    simp only [mul_perm, inv_perm, map_mul, map_inv]
    show Perm.sign (ofPerm π).perm * Perm.sign t.perm * (Perm.sign (ofPerm π).perm)⁻¹ = 1
    rw [this, mul_one]; exact mul_inv_cancel _

theorem eq_of_centralizes_twins {β : Finset (Fin 6)} (hβ : β.card = 4) {w : Wr 6}
    (h1 : ∀ x ∈ memAt β hβ true, w * x = x * w) (h2 : ∀ x ∈ memAt β hβ false, w * x = x * w)
    (hodd : Perm.sign w.perm = -1) (hsq : ∀ x ∈ aeSub 6, (w * w) * x = x * (w * w)) :
    w * w = 1 ∧ wsum w = 0 := by
  obtain ⟨π, hπ⟩ := exists_perm_extend (emb β hβ)
  set P : Wr 6 := ofPerm π with hP
  set w' : Wr 6 := P⁻¹ * w * P with hw'
  have hconj : ∀ a : Wr 4, P * embed ι₀ a * P⁻¹ = embed (emb β hβ) a :=
    fun a => ofPerm_conj_embed_move hπ a
  have back : ∀ e : Wr 6, w * (P * e * P⁻¹) = (P * e * P⁻¹) * w → w' * e = e * w' := by
    intro e h
    have h' := congrArg (fun y => P⁻¹ * y * P) h
    calc w' * e = P⁻¹ * (w * (P * e * P⁻¹)) * P := by simp only [hw']; group
      _ = P⁻¹ * ((P * e * P⁻¹) * w) * P := h'
      _ = e * w' := by simp only [hw']; group
  have hgen : ∀ (a : Wr 4), (a ∈ kList → w' * embed ι₀ a = embed ι₀ a * w') ∧
      (a ∈ kStarList → w' * embed ι₀ a = embed ι₀ a * w') := by
    intro a
    constructor
    · intro ha
      apply back
      rw [hconj]
      exact h1 _ ⟨a, ha, rfl⟩
    · intro ha
      apply back
      rw [hconj]
      exact h2 _ ⟨a, ha, rfl⟩
  have e1 : w' * gi = gi * w' := by
    rw [← embed_iQ]; exact (hgen iQ).1 (by decide)
  have e2 : w' * gj = gj * w' := by
    rw [← embed_jQ]; exact (hgen jQ).1 (by decide)
  have e3 : w' * gis = gis * w' := by
    rw [← embed_iQStar]; exact (hgen iQStar).2 (by decide)
  have e4 : w' * gjs = gjs * w' := by
    rw [← embed_jQStar]; exact (hgen jQStar).2 (by decide)
  have hsign : Perm.sign w'.perm = -1 := by
    rw [← hodd]
    simp only [hw', mul_perm, inv_perm, map_mul, map_inv]
    generalize Perm.sign P.perm = a
    generalize Perm.sign w.perm = b
    rw [mul_comm (a⁻¹ * b) a, mul_inv_cancel_left]
  have hsq' : ∀ t ∈ aeSub 6, (w' * w') * t = t * (w' * w') := by
    intro t ht
    have h := hsq _ (conj_ofPerm_mem_aeSub ht π)
    have h' := congrArg (fun y => P⁻¹ * y * P) h
    calc (w' * w') * t = P⁻¹ * ((w * w) * (P * t * P⁻¹)) * P := by simp only [hw']; group
      _ = P⁻¹ * ((P * t * P⁻¹) * (w * w)) * P := h'
      _ = t * (w' * w') := by simp only [hw']; group
  obtain ⟨hsq1, hws⟩ := mfw_std w' e1 e2 e3 e4 hsign
    (hsq' _ (mem_aeSub.2 ⟨by decide, by decide⟩)) (hsq' _ (mem_aeSub.2 ⟨by decide, by decide⟩))
    (hsq' _ (mem_aeSub.2 ⟨by decide, by decide⟩)) (hsq' _ (mem_aeSub.2 ⟨by decide, by decide⟩))
    (hsq' _ (mem_aeSub.2 ⟨by decide, by decide⟩)) (hsq' _ (mem_aeSub.2 ⟨by decide, by decide⟩))
    (hsq' _ (mem_aeSub.2 ⟨by decide, by decide⟩)) (hsq' _ (mem_aeSub.2 ⟨by decide, by decide⟩))
    (hsq' _ (mem_aeSub.2 ⟨by decide, by decide⟩))
  refine ⟨?_, ?_⟩
  · have : w * w = P * (w' * w') * P⁻¹ := by simp only [hw']; group
    rw [this, hsq1]; group
  · have : wsum w' = wsum w := by
      simp only [hw', wsum_mul, wsum_inv, hP, wsum_ofPerm, zero_add, add_zero]
    rw [← this]; exact hws

end CFSG.ClassicalInvolution.Sp62Rec.I1
