module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Mem
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Three7

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8

variable {n : ℕ}

@[expose] def FourSetPrim (n : ℕ) : Prop :=
  ∀ (X : Set (Finset (Fin n))), (∀ x ∈ X, x.card = 4) → ∀ α ∈ X, (∃ β ∈ X, β ≠ α) →
    (∀ x ∈ X, ∀ y ∈ X, ∀ p : Equiv.Perm (Fin n), Equiv.Perm.sign p = 1 →
      x.map p.toEmbedding ∈ X → y.map p.toEmbedding ∈ X) →
    ∀ γ : Finset (Fin n), γ.card = 4 → γ ∈ X

@[expose] def AEBlocks' (n : ℕ) : Prop :=
  ∀ (α : Finset (Fin n)) (hα : α.card = 4) (B : Set (Subgroup (AEQ n))), IsBlock B →
    memBar α hα true ∈ B → memBar α hα false ∈ B →
    B = {memBar α hα true, memBar α hα false} ∨ (∀ M, IsMember M → M ∈ B)

theorem sum_indicator_emb (ι : Fin 4 ↪ Fin n) (a : Fin n) :
    ∑ i, (if ι i = a then (1 : ZMod 2) else 0) = if a ∈ Set.range ι then 1 else 0 := by
  classical
  by_cases ha : a ∈ Set.range ι
  · obtain ⟨j, rfl⟩ := ha
    rw [if_pos ⟨j, rfl⟩]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [if_neg]
      intro h
      exact hij (ι.injective h)
    · simp
  · rw [if_neg ha]
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro h
    exact ha ⟨i, h⟩

theorem sum_pairVec_emb (a c : Fin n) (β : Finset (Fin n)) (hβ : β.card = 4) :
    ∑ i, pairVec a c (emb β hβ i) =
      (if a ∈ β then 1 else 0) + (if c ∈ β then 1 else 0) := by
  classical
  unfold pairVec
  rw [Finset.sum_add_distrib, sum_indicator_emb, sum_indicator_emb]
  have h1 : ∀ x, x ∈ Set.range (emb β hβ) ↔ x ∈ β := fun x => by
    rw [range_emb]; exact Finset.mem_coe
  by_cases ha : a ∈ β <;> by_cases hc : c ∈ β <;> simp [h1, ha, hc]

theorem exists_twin_vec (hn7 : n ≤ 7) {α β : Finset (Fin n)} (hα : α.card = 4) (hβ : β.card = 4)
    (hne : β ≠ α) : ∃ a c : Fin n, a ∈ α ∧ a ∉ β ∧ c ∈ α ∧ c ∈ β := by
  classical
  have h1 : ∃ a ∈ α, a ∉ β := by
    by_contra hcon
    push Not at hcon
    exact hne (Finset.eq_of_subset_of_card_le hcon (by omega)).symm
  obtain ⟨a, ha, haβ⟩ := h1
  have h2 : 0 < (α ∩ β).card := by
    have h3 := Finset.card_union_add_card_inter α β
    have h4 : (α ∪ β).card ≤ n := by
      have := Finset.card_le_univ (α ∪ β)
      simpa using this
    omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp h2
  exact ⟨a, c, ha, haβ, (Finset.mem_inter.mp hc).1, (Finset.mem_inter.mp hc).2⟩

theorem blk_step {B : Set (Subgroup (AEQ n))} (hB : IsBlock B) {s : AEQ n} (hs : s ∈ Hn n)
    {M : Subgroup (AEQ n)} (hM : M ∈ B) (hMs : M.map (MulAut.conj s).toMonoidHom ∈ B)
    {M' : Subgroup (AEQ n)} (hM' : M' ∈ B) : M'.map (MulAut.conj s).toMonoidHom ∈ B := by
  rcases hB.2 s hs with h | h
  · have : M'.map (MulAut.conj s).toMonoidHom ∈
        (fun M : Subgroup (AEQ n) => M.map (MulAut.conj s).toMonoidHom) '' B := ⟨M', hM', rfl⟩
    rwa [h] at this
  · exact absurd hMs (Set.disjoint_left.mp h ⟨M, hM, rfl⟩)

theorem aeBlocks_of_prim (hn5 : 5 ≤ n) (hn7 : n ≤ 7) (hP : FourSetPrim n) : AEBlocks' n := by
  classical
  intro α hα B hB hT hF
  let X : Set (Finset (Fin n)) := {β | ∃ hβ : β.card = 4, ∃ c : Bool, memBar β hβ c ∈ B}
  have hXc : ∀ x ∈ X, x.card = 4 := fun x hx => hx.1
  have hαX : α ∈ X := ⟨hα, true, hT⟩
  have claim1 : ∀ β ∈ X, ∀ (hβ : β.card = 4) (c : Bool), memBar β hβ c ∈ B := by
    intro β hβX hβ c
    obtain ⟨hβ0, c0, hc0⟩ := hβX
    by_cases hβα : β = α
    · subst hβα
      cases c
      · exact hF
      · exact hT
    · obtain ⟨a, c', haα, haβ, hcα, hcβ⟩ := exists_twin_vec hn7 hα hβ0 hβα
      have hs : mkQ n (ofVec (pairVec a c')) ∈ Hn n := ⟨_, ofVec_pairVec_mem a c', rfl⟩
      have hsα : ∑ i, pairVec a c' (emb α hα i) = 0 := by
        rw [sum_pairVec_emb, if_pos haα, if_pos hcα]
        exact zmod_two_add_self _
      have hsβ : ∑ i, pairVec a c' (emb β hβ0 i) = 1 := by
        rw [sum_pairVec_emb, if_neg haβ, if_pos hcβ]
        simp
      have h1 := conj_memBar_vec_even hn5 α hα true _ hsα
      have h2 := blk_step hB hs hT (by rw [h1]; exact hT) hc0
      rw [conj_memBar_vec_odd hn5 β hβ0 c0 _ hsβ] at h2
      by_cases hcc : c = c0
      · subst hcc; exact hc0
      · have : c = !c0 := by cases c <;> cases c0 <;> simp_all
        rw [this]; exact h2
  have rule : ∀ x ∈ X, ∀ y ∈ X, ∀ p : Equiv.Perm (Fin n), Equiv.Perm.sign p = 1 →
      x.map p.toEmbedding ∈ X → y.map p.toEmbedding ∈ X := by
    intro x hx y hy p hp hxp
    have hs : mkQ n (ofPerm p) ∈ Hn n :=
      ⟨ofPerm p, ⟨by simp [wsum, ofPerm], by simpa [ofPerm] using hp⟩, rfl⟩
    obtain ⟨c1, hc1⟩ := conj_memBar_perm hn5 p x (hXc x hx) true
    have hm1 : (memBar x (hXc x hx) true).map (MulAut.conj (mkQ n (ofPerm p))).toMonoidHom ∈ B := by
      rw [hc1]; exact claim1 _ hxp _ c1
    obtain ⟨c2, hc2⟩ := conj_memBar_perm hn5 p y (hXc y hy) true
    have := blk_step hB hs (claim1 x hx _ true) hm1 (claim1 y hy (hXc y hy) true)
    rw [hc2] at this
    exact ⟨card_map_perm p (hXc y hy), c2, this⟩
  by_cases hex : ∃ β ∈ X, β ≠ α
  · right
    rintro M ⟨γ, hγ, c, rfl⟩
    exact claim1 γ (hP X hXc α hαX hex rule γ hγ) hγ c
  · left
    push Not at hex
    ext M
    constructor
    · intro hM
      obtain ⟨γ, hγ, c, rfl⟩ := hB.1 M hM
      have hγα := hex γ ⟨hγ, c, hM⟩
      subst hγα
      cases c
      · exact Or.inr rfl
      · exact Or.inl rfl
    · rintro (rfl | rfl)
      · exact hT
      · exact hF

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10
