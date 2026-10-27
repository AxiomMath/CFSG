module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Blk

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8

variable {n : ℕ}

theorem exists_twin_vec' (hn7 : n ≤ 7 ∨ 9 ≤ n) {α β : Finset (Fin n)} (hα : α.card = 4)
    (hβ : β.card = 4) (hne : β ≠ α) :
    ∃ a c : Fin n, ∑ i, pairVec a c (emb α hα i) = 0 ∧ ∑ i, pairVec a c (emb β hβ i) = 1 := by
  classical
  rcases hn7 with hn7 | hn9
  · obtain ⟨a, c, haα, haβ, hcα, hcβ⟩ := exists_twin_vec hn7 hα hβ hne
    refine ⟨a, c, ?_, ?_⟩
    · rw [sum_pairVec_emb, if_pos haα, if_pos hcα]
      exact zmod_two_add_self _
    · rw [sum_pairVec_emb, if_neg haβ, if_pos hcβ]
      simp
  · have h1 : ∃ b ∈ β, b ∉ α := by
      by_contra hcon
      push Not at hcon
      exact hne (Finset.eq_of_subset_of_card_le hcon (by omega))
    obtain ⟨b, hb, hbα⟩ := h1
    have h2 : ∃ j, j ∉ α ∪ β := by
      by_contra hcon
      push Not at hcon
      have : (α ∪ β).card = n := by
        have : α ∪ β = Finset.univ := Finset.eq_univ_of_forall hcon
        rw [this]; simp
      have h3 := Finset.card_union_le α β
      omega
    obtain ⟨j, hj⟩ := h2
    rw [Finset.mem_union, not_or] at hj
    refine ⟨b, j, ?_, ?_⟩
    · rw [sum_pairVec_emb, if_neg hbα, if_neg hj.1]; simp
    · rw [sum_pairVec_emb, if_pos hb, if_neg hj.2]; simp

theorem aeBlocks_of_prim' (hn5 : 5 ≤ n) (hn7 : n ≤ 7 ∨ 9 ≤ n) (hP : FourSetPrim n) :
    AEBlocks' n := by
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
    · obtain ⟨a, c', hsα, hsβ⟩ := exists_twin_vec' hn7 hα hβ0 hβα
      have hs : mkQ n (ofVec (pairVec a c')) ∈ Hn n := ⟨_, ofVec_pairVec_mem a c', rfl⟩
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
