module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Prim8b
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10N8

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8

theorem aeBlocks8_of_prim : AEBlocks8' := by
  have hP := fourSetPrim_eight
  classical
  intro α hα B hB hT hF
  have hn5 : 5 ≤ 8 := by norm_num
  let X1 : Set (Finset (Fin 8)) :=
    {β | ∃ hβ : β.card = 4, memBar β hβ true ∈ B ∧ memBar β hβ false ∈ B}
  have hX1c : ∀ x ∈ X1, x.card = 4 := fun x hx => hx.1
  have hαX : α ∈ X1 := ⟨hα, hT, hF⟩
  have claim1 : ∀ β : Finset (Fin 8), ∀ (hβ : β.card = 4), β ≠ αᶜ →
      (∃ c : Bool, memBar β hβ c ∈ B) → β ∈ X1 := by
    intro β hβ hβc ⟨c0, hc0⟩
    by_cases hβα : β = α
    · subst hβα; exact ⟨hβ, hT, hF⟩
    ·
      have hinter : 0 < (α ∩ β).card := by
        by_contra hcon
        have h0 : α ∩ β = ∅ := by rw [← Finset.card_eq_zero]; omega
        have hsub : β ⊆ αᶜ := by
          intro x hx
          rw [Finset.mem_compl]
          intro hxa
          have : x ∈ α ∩ β := Finset.mem_inter.mpr ⟨hxa, hx⟩
          rw [h0] at this; simp at this
        have hcc : (αᶜ).card = 4 := by rw [Finset.card_compl, hα]; simp
        exact hβc (Finset.eq_of_subset_of_card_le hsub (by rw [hβ, hcc]))
      obtain ⟨c', hc'⟩ := Finset.card_pos.mp hinter
      have hc'α : c' ∈ α := (Finset.mem_inter.mp hc').1
      have hc'β : c' ∈ β := (Finset.mem_inter.mp hc').2
      have h1 : ∃ a ∈ α, a ∉ β := by
        by_contra hcon
        push Not at hcon
        exact hβα (Finset.eq_of_subset_of_card_le hcon (by omega)).symm
      obtain ⟨a, haα, haβ⟩ := h1
      have hs : mkQ 8 (ofVec (pairVec a c')) ∈ Hn 8 := ⟨_, ofVec_pairVec_mem a c', rfl⟩
      have hsα : ∑ i, pairVec a c' (emb α hα i) = 0 := by
        rw [sum_pairVec_emb, if_pos haα, if_pos hc'α]
        exact zmod_two_add_self _
      have hsβ : ∑ i, pairVec a c' (emb β hβ i) = 1 := by
        rw [sum_pairVec_emb, if_neg haβ, if_pos hc'β]
        simp
      have h1 := conj_memBar_vec_even hn5 α hα true _ hsα
      have h2 := blk_step hB hs hT (by rw [h1]; exact hT) hc0
      rw [conj_memBar_vec_odd hn5 β hβ c0 _ hsβ] at h2
      refine ⟨hβ, ?_⟩
      cases c0
      · exact ⟨h2, hc0⟩
      · exact ⟨hc0, h2⟩
  have rule : ∀ x ∈ X1, ∀ y ∈ X1, ∀ p : Equiv.Perm (Fin 8), Equiv.Perm.sign p = 1 →
      x.map p.toEmbedding ∈ X1 → y.map p.toEmbedding ∈ X1 := by
    intro x hx y hy p hp hxp
    have hs : mkQ 8 (ofPerm p) ∈ Hn 8 :=
      ⟨ofPerm p, ⟨by simp [wsum, ofPerm], by simpa [ofPerm] using hp⟩, rfl⟩
    obtain ⟨hxc, hxT, hxF⟩ := hx
    obtain ⟨hyc, hyT, hyF⟩ := hy
    obtain ⟨hxpc, hxpT, hxpF⟩ := hxp
    obtain ⟨c1, hc1⟩ := conj_memBar_perm hn5 p x hxc true
    obtain ⟨d1, hd1⟩ := conj_memBar_perm hn5 p y hyc true
    obtain ⟨d2, hd2⟩ := conj_memBar_perm hn5 p y hyc false
    have hm1 : (memBar x hxc true).map (MulAut.conj (mkQ 8 (ofPerm p))).toMonoidHom ∈ B := by
      rw [hc1]; cases c1
      · exact hxpF
      · exact hxpT
    have hi1 := blk_step hB hs hxT hm1 hyT
    have hi2 := blk_step hB hs hxT hm1 hyF
    rw [hd1] at hi1
    rw [hd2] at hi2
    have hdne : d1 ≠ d2 := by
      intro hd
      subst hd
      have heq : (memBar y hyc true).map (MulAut.conj (mkQ 8 (ofPerm p))).toMonoidHom =
          (memBar y hyc false).map (MulAut.conj (mkQ 8 (ofPerm p))).toMonoidHom := by
        rw [hd1, hd2]
      exact memBar_true_ne_false hn5 y hyc
        (Subgroup.map_injective (MulAut.conj (mkQ 8 (ofPerm p))).injective heq)
    refine ⟨card_map_perm p hyc, ?_⟩
    cases d1 <;> cases d2
    · exact absurd rfl hdne
    · exact ⟨hi2, hi1⟩
    · exact ⟨hi1, hi2⟩
    · exact absurd rfl hdne
  by_cases hex : ∃ β ∈ X1, β ≠ α ∧ β ≠ αᶜ
  · right; right
    rintro M ⟨γ, hγ, c, rfl⟩
    have hγX := hP X1 hX1c α hαX hex rule γ hγ
    obtain ⟨_, hγT, hγF⟩ := hγX
    cases c
    · exact hγF
    · exact hγT
  · right; left
    push Not at hex
    intro M hM
    obtain ⟨β, hβ, c, rfl⟩ := hB.1 M hM
    by_cases hβα : β = α
    · exact ⟨β, hβ, c, Or.inl hβα, rfl⟩
    · by_cases hβc : β = αᶜ
      · exact ⟨β, hβ, c, Or.inr hβc, rfl⟩
      · exact absurd (hex β (claim1 β hβ hβc ⟨c, hM⟩) hβα) hβc

theorem aeBlocks8' : AEBlocks8' := aeBlocks8_of_prim

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10
