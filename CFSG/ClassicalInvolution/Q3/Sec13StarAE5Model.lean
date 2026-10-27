module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdAE5A

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13.AE5Star

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

theorem eq_of_commutes {α α' : Finset (Fin 5)} (h : α.card = 4) (h' : α'.card = 4)
    {b b' : Bool} (hne : memBar α h b ≠ memBar α' h' b')
    (hc : ∀ x ∈ memBar α h b, ∀ y ∈ memBar α' h' b', x * y = y * x) : α = α' := by
  clear hne
  by_contra hαα'
  have hd : Disjoint α α' :=
    disjoint_of_zBar_comm hαα' fun y hy => hc _ (zBar_mem_memBar α h b) y hy
  have h5 := Finset.card_le_univ (α ∪ α')
  rw [Finset.card_union_of_disjoint hd, h, h', Fintype.card_fin] at h5
  omega

private theorem local_vec_conj : ∀ v : Fin 4 → ZMod 2, ∀ c : Bool, ∃ d : Bool,
    ∀ a ∈ TL4.AE5.localList c, ofVec v * a * (ofVec v)⁻¹ ∈ TL4.AE5.localList d := by
  decide +kernel

private theorem zOf_eq_ofVec (ι : Fin 4 ↪ Fin 5) : zOf ι = ofVec (zOf ι).vec :=
  Wr.ext rfl (zOf_perm ι)

theorem conj_memBar_of_comm {α : Finset (Fin 5)} (h : α.card = 4) {x : AEQ 5}
    (h1 : ∀ a ∈ memBar α h true, x * a = a * x) (h2 : ∀ a ∈ memBar α h false, x * a = a * x)
    (β : Finset (Fin 5)) (hβ : β.card = 4) (c : Bool) :
    (memBar β hβ c).map (MulAut.conj x).toMonoidHom = memBar β hβ true ∨
      (memBar β hβ c).map (MulAut.conj x).toMonoidHom = memBar β hβ false := by
  suffices ∃ d, (memBar β hβ c).map (MulAut.conj x).toMonoidHom = memBar β hβ d by
    rcases this with ⟨_ | _, hd⟩
    exacts [Or.inr hd, Or.inl hd]
  rcases TL4.AE5.eq_one_or_eq_zBar_of_comm α h h1 h2 with rfl | rfl
  · have e : (MulAut.conj (1 : AEQ 5)).toMonoidHom = MonoidHom.id _ := by
      ext g
      simp
    exact ⟨c, by rw [e, Subgroup.map_id]⟩
  · obtain ⟨d, hd⟩ := local_vec_conj ((zOf (emb α h)).vec ∘ emb β hβ) c
    have hle : (memBar β hβ c).map (MulAut.conj (zBar α h)).toMonoidHom ≤ memBar β hβ d := by
      rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      obtain ⟨a₀, ha₀, rfl⟩ := (TL4.AE5.mem_memAt_iff β hβ).mp ha
      show zBar α h * mkQ 5 (embed (emb β hβ) a₀) * (zBar α h)⁻¹ ∈ memBar β hβ d
      rw [zBar, ← map_inv, ← map_mul, ← map_mul, zOf_eq_ofVec, TL4.SecIdE2.ofVec_conj_embed]
      exact TL4.AE5.embed_mem_memBar β hβ (hd a₀ ha₀)
    have : Finite (memBar β hβ d) :=
      Nat.finite_of_card_ne_zero (by rw [natCard_memBar (le_refl 5)]; norm_num)
    refine ⟨d, Subgroup.eq_of_le_of_card_ge hle ?_⟩
    rw [Subgroup.card_map_of_injective (MulAut.conj (zBar α h)).injective,
      natCard_memBar (le_refl 5), natCard_memBar (le_refl 5)]

end CFSG.ClassicalInvolution.Q3.Sec13.AE5Star
