module

public import CFSG.ClassicalInvolution.Q3.AE.PermElt

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {n : ℕ}

theorem conj_perm_embed (σ : Equiv.Perm (Fin n)) (ι : Fin 4 ↪ Fin n) (a : Wr 4) :
    ofPerm σ * embed ι a * (ofPerm σ)⁻¹ = embed (ι.trans σ.toEmbedding) a := by
  classical
  refine Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
  · rw [ofPerm_conj_vec, embed_vec, embed_vec]
    by_cases hx : σ.symm x ∈ Set.range ι
    · obtain ⟨i, hi⟩ := hx
      have hx' : x = (ι.trans σ.toEmbedding) i := by
        show x = σ (ι i)
        rw [hi, Equiv.apply_symm_apply]
      rw [← hi, embedVec_apply, hx', embedVec_apply]
    · have hx' : x ∉ Set.range (ι.trans σ.toEmbedding) := by
        rintro ⟨i, rfl⟩
        apply hx
        exact ⟨i, by show ι i = σ.symm (σ (ι i)); simp⟩
      rw [embedVec_of_not_mem _ _ hx, embedVec_of_not_mem _ _ hx']
  · rw [ofPerm_conj_perm]
    show σ ((embed ι a).perm (σ⁻¹ x)) = (embed (ι.trans σ.toEmbedding) a).perm x
    rw [embed_perm, embed_perm, Equiv.Perm.inv_def]
    by_cases hx : σ.symm x ∈ Set.range ι
    · obtain ⟨i, hi⟩ := hx
      have hx' : x = (ι.trans σ.toEmbedding) i := by
        show x = σ (ι i)
        rw [hi, Equiv.apply_symm_apply]
      rw [← hi, embedPerm_apply, hx', embedPerm_apply]
      rfl
    · have hx' : x ∉ Set.range (ι.trans σ.toEmbedding) := by
        rintro ⟨i, rfl⟩
        apply hx
        exact ⟨i, by show ι i = σ.symm (σ (ι i)); simp⟩
      rw [embedPerm_of_not_mem _ _ hx, embedPerm_of_not_mem _ _ hx', Equiv.apply_symm_apply]

theorem embed_trans_perm (ι : Fin 4 ↪ Fin n) (c : Equiv.Perm (Fin 4)) (a : Wr 4) :
    embed (c.toEmbedding.trans ι) a = embed ι (ofPerm c * a * (ofPerm c)⁻¹) := by
  classical
  have hrange : Set.range (c.toEmbedding.trans ι) = Set.range ι := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨c i, rfl⟩
    · rintro ⟨j, rfl⟩; exact ⟨c.symm j, by show ι (c (c.symm j)) = ι j; simp⟩
  refine Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
  · rw [embed_vec, embed_vec]
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨j, rfl⟩ := hx
      have : ι j = (c.toEmbedding.trans ι) (c.symm j) := by
        show ι j = ι (c (c.symm j)); simp
      rw [this, embedVec_apply, ← this, embedVec_apply, ofPerm_conj_vec]
    · rw [embedVec_of_not_mem _ _ (by rwa [hrange]), embedVec_of_not_mem _ _ hx]
  · rw [embed_perm, embed_perm]
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨j, rfl⟩ := hx
      have : ι j = (c.toEmbedding.trans ι) (c.symm j) := by
        show ι j = ι (c (c.symm j)); simp
      rw [this, embedPerm_apply, ← this, embedPerm_apply, ofPerm_conj_perm]
      show ι (c (a.perm (c.symm j))) = ι ((c * a.perm * c⁻¹) j)
      simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
    · rw [embedPerm_of_not_mem _ _ (by rwa [hrange]), embedPerm_of_not_mem _ _ hx]

theorem conj_kQ_cases : ∀ c : Equiv.Perm (Fin 4),
    (∀ k ∈ kList, ofPerm c * k * (ofPerm c)⁻¹ ∈ kList) ∨
      (∀ k ∈ kList, ofPerm c * k * (ofPerm c)⁻¹ ∈ kStarList) := by decide +kernel

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf
