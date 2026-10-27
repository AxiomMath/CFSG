module

public import CFSG.ClassicalInvolution.Q3.AE.Embed

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {n : ℕ}

theorem conj_embed_vec (ι : Fin 4 ↪ Fin n) (u : Fin n → ZMod 2) (k : Wr 4) :
    ofVec u * embed ι k * (ofVec u)⁻¹ =
      embed ι (ofVec (fun i => u (ι i)) * k * (ofVec (fun i => u (ι i)))⁻¹) := by
  classical
  refine Wr.ext (funext fun x => ?_) ?_
  · show (u x + (embed ι k).vec ((1 : Equiv.Perm (Fin n)).symm x)) +
      u ((embed ι k).perm.symm x) = _
    rw [embed_vec]
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      show (u (ι i) + embedVec ι k.vec ((1 : Equiv.Perm (Fin n)).symm (ι i))) +
          u ((embed ι k).perm.symm (ι i)) =
        embedVec ι ((ofVec (fun i => u (ι i)) * k * (ofVec (fun i => u (ι i)))⁻¹).vec) (ι i)
      rw [embed_perm, embedPerm_symm_apply, embedVec_apply]
      show (u (ι i) + embedVec ι k.vec (ι i)) + u (ι (k.perm.symm i)) =
        (u (ι i) + k.vec i) + u (ι (k.perm.symm i))
      rw [embedVec_apply]
    · rw [embed_perm, embedPerm_symm_of_not_mem ι _ hx]
      show (u x + embedVec ι k.vec x) + u x =
        embedVec ι ((ofVec (fun i => u (ι i)) * k * (ofVec (fun i => u (ι i)))⁻¹).vec) x
      rw [embedVec_of_not_mem ι _ hx, embedVec_of_not_mem ι _ hx]
      have := zmod_two_add_self (u x)
      calc (u x + 0) + u x = u x + u x := by ring
        _ = 0 := this
  · show 1 * (embed ι k).perm * (1 : Equiv.Perm (Fin n))⁻¹ = embedPerm ι (1 * k.perm * 1⁻¹)
    simp [embed_perm]

theorem conj_embed_perm (ι ι' : Fin 4 ↪ Fin n) (p : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin 4))
    (hτ : ∀ i, p (ι i) = ι' (τ i)) (k : Wr 4) :
    ofPerm p * embed ι k * (ofPerm p)⁻¹ = embed ι' (ofPerm τ * k * (ofPerm τ)⁻¹) := by
  classical
  have hsym : ∀ j, p.symm (ι' j) = ι (τ.symm j) := fun j => by
    apply p.injective
    rw [Equiv.apply_symm_apply, hτ, Equiv.apply_symm_apply]
  refine Wr.ext (funext fun x => ?_) ?_
  · show (0 + (embed ι k).vec (p.symm x)) + 0 = _
    rw [zero_add, add_zero, embed_vec]
    show embedVec ι k.vec (p.symm x) = embedVec ι' (ofPerm τ * k * (ofPerm τ)⁻¹).vec x
    by_cases hx : x ∈ Set.range ι'
    · obtain ⟨j, rfl⟩ := hx
      rw [hsym, embedVec_apply, embedVec_apply]
      show k.vec (τ.symm j) = (0 + k.vec (τ.symm j)) + 0
      rw [zero_add, add_zero]
    · have hnot : p.symm x ∉ Set.range ι := by
        rintro ⟨i, hi⟩
        apply hx
        refine ⟨τ i, ?_⟩
        rw [← hτ, hi, Equiv.apply_symm_apply]
      rw [embedVec_of_not_mem ι _ hnot, embedVec_of_not_mem ι' _ hx]
  · refine Equiv.ext fun x => ?_
    show p ((embedPerm ι k.perm) (p.symm x)) = (embedPerm ι' (τ * k.perm * τ⁻¹)) x
    by_cases hx : x ∈ Set.range ι'
    · obtain ⟨j, rfl⟩ := hx
      rw [hsym, embedPerm_apply, hτ, embedPerm_apply]
      simp
    · have hnot : p.symm x ∉ Set.range ι := by
        rintro ⟨i, hi⟩
        apply hx
        refine ⟨τ i, ?_⟩
        rw [← hτ, hi, Equiv.apply_symm_apply]
      rw [embedPerm_of_not_mem ι _ hnot, embedPerm_of_not_mem ι' _ hx, Equiv.apply_symm_apply]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10
