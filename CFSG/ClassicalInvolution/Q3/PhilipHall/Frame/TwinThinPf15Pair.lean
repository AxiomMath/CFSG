module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Mem
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Coc

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf15

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {n : ℕ}

@[expose] def PairPres (n : ℕ) (f : MulAut (AEQ n)) : Prop :=
  ∀ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool), ∃ (β : Finset (Fin n)) (hβ : β.card = 4)
    (c : Bool), (memBar α h b).map f.toMonoidHom = memBar β hβ c ∧
      (memBar α h (!b)).map f.toMonoidHom = memBar β hβ (!c)

theorem memBar_ne_not (hn : 5 ≤ n) (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    memBar α h b ≠ memBar α h (!b) := by
  cases b
  · exact (memBar_true_ne_false hn α h).symm
  · exact memBar_true_ne_false hn α h

theorem pairPres_mul (f g : MulAut (AEQ n)) (hf : PairPres n f) (hg : PairPres n g) :
    PairPres n (f * g) := by
  intro α h b
  obtain ⟨β, hβ, c, h1, h2⟩ := hg α h b
  obtain ⟨γ, hγ, d, h3, h4⟩ := hf β hβ c
  have hfg : (f * g).toMonoidHom = f.toMonoidHom.comp g.toMonoidHom := rfl
  refine ⟨γ, hγ, d, ?_, ?_⟩
  · rw [hfg, ← Subgroup.map_map, h1, h3]
  · rw [hfg, ← Subgroup.map_map, h2, h4]

theorem pairPres_perm (hn : 5 ≤ n) (p : Equiv.Perm (Fin n)) :
    PairPres n (MulAut.conj (mkQ n (ofPerm p))) := by
  intro α h b
  obtain ⟨c₁, h₁⟩ := TwinThinPf10.conj_memBar_perm hn p α h b
  obtain ⟨c₂, h₂⟩ := TwinThinPf10.conj_memBar_perm hn p α h (!b)
  refine ⟨α.map p.toEmbedding, TwinThinPf10.card_map_perm p h, c₁, h₁, ?_⟩
  rw [h₂]
  have hc : c₂ = !c₁ := by
    by_contra hne
    have hc' : c₂ = c₁ := by cases c₁ <;> cases c₂ <;> simp_all
    have : (memBar α h b).map (MulAut.conj (mkQ n (ofPerm p))).toMonoidHom =
        (memBar α h (!b)).map (MulAut.conj (mkQ n (ofPerm p))).toMonoidHom := by
      rw [h₁, h₂, hc']
    exact memBar_ne_not hn α h b (Subgroup.map_injective (MulAut.conj _).injective this)
  rw [hc]

theorem pairPres_vec (hn : 5 ≤ n) (v : Fin n → ZMod 2) :
    PairPres n (MulAut.conj (mkQ n (ofVec v))) := by
  intro α h b
  rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) (∑ i, v (emb α h i)) with h0 | h1
  · exact ⟨α, h, b, TwinThinPf10.conj_memBar_vec_even hn α h b v h0,
      TwinThinPf10.conj_memBar_vec_even hn α h (!b) v h0⟩
  · refine ⟨α, h, !b, TwinThinPf10.conj_memBar_vec_odd hn α h b v h1, ?_⟩
    rw [Bool.not_not]
    exact TwinThinPf10.conj_memBar_vec_odd hn α h (!b) v h1 |>.trans (by rw [Bool.not_not])

theorem pairPres_of_mem (hn : 5 ≤ n) {x : AEQ n} (hx : x ∈ TwinThinPf8.Hn n) : PairPres n (MulAut.conj x) := by
  obtain ⟨w, -, rfl⟩ := hx
  have hw : w = ofVec w.vec * ofPerm w.perm := (TL4.Mdl117.ofVec_mul_ofPerm w).symm
  rw [hw, map_mul, map_mul]
  exact pairPres_mul _ _ (pairPres_vec hn _) (pairPres_perm hn _)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf15
