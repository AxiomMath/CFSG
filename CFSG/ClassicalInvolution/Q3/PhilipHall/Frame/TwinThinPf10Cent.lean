module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Char

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {n : ℕ}

theorem ofVec_mul_self (u : Fin n → ZMod 2) : ofVec u * ofVec u = 1 := by
  refine Wr.ext (funext fun x => ?_) ?_
  · show u x + u ((1 : Equiv.Perm (Fin n)).symm x) = 0
    exact zmod_two_add_self _
  · rfl

theorem zOf_mul_self (ι : Fin 4 ↪ Fin n) : zOf ι * zOf ι = 1 := by
  rw [zOf_eq_ofVec, ofVec_mul_self]

theorem zOf_perm (ι : Fin 4 ↪ Fin n) : (zOf ι).perm = 1 := by
  rw [zOf_eq_ofVec]; rfl

theorem exists_split (hn : 5 ≤ n) (hn8 : n ≠ 8) (α : Finset (Fin n)) (hα : α.card = 4) (w : Wr n)
    (hB : ∀ c : Bool, ∀ x ∈ memBar α hα c, mkQ n w * x * (mkQ n w)⁻¹ = x) :
    ∃ c e : Wr n, w = c * e ∧ (e = 1 ∨ e = zOf (emb α hα)) ∧
      SupportedOn c (Set.range (emb α hα))ᶜ := by
  have hz := hB true (zBar α hα) (zBar_mem_memBar α hα true)
  have hz' : mkQ n (w * zOf (emb α hα) * w⁻¹) = mkQ n (zOf (emb α hα)) := by
    have hz0 : mkQ n w * mkQ n (zOf (emb α hα)) * (mkQ n w)⁻¹ = mkQ n (zOf (emb α hα)) := hz
    simpa only [map_mul, map_inv] using hz0
  have hp := perm_range_of_conj hn8 (emb α hα) w hz'
  obtain ⟨b, c, hwb, hc⟩ := exists_decomp (emb α hα) w hp
  have hloc : ∀ k : Wr 4, (mkQ n (embed (emb α hα) k) ∈ memBar α hα true ∨
      mkQ n (embed (emb α hα) k) ∈ memBar α hα false) → b * k * b⁻¹ = k := by
    intro k hk
    have h1 : mkQ n (w * embed (emb α hα) k * w⁻¹) = mkQ n (embed (emb α hα) k) := by
      have := hk.elim (hB true _) (hB false _)
      simpa only [map_mul, map_inv] using this
    rw [conj_embed (emb α hα) hwb hc k] at h1
    have h2 := mkQ_inj_of_supportedOn hn (embed_supportedOn (emb α hα) _)
      (embed_supportedOn (emb α hα) k) h1
    exact embed_injective _ h2
  have hb := loc_cent b (fun k hk => hloc k (Or.inl (mkQ_embed_mem_true α hα hk)))
    (fun k hk => hloc k (Or.inr (mkQ_embed_mem_false α hα hk)))
  refine ⟨c, embed (emb α hα) b, hwb, ?_, hc⟩
  rcases hb with rfl | rfl
  · left; exact map_one _
  · right; rfl

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10
