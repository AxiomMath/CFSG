module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Mem
public import CFSG.ClassicalInvolution.Q3.TL4D1MBase
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf20

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10

@[expose] def q0List : List (Wr 4) := kList.flatMap fun k => kStarList.map fun k' => k * k'

theorem kStar_mul_inv_mem_q0 : ∀ κ ∈ kStarList, ∀ k ∈ kList, κ * k⁻¹ ∈ q0List := by
  decide +kernel

theorem kList_mul_inv_mem_q0 : ∀ κ ∈ kList, ∀ k ∈ kList, κ * k⁻¹ ∈ q0List := by
  decide +kernel

theorem fc_key : ∀ ξ ∈ q0List, ξ * ξ = 1 → ξ.perm ≠ 1 →
    ξ * ((ofVec (vec4 [0]) * yQ) * ξ * (ofVec (vec4 [0]) * yQ)⁻¹) ≠
      ((ofVec (vec4 [0]) * yQ) * ξ * (ofVec (vec4 [0]) * yQ)⁻¹) * ξ := by
  decide +kernel

theorem exists_noncomm_perm : ∀ τ : Equiv.Perm (Fin 4), τ ≠ 1 → τ ≠ d₁ → τ ≠ d₂ → τ ≠ d₃ →
    ∃ k ∈ kList, τ * k.perm ≠ k.perm * τ := by
  decide +kernel

theorem d_no_fixed : ∀ τ : Equiv.Perm (Fin 4), (τ = d₁ ∨ τ = d₂ ∨ τ = d₃) → ∀ i, τ i ≠ i := by
  decide +kernel

theorem conj_uniform (b : Wr 4) :
    ((∀ k ∈ kList, b * k * b⁻¹ ∈ kList) ∧ (∀ k ∈ kStarList, b * k * b⁻¹ ∈ kStarList)) ∨
    ((∀ k ∈ kList, b * k * b⁻¹ ∈ kStarList) ∧ (∀ k ∈ kStarList, b * k * b⁻¹ ∈ kList)) := by
  have key : ∀ k : Wr 4, b * k * b⁻¹ =
      ofVec b.vec * (ofPerm b.perm * k * (ofPerm b.perm)⁻¹) * (ofVec b.vec)⁻¹ := by
    intro k
    calc b * k * b⁻¹ = (ofVec b.vec * ofPerm b.perm) * k * (ofVec b.vec * ofPerm b.perm)⁻¹ := by
          rw [← TL4.eq_ofVec_mul_ofPerm b]
      _ = _ := by group
  rcases loc_perm b.perm with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
    rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) (∑ i, b.vec i) with h0 | h0
  · left
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩ <;> rw [key]
    · exact (loc_twin_even b.vec h0).1 _ (h1 k hk)
    · exact (loc_twin_even b.vec h0).2 _ (h1' k hk)
  · right
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩ <;> rw [key]
    · exact (loc_twin_odd b.vec h0).1 _ (h1 k hk)
    · exact (loc_twin_odd b.vec h0).2 _ (h1' k hk)
  · right
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩ <;> rw [key]
    · exact (loc_twin_even b.vec h0).2 _ (h1 k hk)
    · exact (loc_twin_even b.vec h0).1 _ (h1' k hk)
  · left
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩ <;> rw [key]
    · exact (loc_twin_odd b.vec h0).2 _ (h1 k hk)
    · exact (loc_twin_odd b.vec h0).1 _ (h1' k hk)

theorem conj_comm_mem_q0 (b : Wr 4) {k : Wr 4} (hk : k ∈ kList) : (b * k * b⁻¹) * k⁻¹ ∈ q0List := by
  rcases conj_uniform b with ⟨h, -⟩ | ⟨h, -⟩
  · exact kList_mul_inv_mem_q0 _ (h k hk) k hk
  · exact kStar_mul_inv_mem_q0 _ (h k hk) k hk

theorem conj_memBar_of_preserves {n : ℕ} (hn : 5 ≤ n) (U : Finset (Fin n)) (hU : U.card = 4)
    (w : Wr n) (hp : ∀ x, x ∈ U ↔ w.perm x ∈ U) (c : Bool) :
    ∃ c' : Bool, (memBar U hU c).map (MulAut.conj (mkQ n w)).toMonoidHom = memBar U hU c' := by
  classical
  have hrange : ∀ x, x ∈ Set.range (emb U hU) ↔ x ∈ U := fun x => by
    rw [range_emb]; exact Finset.mem_coe
  obtain ⟨b, c₁, hab, hc₁⟩ := exists_decomp (emb U hU) w (fun x => by
    rw [hrange, hrange]; exact hp x)
  have hconj : ∀ q : Wr 4, mkQ n w * mkQ n (embed (emb U hU) q) * (mkQ n w)⁻¹ =
      mkQ n (embed (emb U hU) (b * q * b⁻¹)) := by
    intro q
    rw [← map_inv, ← map_mul, ← map_mul, conj_embed (emb U hU) hab hc₁ q]
  rcases conj_uniform b with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨c, map_conj_eq_of_le hn _ ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    cases c
    · obtain ⟨k, hk, rfl⟩ := mem_memBar_false.mp hx
      show mkQ n w * _ * (mkQ n w)⁻¹ ∈ _
      rw [hconj]
      exact mkQ_embed_mem_false U hU (h2 k hk)
    · obtain ⟨k, hk, rfl⟩ := mem_memBar_true.mp hx
      show mkQ n w * _ * (mkQ n w)⁻¹ ∈ _
      rw [hconj]
      exact mkQ_embed_mem_true U hU (h1 k hk)
  · refine ⟨!c, map_conj_eq_of_le hn _ ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    cases c
    · obtain ⟨k, hk, rfl⟩ := mem_memBar_false.mp hx
      show mkQ n w * _ * (mkQ n w)⁻¹ ∈ _
      rw [hconj]
      exact mkQ_embed_mem_true U hU (h2 k hk)
    · obtain ⟨k, hk, rfl⟩ := mem_memBar_true.mp hx
      show mkQ n w * _ * (mkQ n w)⁻¹ ∈ _
      rw [hconj]
      exact mkQ_embed_mem_false U hU (h1 k hk)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf20
