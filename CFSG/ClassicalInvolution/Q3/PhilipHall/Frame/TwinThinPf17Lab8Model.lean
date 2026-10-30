module

public import CFSG.ClassicalInvolution.Q3.TL4D1MAMA

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf17Lab8

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

theorem eq_or_compl_of_zBar_eq {α γ : Finset (Fin 8)} {hα : α.card = 4} {hγ : γ.card = 4}
    (he : zBar γ hγ = zBar α hα) : γ = α ∨ γ = αᶜ := by
  classical
  rcases mkQ_eq_iff.mp he with h1 | h1
  · left
    have := range_eq_of_zOf_eq (inv_mul_eq_one.mp h1)
    rw [range_emb, range_emb] at this
    exact_mod_cast this
  · right
    have hv : ∀ x, (zOf (emb γ hγ)).vec x + (zOf (emb α hα)).vec x = 1 := by
      intro x
      have h2 := congrFun (congrArg Wr.vec h1) x
      rw [mul_vec, zOf_inv, zOf_perm] at h2
      exact h2
    ext x
    have h3 := hv x
    rw [zOf_vec_apply, zOf_vec_apply] at h3
    have e1 : x ∈ Set.range (emb γ hγ) ↔ x ∈ γ := by rw [range_emb]; exact Finset.mem_coe
    have e2 : x ∈ Set.range (emb α hα) ↔ x ∈ α := by rw [range_emb]; exact Finset.mem_coe
    rw [Finset.mem_compl]
    by_cases h4 : x ∈ γ <;> by_cases h5 : x ∈ α <;>
      simp only [e1.mpr, e2.mpr, h4, h5, ite_true, ite_false, e1, e2] at h3 ⊢ <;> first
        | exact absurd h3 (by decide) | simp [h4, h5]

theorem eq_compl_of_disjoint {α β : Finset (Fin 8)} (hα : α.card = 4) (hβ : β.card = 4)
    (hd : Disjoint β α) : β = αᶜ := by
  have hsub : β ⊆ αᶜ := fun x hx =>
    Finset.mem_compl.mpr (fun hxa => Finset.disjoint_left.mp hd hx hxa)
  have hcc : (αᶜ).card = 4 := by rw [Finset.card_compl, Fintype.card_fin, hα]
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hβ, hcc])

@[expose] def cycFin8 (d b c : Fin 8) : Equiv.Perm (Fin 8) := Equiv.swap d b * Equiv.swap b c

theorem cycFin8_apply_left {d b c : Fin 8} (hdb : d ≠ b) (hdc : d ≠ c) : cycFin8 d b c d = b := by
  rw [cycFin8, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hdb hdc, Equiv.swap_apply_left]

theorem cycFin8_apply_of_ne {d b c x : Fin 8} (hxd : x ≠ d) (hxb : x ≠ b) (hxc : x ≠ c) :
    cycFin8 d b c x = x := by
  rw [cycFin8, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxb hxc,
    Equiv.swap_apply_of_ne_of_ne hxd hxb]

theorem cycFin8_pow_three : ∀ d b c : Fin 8, d ≠ b → b ≠ c → d ≠ c → cycFin8 d b c ^ 3 = 1 := by
  decide +kernel

theorem sign_cycFin8 {d b c : Fin 8} (hdb : d ≠ b) (hbc : b ≠ c) :
    Equiv.Perm.sign (cycFin8 d b c) = 1 := by
  rw [cycFin8, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hdb, Equiv.Perm.sign_swap hbc]
  decide

theorem ofPerm_comm_ofVec {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n → ZMod 2)
    (hv : ∀ x, v (σ.symm x) = v x) : ofPerm σ * ofVec v = ofVec v * ofPerm σ := by
  refine Wr.ext (funext fun x => ?_) (by simp [mul_perm, ofPerm, ofVec])
  show (0 : ZMod 2) + v (σ.symm x) = v x + 0
  rw [zero_add, add_zero, hv]

theorem pairVec_perm_symm {n : ℕ} (σ : Equiv.Perm (Fin n)) {a c : Fin n} (ha : σ a = a)
    (hc : σ c = c) (x : Fin n) :
    CFSG.ClassicalInvolution.Q3.TL4.pairVec a c (σ.symm x) =
      CFSG.ClassicalInvolution.Q3.TL4.pairVec a c x := by
  rw [CFSG.ClassicalInvolution.Q3.TL4.pairVec_apply, CFSG.ClassicalInvolution.Q3.TL4.pairVec_apply]
  have h1 : σ.symm x = a ↔ x = a := by
    rw [Equiv.symm_apply_eq, ha]
  have h2 : σ.symm x = c ↔ x = c := by
    rw [Equiv.symm_apply_eq, hc]
  simp only [h1, h2]

theorem map_cycFin8_ne {α : Finset (Fin 8)} {d b c a : Fin 8} (hdα : d ∈ α) (hbα : b ∉ α)
    (hcα : c ∉ α) (haα : a ∈ α) (had : a ≠ d) (hdb : d ≠ b) (hdc : d ≠ c) :
    α.map (cycFin8 d b c).toEmbedding ≠ α ∧ α.map (cycFin8 d b c).toEmbedding ≠ αᶜ := by
  constructor
  · intro h
    have h1 : b ∈ α.map (cycFin8 d b c).toEmbedding :=
      Finset.mem_map.mpr ⟨d, hdα, by simpa using cycFin8_apply_left hdb hdc⟩
    rw [h] at h1
    exact hbα h1
  · intro h
    have hab : a ≠ b := fun e => hbα (e ▸ haα)
    have hac : a ≠ c := fun e => hcα (e ▸ haα)
    have h1 : a ∈ α.map (cycFin8 d b c).toEmbedding :=
      Finset.mem_map.mpr ⟨a, haα, by simpa using cycFin8_apply_of_ne had hab hac⟩
    rw [h] at h1
    exact (Finset.mem_compl.mp h1) haα

theorem exists_cyc {α : Finset (Fin 8)} (hα : α.card = 4) {a c : Fin 8} (ha : a ∈ α)
    (hc : c ∈ α) :
    ∃ d b₁ c₁ : Fin 8, d ∈ α ∧ d ≠ a ∧ d ≠ c ∧ b₁ ∉ α ∧ c₁ ∉ α ∧ b₁ ≠ c₁ := by
  classical
  obtain ⟨d, hdα, hda, hdc⟩ : ∃ d ∈ α, d ≠ a ∧ d ≠ c := by
    by_contra hne
    push Not at hne
    have hsub : α ⊆ {a, c} := fun d hd => by
      by_cases hda : d = a
      · simp [hda]
      · simp [hne d hd hda]
    have h2 := Finset.card_le_card hsub
    have h3 := Finset.card_insert_le a ({c} : Finset (Fin 8))
    rw [Finset.card_singleton] at h3
    omega
  have hcc : (αᶜ).card = 4 := by rw [Finset.card_compl, Fintype.card_fin, hα]
  obtain ⟨b₁, hb₁, c₁, hc₁, hbc⟩ := Finset.one_lt_card.mp (by rw [hcc]; norm_num : 1 < (αᶜ).card)
  exact ⟨d, b₁, c₁, hdα, hda, hdc, Finset.mem_compl.mp hb₁, Finset.mem_compl.mp hc₁, hbc⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf17Lab8
