module

public import CFSG.ClassicalInvolution.Q3.AE.Conj
public import CFSG.ClassicalInvolution.Q3.AE.E64
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2Conj

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

namespace TwinDisc

namespace AE5

theorem conj_S4 : ∀ c : Equiv.Perm (Fin 4),
    ((∀ k ∈ kList, ofPerm c * k * (ofPerm c)⁻¹ ∈ kList) ∧
      (∀ k ∈ kStarList, ofPerm c * k * (ofPerm c)⁻¹ ∈ kStarList)) ∨
    ((∀ k ∈ kList, ofPerm c * k * (ofPerm c)⁻¹ ∈ kStarList) ∧
      (∀ k ∈ kStarList, ofPerm c * k * (ofPerm c)⁻¹ ∈ kList)) := by decide +kernel

variable {n : ℕ}

theorem mem_memBar_true {α : Finset (Fin n)} {h : α.card = 4} {x : AEQ n} :
    x ∈ memBar α h true ↔ ∃ k ∈ kList, x = mkQ n (embed (emb α h) k) := by
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨k, hk, rfl⟩, rfl⟩

theorem mem_memBar_false {α : Finset (Fin n)} {h : α.card = 4} {x : AEQ n} :
    x ∈ memBar α h false ↔ ∃ k ∈ kStarList, x = mkQ n (embed (emb α h) k) := by
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨k, hk, rfl⟩, rfl⟩

theorem card_conj_memBar (hn : 5 ≤ n) (g : AEQ n) {α : Finset (Fin n)} {h : α.card = 4} (b : Bool) :
    Nat.card ((memBar α h b).map (MulAut.conj g).toMonoidHom) = 8 := by
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, natCard_memBar hn]

theorem conj_memBar_perm (hn : 5 ≤ n) {α β : Finset (Fin n)} {h : α.card = 4} {h' : β.card = 4}
    (σ : Equiv.Perm (Fin n)) (c : Equiv.Perm (Fin 4))
    (hemb : (emb α h).trans σ.toEmbedding = c.toEmbedding.trans (emb β h')) :
    ∃ e : Bool, ∀ b : Bool,
      (memBar α h b).map (MulAut.conj (mkQ n (ofPerm σ))).toMonoidHom = memBar β h' (xor b e) := by
  have img : ∀ k : Wr 4, mkQ n (ofPerm σ) * mkQ n (embed (emb α h) k) * (mkQ n (ofPerm σ))⁻¹ =
      mkQ n (embed (emb β h') (ofPerm c * k * (ofPerm c)⁻¹)) := by
    intro k
    rw [← map_inv, ← map_mul, ← map_mul, conj_perm_embed, hemb, embed_trans_perm]
  have fin : ∀ (b b' : Bool), (∀ x ∈ memBar α h b, mkQ n (ofPerm σ) * x * (mkQ n (ofPerm σ))⁻¹ ∈
      memBar β h' b') → (memBar α h b).map (MulAut.conj (mkQ n (ofPerm σ))).toMonoidHom =
        memBar β h' b' := by
    intro b b' hle
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hle x hx
    · rw [card_conj_memBar hn, natCard_memBar hn]
  rcases conj_S4 c with ⟨hK, hS⟩ | ⟨hK, hS⟩
  · refine ⟨false, fun b => ?_⟩
    cases b
    · refine fin _ _ fun x hx => ?_
      obtain ⟨k, hk, rfl⟩ := mem_memBar_false.mp hx
      rw [img]
      exact mem_memBar_false.mpr ⟨_, hS k hk, rfl⟩
    · refine fin _ _ fun x hx => ?_
      obtain ⟨k, hk, rfl⟩ := mem_memBar_true.mp hx
      rw [img]
      exact mem_memBar_true.mpr ⟨_, hK k hk, rfl⟩
  · refine ⟨true, fun b => ?_⟩
    cases b
    · refine fin _ _ fun x hx => ?_
      obtain ⟨k, hk, rfl⟩ := mem_memBar_false.mp hx
      rw [img]
      exact mem_memBar_true.mpr ⟨_, hS k hk, rfl⟩
    · refine fin _ _ fun x hx => ?_
      obtain ⟨k, hk, rfl⟩ := mem_memBar_true.mp hx
      rw [img]
      exact mem_memBar_false.mpr ⟨_, hK k hk, rfl⟩

theorem conj_memBar_flip (hn : 5 ≤ n) {α : Finset (Fin n)} (h : α.card = 4) {j : Fin n} (hj : j ∉ α)
    (b : Bool) :
    (memBar α h b).map (MulAut.conj (mkQ n (twinVec (emb α h) j))).toMonoidHom = memBar α h (!b) := by
  have hj' : j ∉ Set.range (emb α h) := by rw [range_emb]; exact hj
  have h1 : (memBar α h true).map (MulAut.conj (mkQ n (twinVec (emb α h) j))).toMonoidHom =
      memBar α h false := by
    show ((memK (emb α h)).map (mkQ n)).map _ = (memKStar (emb α h)).map (mkQ n)
    rw [← map_conj_memK (emb α h) hj', Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hsq : mkQ n (twinVec (emb α h) j) * mkQ n (twinVec (emb α h) j) = 1 := by
    rw [← map_mul, twinVec_mul_self, map_one]
  have hinv : (MulAut.conj (mkQ n (twinVec (emb α h) j))).toMonoidHom.comp
      (MulAut.conj (mkQ n (twinVec (emb α h) j))).toMonoidHom = MonoidHom.id _ := by
    refine MonoidHom.ext fun x => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply,
      MonoidHom.id_apply]
    have h3 : (mkQ n (twinVec (emb α h) j))⁻¹ = mkQ n (twinVec (emb α h) j) :=
      inv_eq_of_mul_eq_one_right hsq
    rw [h3]
    calc _ = (mkQ n (twinVec (emb α h) j) * mkQ n (twinVec (emb α h) j)) * x *
          (mkQ n (twinVec (emb α h) j) * mkQ n (twinVec (emb α h) j)) := by group
      _ = x := by rw [hsq]; group
  cases b
  · have := congrArg (Subgroup.map (MulAut.conj (mkQ n (twinVec (emb α h) j))).toMonoidHom) h1
    rw [Subgroup.map_map, hinv, Subgroup.map_id] at this
    exact this.symm
  · exact h1

theorem exists_even_perm (hn : 5 ≤ n) {α β : Finset (Fin n)} (h : α.card = 4) (h' : β.card = 4) :
    ∃ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ = 1 ∧ ∀ x ∈ α, σ x ∈ β := by
  classical
  have hc : α.card = β.card := h.trans h'.symm
  let e : {x // x ∈ α} ≃ {x // x ∈ β} := Finset.equivOfCardEq hc
  set σ₀ : Equiv.Perm (Fin n) := Equiv.extendSubtype e with hσ₀
  have hmap : ∀ x ∈ α, σ₀ x ∈ β := by
    intro x hx
    rw [hσ₀, Equiv.extendSubtype_apply_of_mem e x hx]
    exact (e ⟨x, hx⟩).2
  by_cases hs : Equiv.Perm.sign σ₀ = 1
  · exact ⟨σ₀, hs, hmap⟩
  · have hcard2 : 1 < α.card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard2
    refine ⟨σ₀ * Equiv.swap a b, ?_, fun x hx => ?_⟩
    · rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ₀) with h1 | h1
      · exact absurd h1 hs
      · rw [h1]; decide
    · have : Equiv.swap a b x ∈ α := by
        by_cases hxa : x = a
        · rw [hxa, Equiv.swap_apply_left]; exact hb
        · by_cases hxb : x = b
          · rw [hxb, Equiv.swap_apply_right]; exact ha
          · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]; exact hx
      exact hmap _ this

theorem exists_local {ι ι' : Fin 4 ↪ Fin n} (σ : Equiv.Perm (Fin n))
    (h : ∀ i, σ (ι i) ∈ Set.range ι') : ∃ c : Equiv.Perm (Fin 4), ∀ i, σ (ι i) = ι' (c i) := by
  choose c hc using h
  have hinj : Function.Injective c := fun i j hij => by
    apply ι.injective
    apply σ.injective
    rw [← hc i, ← hc j, hij]
  exact ⟨Equiv.ofBijective c (Finite.injective_iff_bijective.mp hinj), fun i => (hc i).symm⟩

theorem exists_conj_label (hn : 5 ≤ n) {α β : Finset (Fin n)} (h : α.card = 4) (h' : β.card = 4)
    (b c : Bool) : ∃ w ∈ aeSub n,
      (memBar α h b).map (MulAut.conj (mkQ n w)).toMonoidHom = memBar β h' c := by
  classical
  obtain ⟨σ, hσs, hσ⟩ := exists_even_perm hn h h'
  have hmem : ∀ i, σ (emb α h i) ∈ Set.range (emb β h') := by
    intro i
    rw [range_emb]
    apply hσ
    have : emb α h i ∈ Set.range (emb α h) := Set.mem_range_self i
    rw [range_emb] at this
    exact this
  obtain ⟨c0, hc0⟩ := exists_local σ hmem
  have hemb : (emb α h).trans σ.toEmbedding = c0.toEmbedding.trans (emb β h') :=
    Function.Embedding.ext fun i => hc0 i
  obtain ⟨e, he⟩ := conj_memBar_perm hn σ c0 hemb
  have hσW : ofPerm σ ∈ aeSub n :=
    (ofPerm_mem_aeSubOver (A := ⊤) (Subgroup.mem_top σ) hσs).1
  by_cases hbc : xor b e = c
  · exact ⟨ofPerm σ, hσW, by rw [he b, hbc]⟩
  · obtain ⟨j, hj⟩ : ∃ j : Fin n, j ∉ β := by
      by_contra hcon
      push Not at hcon
      have : (Finset.univ : Finset (Fin n)) ⊆ β := fun x _ => hcon x
      have h1 := Finset.card_le_card this
      rw [Finset.card_univ, Fintype.card_fin, h'] at h1
      omega
    have hflip := conj_memBar_flip hn h' hj (xor b e)
    have hc' : (!xor b e) = c := by
      revert hbc
      cases c <;> cases (xor b e) <;> simp
    refine ⟨twinVec (emb β h') j * ofPerm σ, ?_, ?_⟩
    · refine (aeSub n).mul_mem ?_ hσW
      exact (twinVec_mem (emb β h') (by rw [range_emb]; exact hj) ⊤).1
    · have hcomp : (MulAut.conj (mkQ n (twinVec (emb β h') j * ofPerm σ))).toMonoidHom =
          (MulAut.conj (mkQ n (twinVec (emb β h') j))).toMonoidHom.comp
            (MulAut.conj (mkQ n (ofPerm σ))).toMonoidHom := by
        rw [map_mul]
        refine MonoidHom.ext fun x => ?_
        simp [MulAut.conj_apply, mul_assoc]
      rw [hcomp, ← Subgroup.map_map, he b, hflip, hc']

end AE5

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
