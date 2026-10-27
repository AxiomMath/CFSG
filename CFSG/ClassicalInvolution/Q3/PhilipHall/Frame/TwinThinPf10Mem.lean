module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Act
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Char

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {n : ℕ}

theorem loc_perm : ∀ τ : Equiv.Perm (Fin 4),
    ((∀ k ∈ kList, ofPerm τ * k * (ofPerm τ)⁻¹ ∈ kList) ∧
      (∀ k ∈ kStarList, ofPerm τ * k * (ofPerm τ)⁻¹ ∈ kStarList)) ∨
    ((∀ k ∈ kList, ofPerm τ * k * (ofPerm τ)⁻¹ ∈ kStarList) ∧
      (∀ k ∈ kStarList, ofPerm τ * k * (ofPerm τ)⁻¹ ∈ kList)) := by decide +kernel

theorem mem_memBar_true {α : Finset (Fin n)} {hα : α.card = 4} {x : AEQ n} :
    x ∈ memBar α hα true ↔ ∃ k ∈ kList, x = mkQ n (embed (emb α hα) k) := by
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact mkQ_embed_mem_true α hα hk

theorem mem_memBar_false {α : Finset (Fin n)} {hα : α.card = 4} {x : AEQ n} :
    x ∈ memBar α hα false ↔ ∃ k ∈ kStarList, x = mkQ n (embed (emb α hα) k) := by
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact mkQ_embed_mem_false α hα hk

theorem map_conj_eq_of_le (hn : 5 ≤ n) (s : AEQ n) {α β : Finset (Fin n)} {hα : α.card = 4}
    {hβ : β.card = 4} {a b : Bool}
    (h : (memBar α hα a).map (MulAut.conj s).toMonoidHom ≤ memBar β hβ b) :
    (memBar α hα a).map (MulAut.conj s).toMonoidHom = memBar β hβ b := by
  refine Subgroup.eq_of_le_of_card_ge h ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj s).injective, natCard_memBar hn,
    natCard_memBar hn]

theorem conj_mkQ_embed_vec (β : Finset (Fin n)) (hβ : β.card = 4) (u : Fin n → ZMod 2)
    (k : Wr 4) :
    mkQ n (ofVec u) * mkQ n (embed (emb β hβ) k) * (mkQ n (ofVec u))⁻¹ =
      mkQ n (embed (emb β hβ) (ofVec (fun i => u (emb β hβ i)) * k *
        (ofVec (fun i => u (emb β hβ i)))⁻¹)) := by
  rw [← map_inv, ← map_mul, ← map_mul, conj_embed_vec]

theorem conj_memBar_vec_even (hn : 5 ≤ n) (β : Finset (Fin n)) (hβ : β.card = 4) (c : Bool)
    (u : Fin n → ZMod 2) (hu : ∑ i, u (emb β hβ i) = 0) :
    (memBar β hβ c).map (MulAut.conj (mkQ n (ofVec u))).toMonoidHom = memBar β hβ c := by
  have hev := loc_twin_even (fun i => u (emb β hβ i)) hu
  refine map_conj_eq_of_le hn _ ?_
  rintro _ ⟨x, hx, rfl⟩
  cases c
  · obtain ⟨k, hk, rfl⟩ := mem_memBar_false.mp hx
    show mkQ n (ofVec u) * _ * (mkQ n (ofVec u))⁻¹ ∈ _
    rw [conj_mkQ_embed_vec]
    exact mkQ_embed_mem_false β hβ (hev.2 k hk)
  · obtain ⟨k, hk, rfl⟩ := mem_memBar_true.mp hx
    show mkQ n (ofVec u) * _ * (mkQ n (ofVec u))⁻¹ ∈ _
    rw [conj_mkQ_embed_vec]
    exact mkQ_embed_mem_true β hβ (hev.1 k hk)

theorem conj_memBar_vec_odd (hn : 5 ≤ n) (β : Finset (Fin n)) (hβ : β.card = 4) (c : Bool)
    (u : Fin n → ZMod 2) (hu : ∑ i, u (emb β hβ i) = 1) :
    (memBar β hβ c).map (MulAut.conj (mkQ n (ofVec u))).toMonoidHom = memBar β hβ (!c) := by
  have hod := loc_twin_odd (fun i => u (emb β hβ i)) hu
  refine map_conj_eq_of_le hn _ ?_
  rintro _ ⟨x, hx, rfl⟩
  cases c
  · obtain ⟨k, hk, rfl⟩ := mem_memBar_false.mp hx
    show mkQ n (ofVec u) * _ * (mkQ n (ofVec u))⁻¹ ∈ _
    rw [conj_mkQ_embed_vec]
    exact mkQ_embed_mem_true β hβ (hod.2 k hk)
  · obtain ⟨k, hk, rfl⟩ := mem_memBar_true.mp hx
    show mkQ n (ofVec u) * _ * (mkQ n (ofVec u))⁻¹ ∈ _
    rw [conj_mkQ_embed_vec]
    exact mkQ_embed_mem_false β hβ (hod.1 k hk)

theorem card_map_perm (p : Equiv.Perm (Fin n)) {β : Finset (Fin n)} (hβ : β.card = 4) :
    (β.map p.toEmbedding).card = 4 := by rw [Finset.card_map, hβ]

theorem exists_local_perm (p : Equiv.Perm (Fin n)) {β : Finset (Fin n)} (hβ : β.card = 4) :
    ∃ τ : Equiv.Perm (Fin 4), ∀ i, p (emb β hβ i) = emb (β.map p.toEmbedding) (card_map_perm p hβ)
      (τ i) := by
  classical
  set ι := emb β hβ with hι
  set ι' := emb (β.map p.toEmbedding) (card_map_perm p hβ) with hι'
  have hmem : ∀ i, p (ι i) ∈ Set.range ι' := fun i => by
    rw [hι', range_emb]
    simp only [Finset.coe_map, Equiv.coe_toEmbedding, Set.mem_image, Finset.mem_coe]
    refine ⟨ι i, ?_, rfl⟩
    have : ι i ∈ Set.range ι := Set.mem_range_self i
    rw [hι, range_emb] at this
    exact this
  let τf : Fin 4 → Fin 4 := fun i => ι'.toEquivRange.symm ⟨p (ι i), hmem i⟩
  have hτf : ∀ i, ι' (τf i) = p (ι i) := fun i => by
    have := ι'.toEquivRange.apply_symm_apply ⟨p (ι i), hmem i⟩
    exact congrArg Subtype.val this
  have hinj : Function.Injective τf := fun i j h => by
    apply ι.injective
    apply p.injective
    rw [← hτf, ← hτf, h]
  refine ⟨Equiv.ofBijective τf (Function.Injective.bijective_of_finite hinj), fun i => ?_⟩
  exact (hτf i).symm

theorem conj_memBar_perm (hn : 5 ≤ n) (p : Equiv.Perm (Fin n)) (β : Finset (Fin n))
    (hβ : β.card = 4) (c : Bool) :
    ∃ c' : Bool, (memBar β hβ c).map (MulAut.conj (mkQ n (ofPerm p))).toMonoidHom =
      memBar (β.map p.toEmbedding) (card_map_perm p hβ) c' := by
  obtain ⟨τ, hτ⟩ := exists_local_perm p hβ
  have key : ∀ k : Wr 4, mkQ n (ofPerm p) * mkQ n (embed (emb β hβ) k) * (mkQ n (ofPerm p))⁻¹ =
      mkQ n (embed (emb (β.map p.toEmbedding) (card_map_perm p hβ)) (ofPerm τ * k * (ofPerm τ)⁻¹)) :=
    fun k => by
    rw [← map_inv, ← map_mul, ← map_mul, conj_embed_perm _ _ p τ hτ]
  rcases loc_perm τ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨c, map_conj_eq_of_le hn _ ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    cases c
    · obtain ⟨k, hk, rfl⟩ := mem_memBar_false.mp hx
      show mkQ n (ofPerm p) * _ * (mkQ n (ofPerm p))⁻¹ ∈ _
      rw [key]
      exact mkQ_embed_mem_false _ _ (h2 k hk)
    · obtain ⟨k, hk, rfl⟩ := mem_memBar_true.mp hx
      show mkQ n (ofPerm p) * _ * (mkQ n (ofPerm p))⁻¹ ∈ _
      rw [key]
      exact mkQ_embed_mem_true _ _ (h1 k hk)
  · refine ⟨!c, map_conj_eq_of_le hn _ ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    cases c
    · obtain ⟨k, hk, rfl⟩ := mem_memBar_false.mp hx
      show mkQ n (ofPerm p) * _ * (mkQ n (ofPerm p))⁻¹ ∈ _
      rw [key]
      exact mkQ_embed_mem_true _ _ (h2 k hk)
    · obtain ⟨k, hk, rfl⟩ := mem_memBar_true.mp hx
      show mkQ n (ofPerm p) * _ * (mkQ n (ofPerm p))⁻¹ ∈ _
      rw [key]
      exact mkQ_embed_mem_false _ _ (h1 k hk)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10
