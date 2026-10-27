module

public import CFSG.ClassicalInvolution.Q3.AE.Conj
public import CFSG.ClassicalInvolution.Q3.AE.PermElt
public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S.CertB

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr

variable {n : ℕ}

theorem eq_ofVec_mul_ofPerm (a : Wr n) : a = ofVec a.vec * ofPerm a.perm := by
  refine Wr.ext (funext fun i => ?_) (one_mul a.perm).symm
  show a.vec i = a.vec i + 0
  rw [add_zero]

theorem embed_trans_perm (ι : Fin 4 ↪ Fin n) (σ : Equiv.Perm (Fin n)) (k : Wr 4) :
    embed (ι.trans σ.toEmbedding) k = ofPerm σ * embed ι k * (ofPerm σ)⁻¹ := by
  classical
  have hr : ∀ x, x ∈ Set.range (ι.trans σ.toEmbedding) ↔ σ.symm x ∈ Set.range ι := by
    intro x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, by simp⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, by simp [hi]⟩
  refine Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
  · rw [ofPerm_conj_vec, embed_vec, embed_vec]
    by_cases hx : x ∈ Set.range (ι.trans σ.toEmbedding)
    · obtain ⟨i, rfl⟩ := hx
      have e : σ.symm ((ι.trans σ.toEmbedding) i) = ι i := by simp
      rw [e, embedVec_apply, embedVec_apply]
    · rw [embedVec_of_not_mem _ _ hx, embedVec_of_not_mem _ _ (fun h => hx ((hr x).2 h))]
  · rw [ofPerm_conj_perm, embed_perm, embed_perm, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    by_cases hx : x ∈ Set.range (ι.trans σ.toEmbedding)
    · obtain ⟨i, rfl⟩ := hx
      have e : σ⁻¹ ((ι.trans σ.toEmbedding) i) = ι i := by simp [Equiv.Perm.inv_def]
      rw [e, embedPerm_apply, embedPerm_apply]
      rfl
    · have hx' : σ⁻¹ x ∉ Set.range ι := fun h => hx ((hr x).2 h)
      rw [embedPerm_of_not_mem _ _ hx, embedPerm_of_not_mem _ _ hx']
      simp

theorem embed_perm_trans (c : Equiv.Perm (Fin 4)) (ι : Fin 4 ↪ Fin n) (k : Wr 4) :
    embed (c.toEmbedding.trans ι) k = embed ι (ofPerm c * k * (ofPerm c)⁻¹) := by
  classical
  have hr : Set.range (c.toEmbedding.trans ι) = Set.range ι := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨c i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨c.symm i, by simp⟩
  have hj : ∀ j, ι j = (c.toEmbedding.trans ι) (c.symm j) := fun j => by simp
  refine Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
  · rw [embed_vec, embed_vec]
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨j, rfl⟩ := hx
      rw [embedVec_apply, ofPerm_conj_vec, hj j, embedVec_apply]
    · rw [embedVec_of_not_mem _ _ hx, embedVec_of_not_mem _ _ (hr ▸ hx)]
  · rw [embed_perm, embed_perm]
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨j, rfl⟩ := hx
      rw [embedPerm_apply, ofPerm_conj_perm, hj j, embedPerm_apply]
      simp [Equiv.Perm.inv_def]
    · rw [embedPerm_of_not_mem _ _ hx, embedPerm_of_not_mem _ _ (hr ▸ hx)]

theorem ofVec_conj_embed (v : Fin n → ZMod 2) (ι : Fin 4 ↪ Fin n) (k : Wr 4) :
    ofVec v * embed ι k * (ofVec v)⁻¹ =
      embed ι (ofVec (fun i => v (ι i)) * k * (ofVec fun i => v (ι i))⁻¹) := by
  classical
  have hv : ∀ (u : Fin n → ZMod 2) (a : Wr n) (x : Fin n),
      (ofVec u * a * (ofVec u)⁻¹).vec x = u x + a.vec x + u (a.perm.symm x) := fun _ _ _ => rfl
  have hv4 : ∀ (u : Fin 4 → ZMod 2) (a : Wr 4) (x : Fin 4),
      (ofVec u * a * (ofVec u)⁻¹).vec x = u x + a.vec x + u (a.perm.symm x) := fun _ _ _ => rfl
  have hp : ∀ (u : Fin n → ZMod 2) (a : Wr n), (ofVec u * a * (ofVec u)⁻¹).perm = a.perm :=
    fun u a => by
      show 1 * a.perm * (1 : Equiv.Perm (Fin n))⁻¹ = a.perm
      rw [inv_one, mul_one, one_mul]
  have hp4 : ∀ (u : Fin 4 → ZMod 2) (a : Wr 4), (ofVec u * a * (ofVec u)⁻¹).perm = a.perm :=
    fun u a => by
      show 1 * a.perm * (1 : Equiv.Perm (Fin 4))⁻¹ = a.perm
      rw [inv_one, mul_one, one_mul]
  refine Wr.ext (funext fun x => ?_) ?_
  · rw [hv, embed_vec, embed_vec, embed_perm]
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      rw [embedVec_apply, embedVec_apply, embedPerm_symm_apply, hv4]
    · rw [embedVec_of_not_mem _ _ hx, embedVec_of_not_mem _ _ hx, embedPerm_symm_of_not_mem _ _ hx,
        add_zero]
      exact zmod_two_add_self _
  · rw [hp, embed_perm, embed_perm, hp4]

theorem exists_perm_trans_eq {ι ι' : Fin 4 ↪ Fin n} (h : Set.range ι = Set.range ι') :
    ∃ c : Equiv.Perm (Fin 4), c.toEmbedding.trans ι' = ι := by
  set e : Set.range ι ≃ Set.range ι' := Equiv.subtypeEquivRight fun x => by rw [h]
  refine ⟨(ι.toEquivRange.trans e).trans ι'.toEquivRange.symm, Function.Embedding.ext fun i => ?_⟩
  exact congrArg Subtype.val (ι'.toEquivRange.apply_symm_apply (e (ι.toEquivRange i)))

@[expose] def memList (b : Bool) : List (Wr 4) := bif b then kList else kStarList

theorem perm_conj_memList : ∀ (c : Equiv.Perm (Fin 4)) (b : Bool), ∃ b' : Bool,
    ∀ k ∈ memList b, ofPerm c * k * (ofPerm c)⁻¹ ∈ memList b' := by
  decide +kernel

theorem vec_conj_memList : ∀ (u : Fin 4 → ZMod 2) (b : Bool), ∃ b' : Bool,
    ∀ k ∈ memList b, ofVec u * k * (ofVec u)⁻¹ ∈ memList b' := by
  decide +kernel

theorem mem_memAt {α : Finset (Fin n)} {h : α.card = 4} {b : Bool} {x : Wr n} :
    x ∈ memAt α h b ↔ ∃ k ∈ memList b, embed (emb α h) k = x := by
  cases b <;> exact Iff.rfl

theorem card_map_emb (σ : Equiv.Perm (Fin n)) {α : Finset (Fin n)} (h : α.card = 4) :
    (α.map σ.toEmbedding).card = 4 := by
  rw [Finset.card_map, h]

theorem map_conj_memAt_le (v : Fin n → ZMod 2) (σ : Equiv.Perm (Fin n)) (α : Finset (Fin n))
    (h : α.card = 4) (b : Bool) : ∃ c : Bool,
      (memAt α h b).map (MulAut.conj (ofVec v * ofPerm σ)).toMonoidHom ≤
        memAt (α.map σ.toEmbedding) (card_map_emb σ h) c := by
  classical
  set ι := emb α h
  set ι' := emb (α.map σ.toEmbedding) (card_map_emb σ h)
  have hr : Set.range (ι.trans σ.toEmbedding) = Set.range ι' := by
    rw [range_emb]
    ext x
    simp only [Set.mem_range, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
      Finset.coe_map, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨ι i, ?_, rfl⟩
      have : ι i ∈ Set.range ι := Set.mem_range_self i
      rwa [range_emb] at this
    · rintro ⟨y, hy, rfl⟩
      have : y ∈ Set.range ι := by rw [range_emb]; exact hy
      obtain ⟨i, rfl⟩ := this
      exact ⟨i, rfl⟩
  obtain ⟨c, hc⟩ := exists_perm_trans_eq hr
  obtain ⟨b', hb'⟩ := perm_conj_memList c b
  obtain ⟨b'', hb''⟩ := vec_conj_memList (fun i => v (ι' i)) b'
  refine ⟨b'', ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨k, hk, rfl⟩ := mem_memAt.mp hx
  refine mem_memAt.mpr ⟨_, hb'' _ (hb' k hk), ?_⟩
  show _ = ofVec v * ofPerm σ * embed ι k * (ofVec v * ofPerm σ)⁻¹
  rw [← ofVec_conj_embed, ← embed_perm_trans, hc, embed_trans_perm]
  group

theorem map_conj_memAt (v : Fin n → ZMod 2) (σ : Equiv.Perm (Fin n)) (α : Finset (Fin n))
    (h : α.card = 4) (b : Bool) : ∃ c : Bool,
      (memAt α h b).map (MulAut.conj (ofVec v * ofPerm σ)).toMonoidHom =
        memAt (α.map σ.toEmbedding) (card_map_emb σ h) c := by
  obtain ⟨c, hc⟩ := map_conj_memAt_le v σ α h b
  refine ⟨c, Subgroup.eq_of_le_of_card_ge hc ?_⟩
  rw [natCard_memAt, Subgroup.card_map_of_injective (MulAut.conj _).injective, natCard_memAt]

theorem conjSub_mkQ_map (g : Wr n) (H : Subgroup (Wr n)) :
    conjSub (mkQ n g) (H.map (mkQ n)) = (H.map (MulAut.conj g).toMonoidHom).map (mkQ n) := by
  rw [conjSub, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem conjSub_memBar (g : Wr n) (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    ∃ c : Bool, conjSub (mkQ n g) (memBar α h b) =
      memBar (α.map g.perm.toEmbedding) (card_map_emb g.perm h) c := by
  obtain ⟨c, hc⟩ := map_conj_memAt g.vec g.perm α h b
  refine ⟨c, ?_⟩
  rw [memBar, conjSub_mkQ_map, show MulAut.conj g = MulAut.conj (ofVec g.vec * ofPerm g.perm) from
    congrArg _ (eq_ofVec_mul_ofPerm g), hc]
  rfl

open scoped Pointwise in
theorem exists_alternating_map (α₀ α : Finset (Fin 8)) (h₀ : α₀.card = 4) (h : α.card = 4) :
    ∃ σ ∈ alternatingGroup (Fin 8), α₀.map σ.toEmbedding = α := by
  classical
  haveI := Set.powersetCard.isPretransitive_alternatingGroup (α := Fin 8) (n := 4)
    (by simp)
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 8))
    (⟨α₀, h₀⟩ : Set.powersetCard (Fin 8) 4) ⟨α, h⟩
  refine ⟨σ, σ.2, ?_⟩
  have e : σ • α₀ = α := congrArg Subtype.val hσ
  rw [← e, Finset.map_eq_image, Finset.smul_finset_def]
  rfl

theorem exists_conjSub_memBar (α₀ : Finset (Fin 8)) (h₀ : α₀.card = 4) (b₀ : Bool)
    (α : Finset (Fin 8)) (h : α.card = 4) (b : Bool) :
    ∃ g ∈ (aeSub 8).map (mkQ 8), memBar α h b = conjSub g (memBar α₀ h₀ b₀) := by
  obtain ⟨σ, hσA, hσ⟩ := exists_alternating_map α₀ α h₀ h
  have hσ8 : ofPerm σ ∈ aeSub 8 := mem_aeSub.mpr ⟨by simp [wsum, ofPerm],
    Equiv.Perm.mem_alternatingGroup.mp hσA⟩
  obtain ⟨c, hc⟩ := conjSub_memBar (ofPerm σ) α₀ h₀ b₀
  have hc' : conjSub (mkQ 8 (ofPerm σ)) (memBar α₀ h₀ b₀) = memBar α h c := by
    rw [hc]
    congr 1
  obtain ⟨w, hw, hwe⟩ := exists_conj_memBar (by norm_num) α h ⊤
  have hw8 : mkQ 8 w ∈ (aeSub 8).map (mkQ 8) := ⟨w, hw.1, rfl⟩
  have hs8 : mkQ 8 (ofPerm σ) ∈ (aeSub 8).map (mkQ 8) := ⟨_, hσ8, rfl⟩
  have hwe' : conjSub (mkQ 8 w) (memBar α h true) = memBar α h false := hwe
  by_cases hcb : c = b
  · exact ⟨_, hs8, by rw [hc', hcb]⟩
  · cases b <;> cases c
    · exact absurd rfl hcb
    · refine ⟨mkQ 8 w * mkQ 8 (ofPerm σ), Subgroup.mul_mem _ hw8 hs8, ?_⟩
      rw [conjSub_mul, hc', hwe']
    · refine ⟨(mkQ 8 w)⁻¹ * mkQ 8 (ofPerm σ), Subgroup.mul_mem _ (Subgroup.inv_mem _ hw8) hs8, ?_⟩
      rw [conjSub_mul, hc', ← hwe', conjSub_inv_conjSub]
    · exact absurd rfl hcb

theorem emb_apply_of_strictMono {α : Finset (Fin n)} (h : α.card = 4) {f : Fin 4 → Fin n}
    (hf : ∀ i, f i ∈ α) (hmono : StrictMono f) (i : Fin 4) : emb α h i = f i := by
  rw [Finset.orderEmbOfFin_unique h hf hmono]
  rfl

theorem embed_eq_of_apply {ι : Fin 4 ↪ Fin n} {k : Wr 4} {y : Wr n}
    (h1 : ∀ i, y.vec (ι i) = k.vec i) (h2 : ∀ i, y.perm (ι i) = ι (k.perm i))
    (h3 : ∀ x, x ∉ Set.range ι → y.vec x = 0 ∧ y.perm x = x) : embed ι k = y := by
  classical
  refine Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
  · rw [embed_vec]
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      rw [embedVec_apply, h1]
    · rw [embedVec_of_not_mem _ _ hx, (h3 x hx).1]
  · rw [embed_perm]
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      rw [embedPerm_apply, h2]
    · rw [embedPerm_of_not_mem _ _ hx, (h3 x hx).2]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S.CertB
