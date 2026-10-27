module

public import CFSG.ClassicalInvolution.Q3.TL3T36

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr

variable {n : ℕ}

theorem ofPerm_conj_embed_trans (σ : Equiv.Perm (Fin n)) (ι : Fin 4 ↪ Fin n) (a : Wr 4) :
    ofPerm σ * embed ι a * (ofPerm σ)⁻¹ = embed (ι.trans σ.toEmbedding) a := by
  classical
  have hr : ∀ x, σ.symm x ∈ Set.range ι ↔ x ∈ Set.range (ι.trans σ.toEmbedding) := by
    intro x
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      rw [Function.Embedding.trans_apply, hi]
      exact σ.apply_symm_apply x
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      rw [← hi, Function.Embedding.trans_apply]
      exact (σ.symm_apply_apply (ι i)).symm
  have hx' : ∀ i, (ι.trans σ.toEmbedding) i = σ (ι i) := fun i => rfl
  refine Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
  · rw [ofPerm_conj_vec, embed_vec, embed_vec]
    by_cases hx : σ.symm x ∈ Set.range ι
    · obtain ⟨i, hi⟩ := hx
      have e : x = (ι.trans σ.toEmbedding) i := by
        rw [hx', hi]
        exact (σ.apply_symm_apply x).symm
      rw [← hi, embedVec_apply, e, embedVec_apply]
    · rw [embedVec_of_not_mem ι _ hx, embedVec_of_not_mem _ _ (fun h => hx ((hr x).mpr h))]
  · rw [ofPerm_conj_perm, embed_perm, embed_perm]
    show σ (embedPerm ι a.perm (σ⁻¹ x)) = embedPerm (ι.trans σ.toEmbedding) a.perm x
    by_cases hx : σ.symm x ∈ Set.range ι
    · obtain ⟨i, hi⟩ := hx
      have e : x = (ι.trans σ.toEmbedding) i := by
        rw [hx', hi]
        exact (σ.apply_symm_apply x).symm
      rw [Equiv.Perm.inv_def, ← hi, embedPerm_apply, e, embedPerm_apply, hx']
    · rw [Equiv.Perm.inv_def, embedPerm_of_not_mem ι _ hx, Equiv.apply_symm_apply,
        embedPerm_of_not_mem _ _ (fun h => hx ((hr x).mpr h))]

theorem embed_perm_trans (ρ : Equiv.Perm (Fin 4)) (ι : Fin 4 ↪ Fin n) (a : Wr 4) :
    embed (ρ.toEmbedding.trans ι) a = embed ι (ofPerm ρ * a * (ofPerm ρ)⁻¹) := by
  classical
  have hr : Set.range (ρ.toEmbedding.trans ι) = Set.range ι := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨ρ i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨ρ.symm i, by
        rw [Function.Embedding.trans_apply]
        exact congrArg ι (ρ.apply_symm_apply i)⟩
  have hj : ∀ j, ι j = (ρ.toEmbedding.trans ι) (ρ.symm j) := fun j => by
    rw [Function.Embedding.trans_apply]
    exact congrArg ι (ρ.apply_symm_apply j).symm
  refine Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
  · rw [embed_vec, embed_vec]
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨j, rfl⟩ := hx
      rw [embedVec_apply, ofPerm_conj_vec, hj, embedVec_apply]
    · rw [embedVec_of_not_mem ι _ hx, embedVec_of_not_mem _ _ (by rwa [hr])]
  · rw [embed_perm, embed_perm]
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨j, rfl⟩ := hx
      rw [embedPerm_apply, ofPerm_conj_perm, hj, embedPerm_apply, Function.Embedding.trans_apply]
      rfl
    · rw [embedPerm_of_not_mem ι _ hx, embedPerm_of_not_mem _ _ (by rwa [hr])]

theorem perm_conj_kList : ∀ ρ : Equiv.Perm (Fin 4),
    (∀ k ∈ kList, ofPerm ρ * k * (ofPerm ρ)⁻¹ ∈ kList) ∨
      (∀ k ∈ kList, ofPerm ρ * k * (ofPerm ρ)⁻¹ ∈ kStarList) := by
  decide +kernel

theorem perm_conj_kStarList : ∀ ρ : Equiv.Perm (Fin 4),
    (∀ k ∈ kStarList, ofPerm ρ * k * (ofPerm ρ)⁻¹ ∈ kStarList) ∨
      (∀ k ∈ kStarList, ofPerm ρ * k * (ofPerm ρ)⁻¹ ∈ kList) := by
  decide +kernel

theorem natCard_kQ : Nat.card kQ = 8 := by
  have := natCard_memK (Function.Embedding.refl (Fin 4))
  rwa [memK, Subgroup.card_map_of_injective (embed_injective _)] at this

theorem natCard_kQStar : Nat.card kQStar = 8 := by
  have := natCard_memKStar (Function.Embedding.refl (Fin 4))
  rwa [memKStar, Subgroup.card_map_of_injective (embed_injective _)] at this

theorem exists_perm_conj_local (ρ : Equiv.Perm (Fin 4)) (b : Bool) :
    ∃ b' : Bool, (bif b then kQ else kQStar).map (MulAut.conj (ofPerm ρ)).toMonoidHom =
      bif b' then kQ else kQStar := by
  have hcard : ∀ b'' : Bool, Nat.card ↥(bif b'' then kQ else kQStar) = 8 := by
    intro b''
    cases b''
    · exact natCard_kQStar
    · exact natCard_kQ
  have hmap : ∀ (S T : Subgroup (Wr 4)), Nat.card S = 8 → Nat.card T = 8 →
      (∀ k ∈ S, ofPerm ρ * k * (ofPerm ρ)⁻¹ ∈ T) →
      S.map (MulAut.conj (ofPerm ρ)).toMonoidHom = T := by
    intro S T hS hT h
    have hle : S.map (MulAut.conj (ofPerm ρ)).toMonoidHom ≤ T := by
      rintro _ ⟨k, hk, rfl⟩
      exact h k hk
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj (ofPerm ρ)).injective, hS, hT]
  cases b
  · rcases perm_conj_kStarList ρ with h | h
    · exact ⟨false, hmap _ _ (hcard false) (hcard false) fun k hk => h k hk⟩
    · exact ⟨true, hmap _ _ (hcard false) (hcard true) fun k hk => h k hk⟩
  · rcases perm_conj_kList ρ with h | h
    · exact ⟨true, hmap _ _ (hcard true) (hcard true) fun k hk => h k hk⟩
    · exact ⟨false, hmap _ _ (hcard true) (hcard false) fun k hk => h k hk⟩

theorem exists_perm_trans_eq (ι κ : Fin 4 ↪ Fin n) (h : Set.range ι = Set.range κ) :
    ∃ ρ : Equiv.Perm (Fin 4), ι = ρ.toEmbedding.trans κ := by
  classical
  have hmem : ∀ i, ι i ∈ Set.range κ := fun i => h ▸ Set.mem_range_self i
  set f : Fin 4 → Fin 4 := fun i => (hmem i).choose with hf
  have hfi : ∀ i, κ (f i) = ι i := fun i => (hmem i).choose_spec
  have hinj : Function.Injective f := fun i j hij => ι.injective (by rw [← hfi, ← hfi, hij])
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), ?_⟩
  refine Function.Embedding.ext fun i => ?_
  show ι i = κ (f i)
  exact (hfi i).symm

theorem exists_conj_ofPerm_memAt (σ : Equiv.Perm (Fin n)) (α : Finset (Fin n)) (h : α.card = 4)
    (b : Bool) : ∃ b' : Bool, (memAt α h b).map (MulAut.conj (ofPerm σ)).toMonoidHom =
      memAt (α.map σ.toEmbedding) (by rw [Finset.card_map]; exact h) b' := by
  classical
  set β := α.map σ.toEmbedding with hβ
  have hβc : β.card = 4 := by rw [Finset.card_map]; exact h
  have hr : Set.range ((emb α h).trans σ.toEmbedding) = Set.range (emb β hβc) := by
    rw [range_emb]
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      have hi : emb α h i ∈ α := by
        have := Set.mem_range_self (f := emb α h) i
        rwa [range_emb] at this
      exact Finset.mem_map_of_mem _ hi
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      have hy' : y ∈ Set.range (emb α h) := by rw [range_emb]; exact hy
      obtain ⟨i, rfl⟩ := hy'
      exact ⟨i, rfl⟩
  obtain ⟨ρ, hρ⟩ := exists_perm_trans_eq _ _ hr
  obtain ⟨b', hb'⟩ := exists_perm_conj_local ρ b
  refine ⟨b', ?_⟩
  have hloc : memAt α h b = (bif b then kQ else kQStar).map (embed (emb α h)) := by
    cases b <;> rfl
  have hloc' : memAt β hβc b' = (bif b' then kQ else kQStar).map (embed (emb β hβc)) := by
    cases b' <;> rfl
  rw [hloc, hloc', ← hb', Subgroup.map_map, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun a => ?_
  show ofPerm σ * embed (emb α h) a * (ofPerm σ)⁻¹ =
    embed (emb β hβc) (ofPerm ρ * a * (ofPerm ρ)⁻¹)
  rw [ofPerm_conj_embed_trans, hρ, embed_perm_trans]

theorem exists_conj_ofPerm_memBar (σ : Equiv.Perm (Fin n)) (α : Finset (Fin n)) (h : α.card = 4)
    (b : Bool) : ∃ b' : Bool, (memBar α h b).map (MulAut.conj (mkQ n (ofPerm σ))).toMonoidHom =
      memBar (α.map σ.toEmbedding) (by rw [Finset.card_map]; exact h) b' := by
  obtain ⟨b', hb'⟩ := exists_conj_ofPerm_memAt σ α h b
  refine ⟨b', ?_⟩
  rw [memBar, memBar, ← hb', Subgroup.map_map, Subgroup.map_map]
  congr 1

@[expose] def ofPermHom (n : ℕ) : Equiv.Perm (Fin n) →* Wr n where
  toFun := ofPerm
  map_one' := ofPerm_one
  map_mul' σ τ := (ofPerm_mul σ τ).symm

@[expose] def memSpan (n : ℕ) : Subgroup (AEQ n) :=
  Subgroup.closure (⋃ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool),
    (memBar α h b : Set (AEQ n)))

theorem memBar_le_memSpan (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    memBar α h b ≤ memSpan n := fun _ hx =>
  Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨α, Set.mem_iUnion.mpr ⟨h,
    Set.mem_iUnion.mpr ⟨b, hx⟩⟩⟩)

theorem conj_ofPerm_mem_memSpan (σ : Equiv.Perm (Fin n)) {x : AEQ n} (hx : x ∈ memSpan n) :
    mkQ n (ofPerm σ) * x * (mkQ n (ofPerm σ))⁻¹ ∈ memSpan n := by
  have hle : (memSpan n).map (MulAut.conj (mkQ n (ofPerm σ))).toMonoidHom ≤ memSpan n := by
    rw [memSpan, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨α, hy⟩ := Set.mem_iUnion.mp hy
    obtain ⟨h, hy⟩ := Set.mem_iUnion.mp hy
    obtain ⟨b, hy⟩ := Set.mem_iUnion.mp hy
    obtain ⟨b', hb'⟩ := exists_conj_ofPerm_memBar σ α h b
    have hmem : (MulAut.conj (mkQ n (ofPerm σ))).toMonoidHom y ∈
        (memBar α h b).map (MulAut.conj (mkQ n (ofPerm σ))).toMonoidHom := ⟨y, hy, rfl⟩
    rw [hb'] at hmem
    exact memBar_le_memSpan _ _ _ hmem
  exact hle ⟨x, hx, rfl⟩

theorem ofVec_mul_ofPerm (a : Wr n) : ofVec a.vec * ofPerm a.perm = a := by
  refine Wr.ext (funext fun i => ?_) ?_
  · show a.vec i + (0 : ZMod 2) = a.vec i
    rw [add_zero]
  · show (1 : Equiv.Perm (Fin n)) * a.perm = a.perm
    rw [one_mul]

theorem sign_embedPerm (ι : Fin 4 ↪ Fin n) (σ : Equiv.Perm (Fin 4)) :
    Equiv.Perm.sign (embedPerm ι σ) = Equiv.Perm.sign σ := by
  classical
  unfold embedPerm
  exact Equiv.Perm.sign_extendDomain σ ι.toEquivRange

theorem sign_d₁ : Equiv.Perm.sign d₁ = 1 := by decide

theorem aeModel_le_memSpan (hn : 5 ≤ n) : TL4.aeModel n ≤ memSpan n := by
  classical
  have hvec : ∀ u : Fin n → ZMod 2, ∑ i, u i = 0 → mkQ n (ofVec u) ∈ memSpan n := fun u hu =>
    TC.Thin.mem_of_zBar_mem hn (fun δ hδ => memBar_le_memSpan δ hδ true (zBar_mem_memBar δ hδ true)) hu
  set P := (memSpan n).comap ((mkQ n).comp (ofPermHom n)) with hP
  have hmemP : ∀ σ, σ ∈ P ↔ mkQ n (ofPerm σ) ∈ memSpan n := fun σ => Iff.rfl
  have hPn : ∀ τ : Equiv.Perm (Fin n), ∀ σ ∈ P, τ * σ * τ⁻¹ ∈ P := by
    intro τ σ hσ
    rw [hmemP] at hσ ⊢
    have := conj_ofPerm_mem_memSpan τ hσ
    rwa [← map_inv, ← map_mul, ← map_mul, show (ofPerm τ)⁻¹ = ofPerm τ⁻¹ from
      inv_eq_of_mul_eq_one_right (by rw [ofPerm_mul, mul_inv_cancel, ofPerm_one]), ofPerm_mul,
      ofPerm_mul] at this
  obtain ⟨α, -, hα⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (n := 4) (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  set ι := emb α hα with hι
  obtain ⟨a, ha, hap⟩ := exists_mem_kQ_perm d₁ (by simp)
  have hd : embedPerm ι d₁ ∈ P := by
    rw [hmemP]
    have h1 : mkQ n (embed ι a) ∈ memSpan n :=
      memBar_le_memSpan α hα true ⟨embed ι a, ⟨a, ha, rfl⟩, rfl⟩
    have h2 : ofVec (embed ι a).vec * ofPerm (embedPerm ι d₁) = embed ι a := by
      rw [← hap]
      exact ofVec_mul_ofPerm (embed ι a)
    have h3 : mkQ n (ofVec (embed ι a).vec) ∈ memSpan n :=
      hvec _ (by rw [embed_vec, sum_embedVec]; exact (kList_even a ha).1)
    rw [← h2, map_mul] at h1
    have h4 := (memSpan n).mul_mem ((memSpan n).inv_mem h3) h1
    rwa [inv_mul_cancel_left] at h4
  have hs := alternatingGroup.isSimpleGroup (α := Fin n) (by rw [Nat.card_fin]; omega)
  set Q := P.subgroupOf (alternatingGroup (Fin n)) with hQ
  have hQn : Q.Normal := ⟨fun x hx g =>
    Subgroup.mem_subgroupOf.mpr (hPn g x (Subgroup.mem_subgroupOf.mp hx))⟩
  have hdA : embedPerm ι d₁ ∈ alternatingGroup (Fin n) := by
    rw [Equiv.Perm.mem_alternatingGroup, sign_embedPerm, sign_d₁]
  have hd1 : embedPerm ι d₁ ≠ 1 := by
    intro h1
    have e := embedPerm_apply ι d₁ 0
    rw [h1, Equiv.Perm.one_apply, show d₁ 0 = 1 by decide] at e
    exact absurd (ι.injective e) (by decide)
  have hQtop : Q = ⊤ := by
    refine hQn.eq_bot_or_eq_top.resolve_left fun hbot => hd1 ?_
    have : (⟨embedPerm ι d₁, hdA⟩ : alternatingGroup (Fin n)) ∈ Q :=
      Subgroup.mem_subgroupOf.mpr hd
    rw [hbot, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  rintro _ ⟨w, hw, rfl⟩
  rw [← ofVec_mul_ofPerm w, map_mul]
  refine (memSpan n).mul_mem (hvec _ hw.1) ?_
  have : (⟨w.perm, hw.2⟩ : alternatingGroup (Fin n)) ∈ Q := hQtop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

theorem vec_conj_kList_even : ∀ u : Fin 4 → ZMod 2,
    (∀ k ∈ kList, ofVec u * k * (ofVec u)⁻¹ ∈ kList) → ∑ i, u i = 0 := by
  decide +kernel

theorem ofVec_inv (v : Fin n → ZMod 2) : (ofVec v)⁻¹ = ofVec v := by
  refine Wr.ext (funext fun i => ?_) ?_
  · rfl
  · show (1 : Equiv.Perm (Fin n))⁻¹ = 1
    rw [inv_one]

theorem ofVec_conj_embed (v : Fin n → ZMod 2) (ι : Fin 4 ↪ Fin n) (a : Wr 4) :
    ofVec v * embed ι a * (ofVec v)⁻¹ = embed ι (ofVec (v ∘ ι) * a * (ofVec (v ∘ ι))⁻¹) := by
  classical
  rw [ofVec_inv, ofVec_inv]
  refine Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
  · rw [mul_vec, mul_vec, embed_vec]
    show v x + embedVec ι a.vec x + v ((embed ι a).perm.symm x) = _
    rw [embed_perm]
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      rw [embedVec_apply, embedPerm_symm_apply, embed_vec, embedVec_apply, mul_vec, mul_vec]
      rfl
    · rw [embedVec_of_not_mem ι _ hx, embedPerm_symm_of_not_mem ι _ hx, embed_vec,
        embedVec_of_not_mem ι _ hx, add_zero, zmod_two_add_self]
  · show embedPerm ι a.perm x = embedPerm ι ((1 : Equiv.Perm (Fin 4)) * a.perm * 1) x
    rw [one_mul, mul_one]

theorem eq_one_of_normalizes_memBar (hn : 5 ≤ n) (hn8 : n ≠ 8) {x : AEQ n}
    (hx : ∀ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool),
      (memBar α h b).map (MulAut.conj x).toMonoidHom = memBar α h b) : x = 1 := by
  classical
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
  change mkQ n w = 1
  have hz : ∀ (α : Finset (Fin n)) (h : α.card = 4),
      mkQ n w * zBar α h * (mkQ n w)⁻¹ = zBar α h := by
    intro α h
    have hmem : mkQ n w * zBar α h * (mkQ n w)⁻¹ ∈ memBar α h true := by
      rw [← hx α h true]
      exact ⟨zBar α h, zBar_mem_memBar α h true, rfl⟩
    have hsq : (mkQ n w * zBar α h * (mkQ n w)⁻¹) * (mkQ n w * zBar α h * (mkQ n w)⁻¹) = 1 := by
      have hz2 : zBar α h * zBar α h = 1 := by
        rw [zBar, ← map_mul, zOf, ← map_mul,
          show zQ * zQ = 1 by decide, map_one, map_one]
      calc (mkQ n w * zBar α h * (mkQ n w)⁻¹) * (mkQ n w * zBar α h * (mkQ n w)⁻¹)
          = mkQ n w * (zBar α h * zBar α h) * (mkQ n w)⁻¹ := by group
        _ = 1 := by rw [hz2, mul_one, mul_inv_cancel]
    rcases eq_of_mem_memBar_mul_self hn hmem hsq with h1 | h1
    · exfalso
      apply zBar_ne_one hn α h
      calc zBar α h = (mkQ n w)⁻¹ * (mkQ n w * zBar α h * (mkQ n w)⁻¹) * mkQ n w := by group
        _ = 1 := by rw [h1, mul_one, inv_mul_cancel]
    · exact h1
  have hσ : ∀ (α : Finset (Fin n)) (h : α.card = 4), α.map w.perm.toEmbedding = α := by
    intro α h
    have hc : (α.map w.perm.toEmbedding).card = 4 := by rw [Finset.card_map]; exact h
    apply eq_of_zBar_eq hn8 (h := hc) (h' := h)
    rw [← TC.Thin.conj_zBar_ofPerm w.perm α h hc]
    have hv : mkQ n (ofVec w.vec) * zBar α h = zBar α h * mkQ n (ofVec w.vec) :=
      TC.Thin.comm_of_mem_ker_permQ (by rw [TC.Thin.permQ_mkQ]; rfl)
        (by rw [zBar, TC.Thin.permQ_mkQ, zOf_perm])
    have e := hz α h
    rw [← ofVec_mul_ofPerm w, map_mul] at e
    calc mkQ n (ofPerm w.perm) * zBar α h * (mkQ n (ofPerm w.perm))⁻¹
        = (mkQ n (ofVec w.vec))⁻¹ *
            (mkQ n (ofVec w.vec) * mkQ n (ofPerm w.perm) * zBar α h *
              (mkQ n (ofVec w.vec) * mkQ n (ofPerm w.perm))⁻¹) * mkQ n (ofVec w.vec) := by
          group
      _ = (mkQ n (ofVec w.vec))⁻¹ * zBar α h * mkQ n (ofVec w.vec) := by rw [e]
      _ = zBar α h := by rw [mul_assoc, ← hv, ← mul_assoc, inv_mul_cancel, one_mul]
  have hperm : w.perm = 1 := by
    by_contra hne
    obtain ⟨i, hi⟩ : ∃ i, w.perm i ≠ i := by
      by_contra hcon
      push Not at hcon
      exact hne (Equiv.ext hcon)
    have hcard : 3 ≤ ((Finset.univ.erase (w.perm i)).erase i).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hi, Finset.mem_univ _⟩),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq hcard
    have hit : i ∉ t := fun h => (Finset.mem_erase.mp (ht h)).1 rfl
    have hc : (insert i t).card = 4 := by rw [Finset.card_insert_of_notMem hit, htc]
    have h1 := hσ _ hc
    have h2 : w.perm i ∈ (insert i t).map w.perm.toEmbedding :=
      Finset.mem_map_of_mem _ (Finset.mem_insert_self i t)
    rw [h1, Finset.mem_insert] at h2
    rcases h2 with h2 | h2
    · exact hi h2
    · exact (Finset.mem_erase.mp (Finset.mem_erase.mp (ht h2)).2).1 rfl
  have hw : w = ofVec w.vec := by
    rw [← ofVec_mul_ofPerm w, hperm, ofPerm_one, mul_one]
    rfl
  set v := w.vec with hv
  have hsum : ∀ (α : Finset (Fin n)) (h : α.card = 4), ∑ k : Fin 4, v (emb α h k) = 0 := by
    intro α h
    set ι := emb α h with hι
    apply vec_conj_kList_even (v ∘ ι)
    intro k hk
    have hmem : mkQ n (ofVec v * embed ι k * (ofVec v)⁻¹) ∈ memBar α h true := by
      rw [← hx α h true]
      refine ⟨mkQ n (embed ι k), ⟨embed ι k, ⟨k, hk, rfl⟩, rfl⟩, ?_⟩
      show mkQ n w * mkQ n (embed ι k) * (mkQ n w)⁻¹ = _
      rw [map_mul, map_mul, map_inv, ← hw]
    obtain ⟨y, hy, hyeq⟩ := hmem
    rw [ofVec_conj_embed] at hyeq
    have hys := supportedOn_of_mem_memAt hy
    rw [range_emb] at hys
    have hyy := mkQ_inj_of_supportedOn hn (ι := ι) (by rw [hι, range_emb]; exact hys)
      (embed_supportedOn ι _) hyeq
    obtain ⟨k', hk', rfl⟩ := hy
    exact (embed_injective ι hyy) ▸ hk'
  have hconst : ∀ i j, v i = v j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    have hcard : 3 ≤ ((Finset.univ.erase i).erase j).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ _⟩),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq hcard
    have hit : i ∉ t := fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp (ht h)).2).1 rfl
    have hjt : j ∉ t := fun h => (Finset.mem_erase.mp (ht h)).1 rfl
    have hci : (insert i t).card = 4 := by rw [Finset.card_insert_of_notMem hit, htc]
    have hcj : (insert j t).card = 4 := by rw [Finset.card_insert_of_notMem hjt, htc]
    have hs : ∀ (α : Finset (Fin n)) (h : α.card = 4), ∑ k : Fin 4, v (emb α h k) = ∑ x ∈ α, v x := by
      intro α h
      rw [← Finset.sum_image (f := v) (fun a _ b _ hab => (emb α h).injective hab)]
      congr 1
      exact Finset.image_orderEmbOfFin_univ α h
    have h1 := hsum _ hci
    have h2 := hsum _ hcj
    rw [hs, Finset.sum_insert hit] at h1
    rw [hs, Finset.sum_insert hjt] at h2
    have := h1.trans h2.symm
    exact add_right_cancel this
  rw [hw]
  set i₀ : Fin n := ⟨0, by omega⟩
  by_cases h0 : v i₀ = 0
  · have : v = 0 := funext fun i => by rw [hconst i i₀, h0]; rfl
    rw [this]
    exact map_one (mkQ n)
  · have h1 : ∀ i, v i = 1 := fun i => by
      rw [hconst i i₀]
      revert h0
      generalize v i₀ = c
      decide +revert
    refine (QuotientGroup.eq_one_iff _).mpr (Or.inr ?_)
    refine Wr.ext (funext fun i => h1 i) rfl

end CFSG.ClassicalInvolution.Q3.AE

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE

section Recognition

variable {G : Type} [Group G]

@[expose] def ActsBy {m : ℕ} (Ω : Set (Subgroup G)) (lab : Subgroup G → Subgroup (AEQ m)) (g : G)
    (x : AEQ m) : Prop :=
  ∀ M ∈ Ω, lab (conjSub g M) = conjSub x (lab M)

theorem nonempty_aeIdent_of_labels {Ω : Set (Subgroup G)} {m : ℕ} (hm : 5 ≤ m) (hm8 : m ≠ 8)
    (hgen : pSpan Ω = ⊤) (h8 : ∀ L ∈ Ω, Nat.card L = 8)
    (hΩ : ∀ L ∈ Ω, ∀ g : G, conjSub g L ∈ Ω)
    (hz : ∀ L ∈ Ω, ∃ u : G, IsUniqueInvolution L u ∧ ∃ M ∈ Ω, conjSub u M ≠ M)
    (lab : Subgroup G → Subgroup (AEQ m))
    (hlab : ∀ L ∈ Ω, ∃ (α : Finset (Fin m)) (h : α.card = 4) (b : Bool), lab L = memBar α h b)
    (hinj : ∀ L ∈ Ω, ∀ L' ∈ Ω, lab L = lab L' → L = L')
    (hsurj : ∀ (α : Finset (Fin m)) (h : α.card = 4) (b : Bool), ∃ L ∈ Ω, lab L = memBar α h b)
    (hloc : ∀ L ∈ Ω, ∀ l ∈ L, ∃ x ∈ lab L, ActsBy Ω lab l x) :
    Nonempty (AEIdent Ω m) := by
  classical
  have huniq : ∀ g x x', ActsBy Ω lab g x → ActsBy Ω lab g x' → x = x' := by
    intro g x x' hx hx'
    have h1 : x⁻¹ * x' = 1 := by
      refine eq_one_of_normalizes_memBar hm hm8 fun α h b => ?_
      obtain ⟨M, hM, hMl⟩ := hsurj α h b
      have e := (hx M hM).symm.trans (hx' M hM)
      show conjSub (x⁻¹ * x') (memBar α h b) = memBar α h b
      rw [← hMl, conjSub_mul, ← e, conjSub_inv_conjSub]
    rw [← mul_inv_cancel_left x x', h1, mul_one]
  have hact_one : ActsBy Ω lab 1 1 := fun M _ => by rw [conjSub_one, conjSub_one]
  have hact_mul : ∀ g h x y, ActsBy Ω lab g x → ActsBy Ω lab h y → ActsBy Ω lab (g * h) (x * y) :=
    fun g h x y hx hy M hM => by
      rw [conjSub_mul, hx _ (hΩ M hM h), hy M hM, conjSub_mul]
  have hact_inv : ∀ g x, ActsBy Ω lab g x → ActsBy Ω lab g⁻¹ x⁻¹ := fun g x hx M hM => by
    have e := hx _ (hΩ M hM g⁻¹)
    rw [conjSub_conjSub_inv] at e
    rw [e, conjSub_inv_conjSub]
  set S : Subgroup G :=
    { carrier := {g | ∃ x, ActsBy Ω lab g x}
      mul_mem' := fun ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x * y, hact_mul _ _ _ _ hx hy⟩
      one_mem' := ⟨1, hact_one⟩
      inv_mem' := fun ⟨x, hx⟩ => ⟨x⁻¹, hact_inv _ _ hx⟩ } with hS
  have hall : ∀ g : G, ∃ x, ActsBy Ω lab g x := by
    intro g
    have hle : pSpan Ω ≤ S := pSpan_le fun L hL l hl => by
      obtain ⟨x, -, hx⟩ := hloc L hL l hl
      exact ⟨x, hx⟩
    exact hle (hgen ▸ Subgroup.mem_top g)
  set f : G → AEQ m := fun g => (hall g).choose with hf
  have hfa : ∀ g, ActsBy Ω lab g (f g) := fun g => (hall g).choose_spec
  have hfeq : ∀ g x, ActsBy Ω lab g x → f g = x := fun g x hx => huniq g _ _ (hfa g) hx
  set φ₀ : G →* AEQ m := MonoidHom.mk' f fun g h =>
    hfeq _ _ (hact_mul _ _ _ _ (hfa g) (hfa h)) with hφ₀
  have hφ₀a : ∀ g, φ₀ g = f g := fun _ => rfl
  have hmemlab : ∀ L ∈ Ω, ∀ l ∈ L, φ₀ l ∈ lab L := by
    intro L hL l hl
    obtain ⟨x, hxL, hx⟩ := hloc L hL l hl
    rw [hφ₀a, hfeq l x hx]
    exact hxL
  have hinjL : ∀ L ∈ Ω, ∀ l ∈ L, φ₀ l = 1 → l = 1 := by
    intro L hL l hl h1
    by_contra hl1
    obtain ⟨u, hu, M, hM, huM⟩ := hz L hL
    have hord : orderOf l ∣ 8 := h8 L hL ▸ Subgroup.orderOf_dvd_natCard L hl
    obtain ⟨i, hi, hli⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show orderOf l ∣ 2 ^ 3 by simpa using hord)
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hl1 (orderOf_eq_one_iff.mp (by simpa using hli))
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    set k := 2 ^ j with hk
    have hlk : l ^ k * l ^ k = 1 := by
      rw [← pow_add, show k + k = orderOf l by rw [hli, pow_succ]; ring, pow_orderOf_eq_one]
    have hk0 : 0 < k := by positivity
    have hlk1 : l ^ k ≠ 1 := pow_ne_one_of_lt_orderOf hk0.ne'
      (by rw [hli, pow_succ, ← hk]; omega)
    have hue : l ^ k = u := (hu.unique _ (L.pow_mem hl k) hlk).resolve_left hlk1
    have hu1 : φ₀ u = 1 := by rw [← hue, map_pow, h1, one_pow]
    apply huM
    have hact : ActsBy Ω lab u 1 := by rw [← hu1, hφ₀a]; exact hfa u
    have e := hact M hM
    rw [conjSub_one] at e
    exact hinj _ (hΩ M hM u) M hM e
  set φ : ↥(pSpan Ω) →* AEQ m := φ₀.comp (pSpan Ω).subtype with hφ
  have hlabel : ∀ L ∈ Ω, (L.subgroupOf (pSpan Ω)).map φ = lab L := by
    intro L hL
    have hle : (L.subgroupOf (pSpan Ω)).map φ ≤ lab L := by
      rintro _ ⟨y, hy, rfl⟩
      exact hmemlab L hL y (Subgroup.mem_subgroupOf.mp hy)
    obtain ⟨α, h, b, hαb⟩ := hlab L hL
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hαb, natCard_memBar hm]
    have hinjOn : Set.InjOn φ ((L.subgroupOf (pSpan Ω) : Subgroup ↥(pSpan Ω)) :
        Set ↥(pSpan Ω)) := by
      intro y hy y' hy' e
      have hyy : y⁻¹ * y' ∈ L.subgroupOf (pSpan Ω) :=
        (L.subgroupOf _).mul_mem ((L.subgroupOf _).inv_mem hy) hy'
      have h1 : φ₀ ((y⁻¹ * y' : ↥(pSpan Ω)) : G) = 1 := by
        show φ (y⁻¹ * y') = 1
        rw [map_mul, map_inv, e, inv_mul_cancel]
      have h2 := hinjL L hL _ (Subgroup.mem_subgroupOf.mp hyy) h1
      exact inv_mul_eq_one.mp (Subtype.ext h2)
    have hc : Nat.card ↥((L.subgroupOf (pSpan Ω)).map φ) =
        Nat.card ↑(φ '' ((L.subgroupOf (pSpan Ω) : Subgroup ↥(pSpan Ω)) : Set ↥(pSpan Ω))) := by
      rw [← Subgroup.coe_map]
      rfl
    rw [hc, Nat.card_image_of_injOn hinjOn]
    show 8 ≤ Nat.card ↥(L.subgroupOf (pSpan Ω))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_pSpan hL)).toEquiv, h8 L hL]
  have hunion : ∀ {x : AEQ m}, x ∈ ⋃ (α : Finset (Fin m)) (h : α.card = 4) (b : Bool),
      (memBar α h b : Set (AEQ m)) → ∃ (α : Finset (Fin m)) (h : α.card = 4) (b : Bool),
        x ∈ memBar α h b := by
    intro x hx
    obtain ⟨α, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨h, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨b, hx⟩ := Set.mem_iUnion.mp hx
    exact ⟨α, h, b, hx⟩
  have hrange : φ.range = TL4.aeModel m := by
    apply le_antisymm
    · have hle : ∀ g : G, φ₀ g ∈ memSpan m := by
        intro g
        have h' : pSpan Ω ≤ (memSpan m).comap φ₀ := pSpan_le fun L hL l hl => by
          obtain ⟨α, h, b, hαb⟩ := hlab L hL
          have := hmemlab L hL l hl
          rw [hαb] at this
          exact memBar_le_memSpan α h b this
        exact h' (hgen ▸ Subgroup.mem_top g)
      have hspan : memSpan m ≤ TL4.aeModel m := by
        rw [memSpan, Subgroup.closure_le]
        intro x hx
        obtain ⟨α, h, b, hx⟩ := hunion hx
        exact memBar_le_aeModel α h b hx
      rintro _ ⟨y, rfl⟩
      exact hspan (hle y)
    · refine (aeModel_le_memSpan hm).trans ?_
      rw [memSpan, Subgroup.closure_le]
      intro x hx
      obtain ⟨α, h, b, hx⟩ := hunion hx
      obtain ⟨L, hL, hLl⟩ := hsurj α h b
      rw [← hLl, ← hlabel L hL] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact ⟨y, rfl⟩
  have hker : φ.ker ≤ Subgroup.center ↥(pSpan Ω) := by
    intro g hg
    have hg1 : φ₀ (g : G) = 1 := hg
    have hact : ActsBy Ω lab g 1 := by rw [← hg1, hφ₀a]; exact hfa g
    have hnorm : ∀ L ∈ Ω, conjSub (g : G) L = L := fun L hL => by
      have e := hact L hL
      rw [conjSub_one] at e
      exact hinj _ (hΩ L hL g) L hL e
    have hcomm : ∀ L ∈ Ω, ∀ l ∈ L, (g : G) * l = l * g := by
      intro L hL l hl
      have hc : (g : G) * l * (g : G)⁻¹ * l⁻¹ ∈ L := by
        have h1 := conj_mem_conjSub (n := (g : G)) hl
        rw [hnorm L hL] at h1
        exact L.mul_mem h1 (L.inv_mem hl)
      have hc1 : φ₀ ((g : G) * l * (g : G)⁻¹ * l⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg1, one_mul, inv_one, mul_one,
          mul_inv_cancel]
      have h2 := hinjL L hL _ hc hc1
      calc (g : G) * l = ((g : G) * l * (g : G)⁻¹ * l⁻¹) * l * g := by group
        _ = l * g := by rw [h2, one_mul]
    rw [Subgroup.mem_center_iff]
    intro y
    have hle : pSpan Ω ≤ Subgroup.centralizer ({(g : G)} : Set G) := pSpan_le fun L hL l hl =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcomm L hL l hl).symm
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hle y.2))
  exact ⟨{ φ := φ
           range_eq := hrange
           ker_le := hker
           label := fun L hL => by
             obtain ⟨α, h, b, hαb⟩ := hlab L hL
             exact ⟨α, h, b, (hlabel L hL).trans hαb⟩
           label_surj := fun α h b => by
             obtain ⟨L, hL, hLl⟩ := hsurj α h b
             exact ⟨L, hL, (hlabel L hL).trans hLl⟩ }⟩

end Recognition

end CFSG.ClassicalInvolution.Q3.TC.Thin
