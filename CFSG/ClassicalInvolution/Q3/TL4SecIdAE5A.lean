module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2AEM

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.AE5

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.TL4.SecIdE2 (eq_ofVec_mul_ofPerm ofVec_conj_embed)

theorem wsum_allOnes : wsum (allOnes 5) = 1 := by decide

theorem exists_lift (x : AEQ 5) : ∃ w : Wr 5, wsum w = 0 ∧ mkQ 5 w = x := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (piSub 5) x
  by_cases hw : wsum w = 0
  · exact ⟨w, hw, rfl⟩
  · refine ⟨w * allOnes 5, ?_, ?_⟩
    · rw [wsum_mul, wsum_allOnes]
      generalize wsum w = s at hw ⊢
      revert s
      decide
    · rw [map_mul]
      have : mkQ 5 (allOnes 5) = 1 :=
        (QuotientGroup.eq_one_iff (allOnes 5)).mpr (Or.inr rfl)
      rw [this, mul_one]

theorem eq_of_mkQ_eq {a b : Wr 5} (hs : wsum a = wsum b) (h : mkQ 5 a = mkQ 5 b) : a = b := by
  rcases mkQ_eq_iff.mp h with h1 | h1
  · exact inv_mul_eq_one.mp h1
  · exfalso
    have h2 := congrArg wsum h1
    rw [wsum_mul, wsum_inv, hs, wsum_allOnes, zmod_two_add_self] at h2
    exact absurd h2 (by decide)

theorem comm_of_mkQ_comm {a b : Wr 5} (h : mkQ 5 a * mkQ 5 b = mkQ 5 b * mkQ 5 a) :
    a * b = b * a := by
  rw [← map_mul, ← map_mul] at h
  refine eq_of_mkQ_eq ?_ h
  rw [wsum_mul, wsum_mul, add_comm]

theorem conj_embed (ι : Fin 4 ↪ Fin 5) (w : Wr 5) (hmap : ∀ i, w.perm (ι i) ∈ Set.range ι)
    (a : Wr 4) :
    w * embed ι a * w⁻¹ = embed ι (ofVec (w.vec ∘ ι) *
      (ofPerm (localPerm ι w.perm hmap) * a * (ofPerm (localPerm ι w.perm hmap))⁻¹) *
        (ofVec (w.vec ∘ ι))⁻¹) := by
  rw [← ofVec_conj_embed, ← ofPerm_conj_embed (localPerm_spec ι w.perm hmap)]
  conv_lhs => rw [eq_ofVec_mul_ofPerm w]
  group

theorem exists_unique_compl (ι : Fin 4 ↪ Fin 5) :
    ∃ p, p ∉ Set.range ι ∧ ∀ y, y ∉ Set.range ι → y = p := by
  classical
  have hlt : (Finset.univ.map ι).card < (Finset.univ : Finset (Fin 5)).card := by
    rw [card_map_univ, Finset.card_univ, Fintype.card_fin]
    norm_num
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hp' : p ∉ Set.range ι := by
    rw [range_eq_finset]
    exact_mod_cast hp
  refine ⟨p, hp', fun y hy => ?_⟩
  by_contra hyp
  have hy' : y ∉ Finset.univ.map ι := by
    rw [range_eq_finset] at hy
    exact_mod_cast hy
  have hsub : insert p (insert y (Finset.univ.map ι)) ⊆ Finset.univ := Finset.subset_univ _
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [hp, Ne.symm hyp]),
    Finset.card_insert_of_notMem hy', card_map_univ, Finset.card_univ, Fintype.card_fin] at hcard
  omega

theorem sum_eq_add (ι : Fin 4 ↪ Fin 5) {p : Fin 5} (hp : p ∉ Set.range ι)
    (f : Fin 5 → ZMod 2) : ∑ x, f x = ∑ i, f (ι i) + f p := by
  classical
  have hp' : p ∉ Finset.univ.map ι := by
    rw [range_eq_finset] at hp
    exact_mod_cast hp
  have huniv : Finset.univ = insert p (Finset.univ.map ι) := by
    refine (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_).symm
    rw [Finset.card_insert_of_notMem hp', card_map_univ, Finset.card_univ, Fintype.card_fin]
  rw [huniv, Finset.sum_insert hp', Finset.sum_map, add_comm]

theorem perm_eq_one_of_fix (ι : Fin 4 ↪ Fin 5) {σ : Equiv.Perm (Fin 5)}
    (hfix : ∀ i, σ (ι i) = ι i) : σ = 1 := by
  obtain ⟨p, hp, hu⟩ := exists_unique_compl ι
  refine Equiv.ext fun x => ?_
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hx
    exact hfix i
  · rw [hu x hx]
    show σ p = p
    refine hu _ fun ⟨i, hi⟩ => hp ⟨i, ?_⟩
    apply σ.injective
    rw [hfix i, hi]

theorem local_cent : ∀ c : Equiv.Perm (Fin 4), ∀ v : Fin 4 → ZMod 2,
    ((∀ a ∈ kList, ofVec v * (ofPerm c * a * (ofPerm c)⁻¹) * (ofVec v)⁻¹ = a) ∧
      (∀ a ∈ kStarList, ofVec v * (ofPerm c * a * (ofPerm c)⁻¹) * (ofVec v)⁻¹ = a)) →
    c = 1 ∧ (v = 0 ∨ v = fun _ => 1) := by
  decide +kernel

theorem local_twin : ∀ c : Equiv.Perm (Fin 4), ∀ v : Fin 4 → ZMod 2,
    (c * c = 1 ∧ (∀ i, v i + v (c.symm i) = 0) ∧
      (∀ a ∈ kList, ofVec v * (ofPerm c * a * (ofPerm c)⁻¹) * (ofVec v)⁻¹ = a) ∧
      (∀ a ∈ kStarList, ofVec v * (ofPerm c * a * (ofPerm c)⁻¹) * (ofVec v)⁻¹ ∈ kStarList)) →
    ∀ a ∈ kStarList, ofVec v * (ofPerm c * a * (ofPerm c)⁻¹) * (ofVec v)⁻¹ = a := by
  decide +kernel

theorem local_twin' : ∀ c : Equiv.Perm (Fin 4), ∀ v : Fin 4 → ZMod 2,
    (c * c = 1 ∧ (∀ i, v i + v (c.symm i) = 0) ∧
      (∀ a ∈ kStarList, ofVec v * (ofPerm c * a * (ofPerm c)⁻¹) * (ofVec v)⁻¹ = a) ∧
      (∀ a ∈ kList, ofVec v * (ofPerm c * a * (ofPerm c)⁻¹) * (ofVec v)⁻¹ ∈ kList)) →
    ∀ a ∈ kList, ofVec v * (ofPerm c * a * (ofPerm c)⁻¹) * (ofVec v)⁻¹ = a := by
  decide +kernel

variable (α : Finset (Fin 5)) (h : α.card = 4)

@[expose] def localList (b : Bool) : List (Wr 4) := bif b then kList else kStarList

theorem mem_memAt_iff {b : Bool} {x : Wr 5} :
    x ∈ memAt α h b ↔ ∃ a ∈ localList b, embed (emb α h) a = x := by
  cases b
  · exact Iff.rfl
  · exact Iff.rfl

theorem embed_mem_memBar {b : Bool} {a : Wr 4} (ha : a ∈ localList b) :
    mkQ 5 (embed (emb α h) a) ∈ memBar α h b :=
  ⟨embed (emb α h) a, (mem_memAt_iff α h).mpr ⟨a, ha, rfl⟩, rfl⟩

theorem wsum_embed_of_mem {b : Bool} {a : Wr 4} (ha : a ∈ localList b) :
    wsum (embed (emb α h) a) = 0 := by
  cases b
  · exact (memKStar_le_aeSub (emb α h) ⟨a, ha, rfl⟩).1
  · exact (memK_le_aeSub (emb α h) ⟨a, ha, rfl⟩).1

theorem perm_mem_of_comm_zBar {w : Wr 5} (hz : mkQ 5 w * zBar α h = zBar α h * mkQ 5 w) :
    ∀ i, w.perm (emb α h i) ∈ Set.range (emb α h) := fun i =>
  perm_mem_of_comm_zOf (comm_of_mkQ_comm hz).symm ⟨i, rfl⟩

theorem local_eq_of_comm {w : Wr 5} (hmap : ∀ i, w.perm (emb α h i) ∈ Set.range (emb α h))
    {b : Bool} (hb : ∀ a' ∈ memBar α h b, mkQ 5 w * a' = a' * mkQ 5 w) {a : Wr 4}
    (ha : a ∈ localList b) :
    ofVec (w.vec ∘ emb α h) * (ofPerm (localPerm (emb α h) w.perm hmap) * a *
      (ofPerm (localPerm (emb α h) w.perm hmap))⁻¹) * (ofVec (w.vec ∘ emb α h))⁻¹ = a := by
  have hc := comm_of_mkQ_comm (hb _ (embed_mem_memBar α h ha))
  apply embed_injective (emb α h)
  rw [← conj_embed (emb α h) w hmap, hc, mul_inv_cancel_right]

theorem local_mem_of_norm {w : Wr 5} (hmap : ∀ i, w.perm (emb α h i) ∈ Set.range (emb α h))
    (hw0 : wsum w = 0) {b : Bool}
    (hb : ∀ a' ∈ memBar α h b, mkQ 5 w * a' * (mkQ 5 w)⁻¹ ∈ memBar α h b) {a : Wr 4}
    (ha : a ∈ localList b) :
    ofVec (w.vec ∘ emb α h) * (ofPerm (localPerm (emb α h) w.perm hmap) * a *
      (ofPerm (localPerm (emb α h) w.perm hmap))⁻¹) * (ofVec (w.vec ∘ emb α h))⁻¹ ∈
        localList b := by
  have h5 := hb _ (embed_mem_memBar α h ha)
  rw [← map_mul, ← map_inv, ← map_mul, conj_embed (emb α h) w hmap] at h5
  obtain ⟨a', ha', he⟩ := h5
  obtain ⟨a'', ha'', rfl⟩ := (mem_memAt_iff α h).mp ha'
  have hs : wsum (embed (emb α h) a'') = wsum (embed (emb α h)
      (ofVec (w.vec ∘ emb α h) * (ofPerm (localPerm (emb α h) w.perm hmap) * a *
        (ofPerm (localPerm (emb α h) w.perm hmap))⁻¹) * (ofVec (w.vec ∘ emb α h))⁻¹)) := by
    rw [wsum_embed_of_mem α h ha'', ← conj_embed (emb α h) w hmap, wsum_mul, wsum_mul,
      wsum_inv, wsum_embed_of_mem α h ha, hw0, add_zero, zero_add]
  rw [← embed_injective (emb α h) (eq_of_mkQ_eq hs he)]
  exact ha''

theorem eq_one_or_eq_zBar_of_comm {x : AEQ 5}
    (h1 : ∀ a ∈ memBar α h true, x * a = a * x) (h2 : ∀ a ∈ memBar α h false, x * a = a * x) :
    x = 1 ∨ x = zBar α h := by
  obtain ⟨w, hw0, rfl⟩ := exists_lift x
  have hmap := perm_mem_of_comm_zBar α h (h1 _ (zBar_mem_memBar α h true))
  obtain ⟨hc1, hv⟩ := local_cent _ _ ⟨fun a ha => local_eq_of_comm α h hmap h1 ha,
    fun a ha => local_eq_of_comm α h hmap h2 ha⟩
  have hfix : ∀ i, w.perm (emb α h i) = emb α h i := fun i => by
    rw [localPerm_spec (emb α h) w.perm hmap, hc1]
    rfl
  have hperm := perm_eq_one_of_fix (emb α h) hfix
  obtain ⟨p, hp, hu⟩ := exists_unique_compl (emb α h)
  have hsum := sum_eq_add (emb α h) hp w.vec
  have hwp : w.vec p = 0 := by
    have : wsum w = ∑ x, w.vec x := rfl
    rw [hw0, hsum] at this
    rcases hv with hv | hv
    · have h0 : ∀ i, w.vec (emb α h i) = 0 := fun i => congrFun hv i
      simp only [h0, Finset.sum_const_zero, zero_add] at this
      exact this.symm
    · have h0 : ∀ i, w.vec (emb α h i) = 1 := fun i => congrFun hv i
      simp only [h0, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      rw [show ((4 : ℕ) : ZMod 2) * 1 = 0 by decide, zero_add] at this
      exact this.symm
  rcases hv with hv | hv
  · left
    have : w = 1 := by
      refine Wr.ext (funext fun y => ?_) hperm
      by_cases hy : y ∈ Set.range (emb α h)
      · obtain ⟨i, rfl⟩ := hy
        exact congrFun hv i
      · rw [hu y hy, hwp]
        rfl
    rw [this, map_one]
  · right
    have : w = zOf (emb α h) := by
      refine Wr.ext (funext fun y => ?_) (hperm.trans (zOf_perm (emb α h)).symm)
      rw [zOf_vec_apply]
      by_cases hy : y ∈ Set.range (emb α h)
      · simp only [hy, ite_true]
        obtain ⟨i, rfl⟩ := hy
        exact congrFun hv i
      · simp only [hy, ite_false]
        rw [hu y hy, hwp]
    rw [this]
    rfl

theorem comm_of_twin_of_sq (b : Bool) {y : AEQ 5} (hy : y * y = 1)
    (h1 : ∀ a ∈ memBar α h b, y * a = a * y)
    (h2 : ∀ a ∈ memBar α h (!b), y * a * y⁻¹ ∈ memBar α h (!b)) :
    ∀ a ∈ memBar α h (!b), y * a = a * y := by
  obtain ⟨w, hw0, rfl⟩ := exists_lift y
  have hmap := perm_mem_of_comm_zBar α h (h1 _ (zBar_mem_memBar α h b))
  have hww : w * w = 1 := by
    refine eq_of_mkQ_eq ?_ (by rw [map_mul, hy, map_one])
    rw [wsum_mul, hw0, add_zero, wsum_one]
  have hcc : localPerm (emb α h) w.perm hmap * localPerm (emb α h) w.perm hmap = 1 := by
    refine Equiv.ext fun i => (emb α h).injective ?_
    have h3 : (w * w).perm (emb α h i) = emb α h i := by rw [hww]; rfl
    rw [mul_perm] at h3
    show emb α h (localPerm (emb α h) w.perm hmap (localPerm (emb α h) w.perm hmap i)) =
      emb α h i
    rw [← localPerm_spec, ← localPerm_spec]
    exact h3
  have hvv : ∀ i, (w.vec ∘ emb α h) i +
      (w.vec ∘ emb α h) ((localPerm (emb α h) w.perm hmap).symm i) = 0 := by
    intro i
    have h3 : (w * w).vec (emb α h i) = 0 := by rw [hww]; rfl
    rw [mul_vec] at h3
    have h4 : w.perm.symm (emb α h i) = emb α h ((localPerm (emb α h) w.perm hmap).symm i) := by
      apply w.perm.injective
      rw [Equiv.apply_symm_apply, localPerm_spec (emb α h) w.perm hmap, Equiv.apply_symm_apply]
    rw [h4] at h3
    exact h3
  have hfix : ∀ a ∈ localList (!b),
      ofVec (w.vec ∘ emb α h) * (ofPerm (localPerm (emb α h) w.perm hmap) * a *
        (ofPerm (localPerm (emb α h) w.perm hmap))⁻¹) * (ofVec (w.vec ∘ emb α h))⁻¹ = a := by
    cases b
    · exact local_twin' _ _ ⟨hcc, hvv, fun a ha => local_eq_of_comm α h hmap h1 ha,
        fun a ha => local_mem_of_norm α h hmap hw0 h2 ha⟩
    · exact local_twin _ _ ⟨hcc, hvv, fun a ha => local_eq_of_comm α h hmap h1 ha,
        fun a ha => local_mem_of_norm α h hmap hw0 h2 ha⟩
  intro a ha
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  obtain ⟨a₁, ha₁, rfl⟩ := (mem_memAt_iff α h).mp ha₀
  have hc : w * embed (emb α h) a₁ * w⁻¹ = embed (emb α h) a₁ := by
    rw [conj_embed (emb α h) w hmap, hfix a₁ ha₁]
  have hc' : w * embed (emb α h) a₁ = embed (emb α h) a₁ * w :=
    calc w * embed (emb α h) a₁ = (w * embed (emb α h) a₁ * w⁻¹) * w := by group
      _ = embed (emb α h) a₁ * w := by rw [hc]
  rw [← map_mul, ← map_mul, hc']

theorem mul_ne_zBar {β : Finset (Fin 5)} (h' : β.card = 4) (hβ : β ≠ α) {x y : AEQ 5}
    (hx : x ∈ memBar α h true) (hy : y ∈ memBar α h false) : x * y ≠ zBar β h' := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨a', ha', rfl⟩ := hy
  intro he
  rw [← map_mul] at he
  have hs : wsum (a * a') = wsum (zOf (emb β h')) := by
    rw [wsum_mul, (memK_le_aeSub (emb α h) ha).1, (memKStar_le_aeSub (emb α h) ha').1,
      (memK_le_aeSub (emb β h') (zOf_mem_memK (emb β h'))).1, add_zero]
  have heq := eq_of_mkQ_eq hs he
  have hsupp : SupportedOn (zOf (emb β h')) (Set.range (emb α h)) := by
    rw [← heq]
    exact (supportedOn_of_mem_memAt (b := true) ha).mul (supportedOn_of_mem_memAt (b := false) ha')
  have hsub : Set.range (emb β h') ⊆ Set.range (emb α h) := by
    intro y hy
    by_contra hyα
    have h1 := (hsupp y hyα).1
    rw [zOf_vec_apply] at h1
    simp only [hy, ite_true] at h1
    exact absurd h1 (by decide)
  have hrange := range_eq_of_subset hsub
  rw [range_emb, range_emb] at hrange
  exact hβ (by exact_mod_cast hrange)

theorem eq_one_of_comm_aeBar {x : AEQ 5} (hx : ∀ g ∈ (aeSub 5).map (mkQ 5), x * g = g * x) :
    x = 1 := by
  have h0 : ({0, 1, 2, 3} : Finset (Fin 5)).card = 4 := by decide
  have h1 : ({0, 1, 2, 4} : Finset (Fin 5)).card = 4 := by decide
  have hmem : ∀ (γ : Finset (Fin 5)) (hγ : γ.card = 4) (b : Bool), ∀ a ∈ memBar γ hγ b,
      a ∈ (aeSub 5).map (mkQ 5) := by
    rintro γ hγ b _ ⟨a, ha, rfl⟩
    refine ⟨a, ?_, rfl⟩
    cases b
    · exact memKStar_le_aeSub _ ha
    · exact memK_le_aeSub _ ha
  rcases eq_one_or_eq_zBar_of_comm _ h0 (fun a ha => hx a (hmem _ _ _ a ha))
      (fun a ha => hx a (hmem _ _ _ a ha)) with hx1 | hx1
  · exact hx1
  · exfalso
    have hne : (Set.range (emb ({0, 1, 2, 3} : Finset (Fin 5)) h0) ∩
        Set.range (emb ({0, 1, 2, 4} : Finset (Fin 5)) h1)).Nonempty := by
      refine ⟨0, ?_, ?_⟩ <;> rw [range_emb] <;> decide
    have hneq : Set.range (emb ({0, 1, 2, 3} : Finset (Fin 5)) h0) ≠
        Set.range (emb ({0, 1, 2, 4} : Finset (Fin 5)) h1) := by
      rw [range_emb, range_emb]
      intro he
      have : (4 : Fin 5) ∈ (({0, 1, 2, 3} : Finset (Fin 5)) : Set (Fin 5)) := by
        rw [he]; decide
      exact absurd this (by decide)
    obtain ⟨b, hb, hbne⟩ := not_comm_mkQ_zOf_memK hne hneq
    apply hbne
    have := hx (mkQ 5 b) ⟨b, memK_le_aeSub _ hb, rfl⟩
    rw [hx1] at this
    exact this

end CFSG.ClassicalInvolution.Q3.TL4.AE5
