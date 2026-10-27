module

public import CFSG.ClassicalInvolution.Q3.TL3T52
public import CFSG.ClassicalInvolution.Q3.TL3T52A

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.TC.Thin.Amalg

variable {k m : ℕ}

@[expose] def memLabels (m : ℕ) : Set (Subgroup (AEQ m)) :=
  {μ | ∃ (α : Finset (Fin m)) (h : α.card = 4) (b : Bool), μ = memBar α h b}

@[expose] def memLabelsOn (S : Set (Fin m)) : Set (Subgroup (AEQ m)) :=
  {μ | ∃ (α : Finset (Fin m)) (h : α.card = 4) (b : Bool), (α : Set (Fin m)) ⊆ S ∧ μ = memBar α h b}

@[expose] def permAct (σ : Equiv.Perm (Fin m)) (μ : Subgroup (AEQ m)) : Subgroup (AEQ m) :=
  conjSub (mkQ m (ofPerm σ)) μ

theorem permAct_mul (σ τ : Equiv.Perm (Fin m)) (μ : Subgroup (AEQ m)) :
    permAct (σ * τ) μ = permAct σ (permAct τ μ) := by
  unfold permAct
  rw [← ofPerm_mul, map_mul, conjSub_mul]

theorem permAct_one (μ : Subgroup (AEQ m)) : permAct 1 μ = μ := by
  unfold permAct
  rw [ofPerm_one, map_one, conjSub_one]

theorem permAct_inv_permAct (σ : Equiv.Perm (Fin m)) (μ : Subgroup (AEQ m)) :
    permAct σ⁻¹ (permAct σ μ) = μ := by
  rw [← permAct_mul, inv_mul_cancel, permAct_one]

theorem permAct_injective (σ : Equiv.Perm (Fin m)) : Function.Injective (permAct σ) := by
  intro μ μ' h
  have := congrArg (permAct σ⁻¹) h
  rwa [permAct_inv_permAct, permAct_inv_permAct] at this

theorem memLabelsOn_subset (S : Set (Fin m)) : memLabelsOn S ⊆ memLabels m := by
  rintro μ ⟨α, h, b, -, rfl⟩
  exact ⟨α, h, b, rfl⟩

theorem memLabelsOn_univ : memLabelsOn (Set.univ : Set (Fin m)) = memLabels m := by
  refine Set.Subset.antisymm (memLabelsOn_subset _) ?_
  rintro μ ⟨α, h, b, rfl⟩
  exact ⟨α, h, b, Set.subset_univ _, rfl⟩

theorem memBar_mem_memLabels (α : Finset (Fin m)) (h : α.card = 4) (b : Bool) :
    memBar α h b ∈ memLabels m := ⟨α, h, b, rfl⟩

theorem conjSub_mem_memLabels (x : AEQ m) {μ : Subgroup (AEQ m)} (hμ : μ ∈ memLabels m) :
    conjSub x μ ∈ memLabels m := by
  obtain ⟨α, h, b, rfl⟩ := hμ
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (piSub m) x
  obtain ⟨b', hb'⟩ := exists_conj_memBar_map w α h b
  exact ⟨_, _, b', hb'⟩

theorem permAct_mem_memLabels (σ : Equiv.Perm (Fin m)) {μ : Subgroup (AEQ m)}
    (hμ : μ ∈ memLabels m) : permAct σ μ ∈ memLabels m :=
  conjSub_mem_memLabels _ hμ

theorem permAct_memBar (σ : Equiv.Perm (Fin m)) (α : Finset (Fin m)) (h : α.card = 4) (b : Bool) :
    ∃ b' : Bool, permAct σ (memBar α h b) =
      memBar (α.map σ.toEmbedding) (by rw [Finset.card_map]; exact h) b' :=
  exists_conj_ofPerm_memBar σ α h b

theorem permAct_mem_memLabelsOn {S : Set (Fin m)} (σ : Equiv.Perm (Fin m)) {α : Finset (Fin m)}
    {h : α.card = 4} (b : Bool) (hσ : ∀ x ∈ α, σ x ∈ S) :
    permAct σ (memBar α h b) ∈ memLabelsOn S := by
  obtain ⟨b', hb'⟩ := permAct_memBar σ α h b
  refine ⟨α.map σ.toEmbedding, _, b', ?_, hb'⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hx)
  exact hσ y hy

theorem map_eq_of_permAct_memBar (hm : 5 ≤ m) {σ : Equiv.Perm (Fin m)}
    {α β : Finset (Fin m)} {hα : α.card = 4} {hβ : β.card = 4} {b b' : Bool}
    (h : permAct σ (memBar α hα b) = memBar β hβ b') : α.map σ.toEmbedding = β := by
  obtain ⟨b'', hb''⟩ := permAct_memBar σ α hα b
  exact eq_of_memBar_eq' hm (hb''.symm.trans h)

theorem memBar_congr {α α' : Finset (Fin k)} {h : α.card = 4} {h' : α'.card = 4} {b b' : Bool}
    (hα : α = α') (hb : b = b') : memBar α h b = memBar α' h' b' := by
  subst hα
  subst hb
  rfl

private theorem exists_map_eq_of_subset' (c : Fin k ↪ Fin m) {α : Finset (Fin m)}
    (hα : ∀ x ∈ α, x ∈ Set.range c) : ∃ α' : Finset (Fin k), α'.map c = α := by
  classical
  refine ⟨Finset.univ.filter (fun i => c i ∈ α), ?_⟩
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hx
    obtain ⟨i, rfl⟩ := hα x hx
    exact ⟨i, hx, rfl⟩

theorem emb_map_eq_of_strictMono {c : Fin k ↪ Fin m} (hc : StrictMono c) (γ : Finset (Fin k))
    (hγ : γ.card = 4) (hγ' : (γ.map c).card = 4) :
    emb (γ.map c) hγ' = (emb γ hγ).trans c := by
  refine Function.Embedding.ext fun i => ?_
  have h : (fun i => c (γ.orderEmbOfFin hγ i)) = ⇑((γ.map c).orderEmbOfFin hγ') :=
    Finset.orderEmbOfFin_unique hγ'
      (fun i => Finset.mem_map_of_mem c (Finset.orderEmbOfFin_mem γ hγ i))
      (hc.comp (γ.orderEmbOfFin hγ).strictMono)
  exact (congrFun h i).symm

theorem memAt_map_embW {c : Fin k ↪ Fin m} (hc : StrictMono c) (γ : Finset (Fin k))
    (hγ : γ.card = 4) (hγ' : (γ.map c).card = 4) (b : Bool) :
    (memAt γ hγ b).map (embW c) = memAt (γ.map c) hγ' b := by
  have e : (embW c).comp (embed (emb γ hγ)) = embed (emb (γ.map c) hγ') := by
    refine MonoidHom.ext fun a => ?_
    rw [MonoidHom.comp_apply, embW_embed, emb_map_eq_of_strictMono hc γ hγ hγ']
  cases b
  · show (kQStar.map (embed (emb γ hγ))).map (embW c) = kQStar.map (embed (emb (γ.map c) hγ'))
    rw [Subgroup.map_map, e]
  · show (kQ.map (embed (emb γ hγ))).map (embW c) = kQ.map (embed (emb (γ.map c) hγ'))
    rw [Subgroup.map_map, e]

theorem exists_conj_memAt (w : Wr k) (α : Finset (Fin k)) (h : α.card = 4) (b : Bool) :
    ∃ b' : Bool, conjSub w (memAt α h b) =
      memAt (α.map w.perm.toEmbedding) (by rw [Finset.card_map]; exact h) b' := by
  obtain ⟨b₁, hb₁⟩ := exists_conj_ofPerm_memAt w.perm α h b
  have hβc : (α.map w.perm.toEmbedding).card = 4 := by rw [Finset.card_map]; exact h
  have e1 : conjSub w (memAt α h b) = conjSub (ofVec w.vec) (memAt (α.map w.perm.toEmbedding) hβc b₁) := by
    rw [← hb₁]
    conv_lhs => rw [← ofVec_mul_ofPerm w]
    rw [conjSub_mul]
    rfl
  rw [e1]
  have hv : (ofVec w.vec).perm = 1 := rfl
  have hK := TL4.AECov.map_embed_conj (emb (α.map w.perm.toEmbedding) hβc) hv
  rcases TL4.AECov.kQ_conj_vec (fun i => (ofVec w.vec).vec (emb (α.map w.perm.toEmbedding) hβc i))
    with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨b₁, ?_⟩
    cases b₁
    · show (kQStar.map (embed (emb _ hβc))).map (MulAut.conj (ofVec w.vec)).toMonoidHom = _
      rw [hK, h2]
      rfl
    · show (kQ.map (embed (emb _ hβc))).map (MulAut.conj (ofVec w.vec)).toMonoidHom = _
      rw [hK, h1]
      rfl
  · refine ⟨!b₁, ?_⟩
    cases b₁
    · show (kQStar.map (embed (emb _ hβc))).map (MulAut.conj (ofVec w.vec)).toMonoidHom = _
      rw [hK, h2]
      rfl
    · show (kQ.map (embed (emb _ hβc))).map (MulAut.conj (ofVec w.vec)).toMonoidHom = _
      rw [hK, h1]
      rfl

theorem map_conj_map {H H' : Type*} [Group H] [Group H'] (φ : H →* H') (g : H) (S : Subgroup H) :
    conjSub (φ g) (S.map φ) = (conjSub g S).map φ := by
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

open Classical in
@[expose] noncomputable def transLab (c : Fin k ↪ Fin m) (μ : Subgroup (AEQ k)) :
    Subgroup (AEQ m) :=
  if h : ∃ (p : Finset (Fin k) × Bool) (hp : p.1.card = 4), μ = memBar p.1 hp p.2 then
    memBar (h.choose.1.map c) (by rw [Finset.card_map]; exact h.choose_spec.choose) h.choose.2
  else ⊥

theorem transLab_memBar (hk : 5 ≤ k) (c : Fin k ↪ Fin m) (α : Finset (Fin k))
    (hα : α.card = 4) (b : Bool) :
    transLab c (memBar α hα b) = memBar (α.map c) (by rw [Finset.card_map]; exact hα) b := by
  have h : ∃ (p : Finset (Fin k) × Bool) (hp : p.1.card = 4), memBar α hα b = memBar p.1 hp p.2 :=
    ⟨(α, b), hα, rfl⟩
  unfold transLab
  rw [dif_pos h]
  have e := h.choose_spec.choose_spec
  have hαc : α = h.choose.1 := eq_of_memBar_eq' hk e
  refine memBar_congr (by rw [← hαc]) ?_
  have e' : memBar α hα b = memBar α hα h.choose.2 := e.trans (memBar_congr hαc.symm rfl)
  generalize h.choose.2 = bc at e' ⊢
  cases b <;> cases bc <;>
    first
    | rfl
    | exact absurd e' (memBar_true_ne_false hk α hα)
    | exact absurd e'.symm (memBar_true_ne_false hk α hα)

theorem transLab_injOn (hk : 5 ≤ k) (hm : 5 ≤ m) (c : Fin k ↪ Fin m)
    {μ μ' : Subgroup (AEQ k)} (hμ : μ ∈ memLabels k) (hμ' : μ' ∈ memLabels k)
    (h : transLab c μ = transLab c μ') : μ = μ' := by
  obtain ⟨α, hα, b, rfl⟩ := hμ
  obtain ⟨α', hα', b', rfl⟩ := hμ'
  rw [transLab_memBar hk, transLab_memBar hk] at h
  have hαα : α = α' := Finset.map_injective c (eq_of_memBar_eq' hm h)
  subst hαα
  have hbb : b = b' := by
    cases b <;> cases b' <;>
      first
      | rfl
      | exact absurd h (memBar_true_ne_false hm _ _)
      | exact absurd h.symm (memBar_true_ne_false hm _ _)
  subst hbb
  rfl

theorem transLab_mem_memLabelsOn (hk : 5 ≤ k) (c : Fin k ↪ Fin m)
    {μ : Subgroup (AEQ k)} (hμ : μ ∈ memLabels k) : transLab c μ ∈ memLabelsOn (Set.range c) := by
  obtain ⟨α, hα, b, rfl⟩ := hμ
  rw [transLab_memBar hk]
  refine ⟨α.map c, _, b, ?_, rfl⟩
  intro x hx
  obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hx)
  exact ⟨y, rfl⟩

theorem exists_transLab_eq (hk : 5 ≤ k) (c : Fin k ↪ Fin m)
    {μ : Subgroup (AEQ m)} (hμ : μ ∈ memLabelsOn (Set.range c)) :
    ∃ μ' ∈ memLabels k, transLab c μ' = μ := by
  obtain ⟨α, hα, b, hαc, rfl⟩ := hμ
  obtain ⟨γ, hγ⟩ := exists_map_eq_of_subset' c (α := α) fun x hx => hαc hx
  subst hγ
  have hγc : γ.card = 4 := by rwa [Finset.card_map] at hα
  exact ⟨memBar γ hγc b, ⟨γ, hγc, b, rfl⟩, transLab_memBar hk c γ hγc b⟩

theorem transport_conj (hk : 5 ≤ k) {c : Fin k ↪ Fin m} (hc : StrictMono c)
    (w : Wr k) {μ : Subgroup (AEQ k)} (hμ : μ ∈ memLabels k) :
    transLab c (conjSub (mkQ k w) μ) = conjSub (mkQ m (embW c w)) (transLab c μ) := by
  obtain ⟨δ, hδ, e, rfl⟩ := hμ
  obtain ⟨e', he'⟩ := exists_conj_memAt w δ hδ e
  have hδ' : (δ.map c).card = 4 := by rw [Finset.card_map]; exact hδ
  have hδw : (δ.map w.perm.toEmbedding).card = 4 := by rw [Finset.card_map]; exact hδ
  have hL : conjSub (mkQ k w) (memBar δ hδ e) = memBar (δ.map w.perm.toEmbedding) hδw e' := by
    unfold memBar
    rw [map_conj_map, he']
  have hR : conjSub (mkQ m (embW c w)) (memBar (δ.map c) hδ' e) =
      memBar ((δ.map w.perm.toEmbedding).map c) (by rw [Finset.card_map]; exact hδw) e' := by
    unfold memBar
    rw [map_conj_map, ← memAt_map_embW hc δ hδ hδ' e, map_conj_map, he',
      memAt_map_embW hc _ hδw]
  rw [hL, transLab_memBar hk, transLab_memBar hk, hR]

theorem conjSub_embW_ofPerm (c : Fin k ↪ Fin m) (τ : Equiv.Perm (Fin k)) (μ : Subgroup (AEQ m)) :
    conjSub (mkQ m (embW c (ofPerm τ))) μ = permAct (extPerm c τ) μ := by
  rw [embW_ofPerm, embWPerm_eq_extPerm]
  rfl

theorem transLab_permAct (hk : 5 ≤ k) {c : Fin k ↪ Fin m} (hc : StrictMono c)
    (τ : Equiv.Perm (Fin k)) {μ : Subgroup (AEQ k)} (hμ : μ ∈ memLabels k) :
    transLab c (permAct τ μ) = permAct (extPerm c τ) (transLab c μ) := by
  rw [permAct, transport_conj hk hc _ hμ, conjSub_embW_ofPerm]

@[expose] def altFix (s : Set (Fin m)) : Subgroup (alternatingGroup (Fin m)) where
  carrier := {σ | ∀ x ∈ s, (σ : Equiv.Perm (Fin m)) x = x}
  mul_mem' {a b} ha hb x hx := by
    show (a : Equiv.Perm (Fin m)) ((b : Equiv.Perm (Fin m)) x) = x
    rw [hb x hx, ha x hx]
  one_mem' x _ := rfl
  inv_mem' {a} ha x hx := by
    show ((a : Equiv.Perm (Fin m))⁻¹) x = x
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (ha x hx).symm

theorem mem_altFix {s : Set (Fin m)} {σ : alternatingGroup (Fin m)} :
    σ ∈ altFix s ↔ ∀ x ∈ s, (σ : Equiv.Perm (Fin m)) x = x := Iff.rfl

private theorem extendPermOfInjOn (S : Finset (Fin m)) (f : Fin m → Fin m)
    (hf : Set.InjOn f (S : Set (Fin m))) :
    ∃ π : Equiv.Perm (Fin m), ∀ x ∈ S, π x = f x := by
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair (fun x : S => (x : Fin m))
    (fun x : S => f x) Subtype.val_injective
    (fun a b h => Subtype.ext (hf (Finset.mem_coe.mpr a.2) (Finset.mem_coe.mpr b.2) h))
  exact ⟨π, fun x hx => hπ ⟨x, hx⟩⟩

private theorem exists_alt_agree (π : Equiv.Perm (Fin m)) (S : Finset (Fin m))
    (hS : S.card + 2 ≤ m) :
    ∃ τ : alternatingGroup (Fin m), ∀ x ∈ S, (τ : Equiv.Perm (Fin m)) x = π x := by
  classical
  by_cases hs : Equiv.Perm.sign π = 1
  · exact ⟨⟨π, Equiv.Perm.mem_alternatingGroup.mpr hs⟩, fun x _ => rfl⟩
  · have hcard : 1 < (Sᶜ).card := by
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
    have hneg : Equiv.Perm.sign π = -1 := (Int.units_eq_one_or _).resolve_left hs
    refine ⟨⟨π * Equiv.swap a b, ?_⟩, fun x hx => ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab, hneg]
      decide
    · have hxa : x ≠ a := fun h => (Finset.mem_compl.mp ha) (h ▸ hx)
      have hxb : x ≠ b := fun h => (Finset.mem_compl.mp hb) (h ▸ hx)
      show π (Equiv.swap a b x) = π x
      rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

private theorem exists_injOn_maps_finset (D W : Finset (Fin m)) (h : D.card ≤ W.card) :
    ∃ g : Fin m → Fin m, Set.InjOn g (D : Set (Fin m)) ∧ ∀ x ∈ D, g x ∈ W := by
  classical
  obtain ⟨e⟩ : Nonempty ({x // x ∈ D} ↪ {x // x ∈ W}) :=
    Function.Embedding.nonempty_of_card_le (by simpa using h)
  refine ⟨fun x => if hx : x ∈ D then (e ⟨x, hx⟩ : Fin m) else x, ?_, ?_⟩
  · intro x hx y hy hxy
    have hx' : x ∈ D := Finset.mem_coe.mp hx
    have hy' : y ∈ D := Finset.mem_coe.mp hy
    simp only [dif_pos hx', dif_pos hy'] at hxy
    exact congrArg Subtype.val (e.injective (Subtype.ext hxy))
  · intro x hx
    simp only [dif_pos hx]
    exact (e ⟨x, hx⟩).2

private theorem exists_perm_fix_map (F D W : Finset (Fin m)) (hFW : Disjoint F W)
    (hDW : D.card ≤ W.card) :
    ∃ π : Equiv.Perm (Fin m), (∀ x ∈ F, π x = x) ∧ ∀ x ∈ D, x ∉ F → π x ∈ W := by
  classical
  obtain ⟨g, hg, hgW⟩ := exists_injOn_maps_finset D W hDW
  obtain ⟨f, hf⟩ : ∃ f : Fin m → Fin m, ∀ x, f x = if x ∈ F then x else g x :=
    ⟨_, fun _ => rfl⟩
  have hinj : Set.InjOn f ((F ∪ D : Finset (Fin m)) : Set (Fin m)) := by
    intro x hx y hy hxy
    have hx' : x ∈ F ∪ D := Finset.mem_coe.mp hx
    have hy' : y ∈ F ∪ D := Finset.mem_coe.mp hy
    rw [hf, hf] at hxy
    by_cases hxF : x ∈ F
    · by_cases hyF : y ∈ F
      · rw [if_pos hxF, if_pos hyF] at hxy
        exact hxy
      · rw [if_pos hxF, if_neg hyF] at hxy
        have hyD : y ∈ D := (Finset.mem_union.mp hy').resolve_left hyF
        have hW := hgW y hyD
        rw [← hxy] at hW
        exact absurd hW (Finset.disjoint_left.mp hFW hxF)
    · by_cases hyF : y ∈ F
      · rw [if_neg hxF, if_pos hyF] at hxy
        have hxD : x ∈ D := (Finset.mem_union.mp hx').resolve_left hxF
        have hW := hgW x hxD
        rw [hxy] at hW
        exact absurd hW (Finset.disjoint_left.mp hFW hyF)
      · rw [if_neg hxF, if_neg hyF] at hxy
        have hxD : x ∈ D := (Finset.mem_union.mp hx').resolve_left hxF
        have hyD : y ∈ D := (Finset.mem_union.mp hy').resolve_left hyF
        exact hg (Finset.mem_coe.mpr hxD) (Finset.mem_coe.mpr hyD) hxy
  obtain ⟨π, hπ⟩ := extendPermOfInjOn (F ∪ D) f hinj
  refine ⟨π, fun x hx => ?_, fun x hx hxF => ?_⟩
  · rw [hπ x (Finset.mem_union_left _ hx), hf, if_pos hx]
  · rw [hπ x (Finset.mem_union_right _ hx), hf, if_neg hxF]
    exact hgW x hx

theorem exists_alt_agree_fix (σ : Equiv.Perm (Fin m)) (α T : Finset (Fin m))
    (hσα : α.map σ.toEmbedding = α) (hαT : Disjoint α T) (hm : α.card + T.card + 2 ≤ m) :
    ∃ τ : alternatingGroup (Fin m), (∀ x ∈ α, (τ : Equiv.Perm (Fin m)) x = σ x) ∧
      ∀ x ∈ T, (τ : Equiv.Perm (Fin m)) x = x := by
  classical
  have hσmem : ∀ x ∈ α, σ x ∈ α := fun x hx => by
    rw [← hσα]
    exact Finset.mem_map_of_mem _ hx
  obtain ⟨f, hf⟩ : ∃ f : Fin m → Fin m, ∀ x, f x = if x ∈ α then σ x else x :=
    ⟨_, fun _ => rfl⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    rw [hf, hf] at hxy
    by_cases hx : x ∈ α
    · by_cases hy : y ∈ α
      · rw [if_pos hx, if_pos hy] at hxy
        exact σ.injective hxy
      · rw [if_pos hx, if_neg hy] at hxy
        have : y ∈ α := by
          rw [← hxy]
          exact hσmem x hx
        exact absurd this hy
    · by_cases hy : y ∈ α
      · rw [if_neg hx, if_pos hy] at hxy
        have : x ∈ α := by
          rw [hxy]
          exact hσmem y hy
        exact absurd this hx
      · rw [if_neg hx, if_neg hy] at hxy
        exact hxy
  obtain ⟨τ, hτ⟩ := exists_alt_agree
    (Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)) (α ∪ T) (by
      have := Finset.card_union_le α T
      omega)
  refine ⟨τ, fun x hx => ?_, fun x hx => ?_⟩
  · rw [hτ x (Finset.mem_union_left _ hx)]
    show f x = σ x
    rw [hf, if_pos hx]
  · rw [hτ x (Finset.mem_union_right _ hx)]
    show f x = x
    rw [hf, if_neg (Finset.disjoint_right.mp hαT hx)]

theorem exists_alt_fix_avoid (F U T : Finset (Fin m)) (hFT : Disjoint F T)
    (hU : (U \ F).card + F.card + T.card ≤ m) (hm : (F ∪ U).card + 2 ≤ m) :
    ∃ σ : alternatingGroup (Fin m), (∀ x ∈ F, (σ : Equiv.Perm (Fin m)) x = x) ∧
      ∀ x ∈ U, (σ : Equiv.Perm (Fin m)) x ∉ T := by
  classical
  have hW : (U \ F).card ≤ ((F ∪ T)ᶜ).card := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_union_of_disjoint hFT]
    omega
  have hFW : Disjoint F ((F ∪ T)ᶜ) :=
    Finset.disjoint_left.mpr fun x hxF hxc =>
      (Finset.mem_compl.mp hxc) (Finset.mem_union_left _ hxF)
  obtain ⟨π, hπF, hπU⟩ := exists_perm_fix_map F (U \ F) ((F ∪ T)ᶜ) hFW hW
  obtain ⟨τ, hτ⟩ := exists_alt_agree π (F ∪ U) hm
  refine ⟨τ, fun x hx => ?_, fun x hx hxT => ?_⟩
  · rw [hτ x (Finset.mem_union_left _ hx)]
    exact hπF x hx
  · rw [hτ x (Finset.mem_union_right _ hx)] at hxT
    by_cases hxF : x ∈ F
    · rw [hπF x hxF] at hxT
      exact Finset.disjoint_left.mp hFT hxF hxT
    · have hmem := hπU x (Finset.mem_sdiff.mpr ⟨hx, hxF⟩) hxF
      exact (Finset.mem_compl.mp hmem) (Finset.mem_union_right _ hxT)

private theorem mem_memAt_iff' (α : Finset (Fin m)) (h : α.card = 4) (b : Bool) (x : Wr m) :
    x ∈ memAt α h b ↔ ∃ k ∈ (bif b then kList else kStarList), embed (emb α h) k = x := by
  cases b
  · exact ⟨fun ⟨k, hk, e⟩ => ⟨k, hk, e⟩, fun ⟨k, hk, e⟩ => ⟨k, hk, e⟩⟩
  · exact ⟨fun ⟨k, hk, e⟩ => ⟨k, hk, e⟩, fun ⟨k, hk, e⟩ => ⟨k, hk, e⟩⟩

private theorem conjSub_ofPerm_memAt_of_local {σ : Equiv.Perm (Fin m)} (α : Finset (Fin m))
    (h : α.card = 4) (c : Equiv.Perm (Fin 4)) (hσ : ∀ i, σ (emb α h i) = emb α h (c i))
    (b b' : Bool) (hc : ∀ k ∈ (bif b then kList else kStarList),
      ofPerm c * k * (ofPerm c)⁻¹ ∈ (bif b' then kList else kStarList)) :
    conjSub (ofPerm σ) (memAt α h b) = memAt α h b' := by
  have hconj := fun a => ofPerm_conj_embed (ι := emb α h) hσ a
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk, rfl⟩ := (mem_memAt_iff' α h b x).mp hx
    refine (mem_memAt_iff' α h b' _).mpr ⟨_, hc k hk, ?_⟩
    show embed (emb α h) (ofPerm c * k * (ofPerm c)⁻¹) =
      ofPerm σ * embed (emb α h) k * (ofPerm σ)⁻¹
    exact (hconj k).symm
  · refine le_of_eq ?_
    show Nat.card (memAt α h b') =
      Nat.card ((memAt α h b).map (MulAut.conj (ofPerm σ)).toMonoidHom)
    rw [Subgroup.card_map_of_injective (MulAut.conj (ofPerm σ)).injective, natCard_memAt,
      natCard_memAt]

private theorem permAct_memBar_of_fix {ρ : Equiv.Perm (Fin m)} (α : Finset (Fin m))
    (h : α.card = 4) (hρ : ∀ x ∈ α, ρ x = x) (b : Bool) :
    permAct ρ (memBar α h b) = memBar α h b := by
  have hσ : ∀ i, ρ (emb α h i) = emb α h ((1 : Equiv.Perm (Fin 4)) i) := by
    intro i
    have hi : emb α h i ∈ α := by
      have := Set.mem_range_self (f := emb α h) i
      rw [range_emb] at this
      exact this
    exact hρ _ hi
  have e : conjSub (ofPerm ρ) (memAt α h b) = memAt α h b :=
    conjSub_ofPerm_memAt_of_local α h 1 hσ b b (fun k hk => by simpa [ofPerm_one] using hk)
  unfold permAct memBar
  rw [map_conj_map, e]

private theorem swap_conj_kList : ∀ i j : Fin 4, i ≠ j →
    ∀ k ∈ kList, ofPerm (Equiv.swap i j) * k * (ofPerm (Equiv.swap i j))⁻¹ ∈ kStarList := by
  decide +kernel

private theorem swap_conj_kStarList : ∀ i j : Fin 4, i ≠ j →
    ∀ k ∈ kStarList, ofPerm (Equiv.swap i j) * k * (ofPerm (Equiv.swap i j))⁻¹ ∈ kList := by
  decide +kernel

private theorem permAct_swap_memBar (α : Finset (Fin m)) (h : α.card = 4) {x y : Fin m}
    (hx : x ∈ α) (hy : y ∈ α) (hxy : x ≠ y) (b : Bool) :
    permAct (Equiv.swap x y) (memBar α h b) = memBar α h (!b) := by
  obtain ⟨i, hi⟩ : x ∈ Set.range (emb α h) := by
    rw [range_emb]
    exact hx
  obtain ⟨j, hj⟩ : y ∈ Set.range (emb α h) := by
    rw [range_emb]
    exact hy
  have hij : i ≠ j := by
    rintro rfl
    exact hxy (hi.symm.trans hj)
  have hσ : ∀ k, Equiv.swap x y (emb α h k) = emb α h (Equiv.swap i j k) := by
    intro k
    by_cases hki : k = i
    · rw [hki, Equiv.swap_apply_left, hi, Equiv.swap_apply_left, hj]
    · by_cases hkj : k = j
      · rw [hkj, Equiv.swap_apply_right, hj, Equiv.swap_apply_right, hi]
      · have h1 : emb α h k ≠ x := fun e => hki ((emb α h).injective (e.trans hi.symm))
        have h2 : emb α h k ≠ y := fun e => hkj ((emb α h).injective (e.trans hj.symm))
        rw [Equiv.swap_apply_of_ne_of_ne hki hkj, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hc : ∀ k ∈ (bif b then kList else kStarList),
      ofPerm (Equiv.swap i j) * k * (ofPerm (Equiv.swap i j))⁻¹ ∈
        (bif !b then kList else kStarList) := by
    cases b
    · exact swap_conj_kStarList i j hij
    · exact swap_conj_kList i j hij
  have e : conjSub (ofPerm (Equiv.swap x y)) (memAt α h b) = memAt α h (!b) :=
    conjSub_ofPerm_memAt_of_local α h (Equiv.swap i j) hσ b (!b) hc
  unfold permAct memBar
  rw [map_conj_map, e]

private theorem permAct_memBar_congr {σ τ : Equiv.Perm (Fin m)} (α : Finset (Fin m))
    (h : α.card = 4) (hστ : ∀ x ∈ α, σ x = τ x) (b : Bool) :
    permAct σ (memBar α h b) = permAct τ (memBar α h b) := by
  have hρ : ∀ x ∈ α, (σ⁻¹ * τ) x = x := by
    intro x hx
    show σ⁻¹ (τ x) = x
    rw [← hστ x hx]
    exact σ.symm_apply_apply x
  have e : σ * (σ⁻¹ * τ) = τ := mul_inv_cancel_left σ τ
  rw [← e, permAct_mul, permAct_memBar_of_fix α h hρ b]

theorem exists_altFix_permAct_eq (T : Finset (Fin m)) (hT : T.card + 6 ≤ m)
    {μ μ' : Subgroup (AEQ m)} (hμ : μ ∈ memLabelsOn ((T : Set (Fin m))ᶜ))
    (hμ' : μ' ∈ memLabelsOn ((T : Set (Fin m))ᶜ)) :
    ∃ σ : alternatingGroup (Fin m), (∀ x ∈ T, (σ : Equiv.Perm (Fin m)) x = x) ∧
      permAct (σ : Equiv.Perm (Fin m)) μ = μ' := by
  classical
  obtain ⟨α, hα, b, hαT, rfl⟩ := hμ
  obtain ⟨α', hα', b', hα'T, rfl⟩ := hμ'
  have hαT' : ∀ x ∈ α, x ∉ T := fun x hx hxT =>
    hαT (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hxT)
  have hα'T' : ∀ x ∈ α', x ∉ T := fun x hx hxT =>
    hα'T (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hxT)
  have hTα' : Disjoint T α' :=
    Finset.disjoint_left.mpr fun x hxT hxα' => hα'T' x hxα' hxT
  obtain ⟨π₀, hπ₀T, hπ₀α⟩ := exists_perm_fix_map T α α' hTα' (by omega)
  have hmap : α.map π₀.toEmbedding = α' := by
    refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) (by rw [Finset.card_map]; omega)
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    exact hπ₀α x hx (hαT' x hx)
  obtain ⟨b₁, hb₁⟩ := permAct_memBar π₀ α hα b
  have hb₁' : permAct π₀ (memBar α hα b) = memBar α' hα' b₁ := by
    rw [hb₁]
    exact memBar_congr hmap rfl
  obtain ⟨π₁, hπ₁T, hπ₁⟩ : ∃ π₁ : Equiv.Perm (Fin m), (∀ x ∈ T, π₁ x = x) ∧
      permAct π₁ (memBar α hα b) = memBar α' hα' b' := by
    by_cases hbb : b₁ = b'
    · exact ⟨π₀, hπ₀T, by rw [hb₁', hbb]⟩
    · obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < α'.card)
      refine ⟨Equiv.swap x y * π₀, fun z hz => ?_, ?_⟩
      · have hzx : z ≠ x := fun e => hα'T' x hx (e ▸ hz)
        have hzy : z ≠ y := fun e => hα'T' y hy (e ▸ hz)
        show Equiv.swap x y (π₀ z) = z
        rw [hπ₀T z hz]
        exact Equiv.swap_apply_of_ne_of_ne hzx hzy
      · have hnb : (!b₁) = b' := by
          revert hbb
          cases b₁ <;> cases b' <;> simp
        rw [permAct_mul, hb₁', permAct_swap_memBar α' hα' hx hy hxy, hnb]
  obtain ⟨τ, hτ⟩ := exists_alt_agree π₁ (T ∪ α) (by
    have := Finset.card_union_le T α
    omega)
  refine ⟨τ, fun x hx => ?_, ?_⟩
  · rw [hτ x (Finset.mem_union_left _ hx)]
    exact hπ₁T x hx
  · exact (permAct_memBar_congr α hα
      (fun x hx => (hτ x (Finset.mem_union_right _ hx)).symm) b).symm.trans hπ₁

theorem exists_alt_permAct_eq (hm : 6 ≤ m) {μ μ' : Subgroup (AEQ m)} (hμ : μ ∈ memLabels m)
    (hμ' : μ' ∈ memLabels m) :
    ∃ σ : alternatingGroup (Fin m), permAct (σ : Equiv.Perm (Fin m)) μ = μ' := by
  obtain ⟨σ, -, hσ⟩ := exists_altFix_permAct_eq (∅ : Finset (Fin m)) (by simpa using hm)
    (μ := μ) (μ' := μ') (by simpa [memLabelsOn_univ] using hμ)
    (by simpa [memLabelsOn_univ] using hμ')
  exact ⟨σ, hσ⟩

end CFSG.ClassicalInvolution.Q3.AE
