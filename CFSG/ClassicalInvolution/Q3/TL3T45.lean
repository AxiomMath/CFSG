module

public import CFSG.ClassicalInvolution.Q3.TL3T43
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Brg

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr Certificates.AE117

variable {n k : ℕ}

open Classical in
@[expose] noncomputable def embWVec (ι : Fin k ↪ Fin n) (v : Fin k → ZMod 2) : Fin n → ZMod 2 :=
  fun x => if h : x ∈ Set.range ι then v (ι.toEquivRange.symm ⟨x, h⟩) else 0

@[expose] noncomputable def embWPerm (ι : Fin k ↪ Fin n) (σ : Equiv.Perm (Fin k)) :
    Equiv.Perm (Fin n) :=
  by classical exact σ.extendDomain ι.toEquivRange

theorem embWVec_apply (ι : Fin k ↪ Fin n) (v : Fin k → ZMod 2) (i : Fin k) :
    embWVec ι v (ι i) = v i := by
  classical
  unfold embWVec
  rw [dite_eq_left ⟨i, rfl⟩]
  congr 1
  apply ι.toEquivRange.injective
  rw [Equiv.apply_symm_apply]
  rfl

theorem embWVec_of_not_mem (ι : Fin k ↪ Fin n) (v : Fin k → ZMod 2) {x : Fin n}
    (hx : x ∉ Set.range ι) : embWVec ι v x = 0 := by
  classical
  unfold embWVec
  rw [dite_eq_right hx]

theorem embWPerm_apply (ι : Fin k ↪ Fin n) (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    embWPerm ι σ (ι i) = ι (σ i) := by
  classical
  have := Equiv.Perm.extendDomain_apply_image σ ι.toEquivRange i
  simpa [embWPerm] using this

theorem embWPerm_of_not_mem (ι : Fin k ↪ Fin n) (σ : Equiv.Perm (Fin k)) {x : Fin n}
    (hx : x ∉ Set.range ι) : embWPerm ι σ x = x := by
  classical
  exact Equiv.Perm.extendDomain_apply_not_subtype σ ι.toEquivRange hx

theorem embWPerm_mul (ι : Fin k ↪ Fin n) (σ τ : Equiv.Perm (Fin k)) :
    embWPerm ι (σ * τ) = embWPerm ι σ * embWPerm ι τ := by
  classical
  unfold embWPerm
  rw [Equiv.Perm.extendDomain_mul]

theorem embWPerm_symm_apply (ι : Fin k ↪ Fin n) (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    (embWPerm ι σ).symm (ι i) = ι (σ.symm i) := by
  apply (embWPerm ι σ).injective
  rw [Equiv.apply_symm_apply, embWPerm_apply, Equiv.apply_symm_apply]

theorem embWPerm_symm_of_not_mem (ι : Fin k ↪ Fin n) (σ : Equiv.Perm (Fin k)) {x : Fin n}
    (hx : x ∉ Set.range ι) : (embWPerm ι σ).symm x = x := by
  apply (embWPerm ι σ).injective
  rw [Equiv.apply_symm_apply, embWPerm_of_not_mem ι σ hx]

@[expose] noncomputable def embW (ι : Fin k ↪ Fin n) : Wr k →* Wr n where
  toFun a := ⟨embWVec ι a.vec, embWPerm ι a.perm⟩
  map_one' := by
    refine Wr.ext (funext fun x => ?_) ?_
    · show embWVec ι (1 : Wr k).vec x = (1 : Wr n).vec x
      by_cases hx : x ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hx
        rw [embWVec_apply]
        rfl
      · rw [embWVec_of_not_mem ι _ hx]
        rfl
    · show embWPerm ι 1 = 1
      classical
      unfold embWPerm
      exact Equiv.Perm.extendDomain_one ι.toEquivRange
  map_mul' a b := by
    refine Wr.ext (funext fun x => ?_) (embWPerm_mul ι a.perm b.perm)
    show embWVec ι (a * b).vec x = embWVec ι a.vec x +
      embWVec ι b.vec ((embWPerm ι a.perm).symm x)
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      rw [embWPerm_symm_apply, embWVec_apply, embWVec_apply, embWVec_apply, mul_vec]
    · rw [embWPerm_symm_of_not_mem ι _ hx, embWVec_of_not_mem ι _ hx,
        embWVec_of_not_mem ι _ hx, embWVec_of_not_mem ι _ hx, add_zero]

theorem embW_vec (ι : Fin k ↪ Fin n) (a : Wr k) : (embW ι a).vec = embWVec ι a.vec := rfl

theorem embW_perm (ι : Fin k ↪ Fin n) (a : Wr k) : (embW ι a).perm = embWPerm ι a.perm := rfl

theorem embW_injective (ι : Fin k ↪ Fin n) : Function.Injective (embW ι) := by
  intro a b h
  refine Wr.ext (funext fun i => ?_) (Equiv.ext fun i => ι.injective ?_)
  · have := congrArg (fun w : Wr n => w.vec (ι i)) h
    simpa only [embW_vec, embWVec_apply] using this
  · have := congrArg (fun w : Wr n => w.perm (ι i)) h
    simpa only [embW_perm, embWPerm_apply] using this

theorem embW_embed (c : Fin k ↪ Fin n) (ι : Fin 4 ↪ Fin k) (a : Wr 4) :
    embW c (embed ι a) = embed (ι.trans c) a := by
  classical
  refine Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
  · rw [embW_vec, embed_vec, embed_vec]
    by_cases hx : x ∈ Set.range c
    · obtain ⟨j, rfl⟩ := hx
      rw [embWVec_apply]
      by_cases hj : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hj
        rw [embedVec_apply]
        exact (embedVec_apply (ι.trans c) a.vec i).symm
      · rw [embedVec_of_not_mem ι _ hj, embedVec_of_not_mem]
        rintro ⟨i, hi⟩
        exact hj ⟨i, c.injective hi⟩
    · rw [embWVec_of_not_mem c _ hx, embedVec_of_not_mem]
      rintro ⟨i, rfl⟩
      exact hx ⟨ι i, rfl⟩
  · rw [embW_perm, embed_perm, embed_perm]
    by_cases hx : x ∈ Set.range c
    · obtain ⟨j, rfl⟩ := hx
      rw [embWPerm_apply]
      by_cases hj : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hj
        rw [embedPerm_apply]
        exact (embedPerm_apply (ι.trans c) a.perm i).symm
      · rw [embedPerm_of_not_mem ι _ hj, embedPerm_of_not_mem]
        rintro ⟨i, hi⟩
        exact hj ⟨i, c.injective hi⟩
    · rw [embWPerm_of_not_mem c _ hx, embedPerm_of_not_mem]
      rintro ⟨i, rfl⟩
      exact hx ⟨ι i, rfl⟩

theorem orderOf_mkQ_embW (c : Fin k ↪ Fin n) (hc : ∃ x, x ∉ Set.range c) (w : Wr k) :
    orderOf (mkQ n (embW c w)) = orderOf w := by
  obtain ⟨x₀, hx₀⟩ := hc
  have hinj : Function.Injective ((mkQ n).comp (embW c)) := by
    rw [injective_iff_map_eq_one]
    intro w hw
    rcases (mem_piSub.mp ((QuotientGroup.eq_one_iff _).mp hw)) with h | h
    · exact embW_injective c (by rw [h, map_one])
    · exfalso
      have := congrArg (fun w : Wr n => w.vec x₀) h
      simp only [embW_vec, embWVec_of_not_mem c _ hx₀] at this
      exact absurd this (by show (0 : ZMod 2) ≠ 1; decide)
  exact orderOf_injective _ hinj w

theorem memLC_eq' (ι : Fin 4 ↪ Fin n) (b : Bool) :
    memLC (ι 0) (ι 1) (ι 2) (ι 3) b = (if b then kList else kStarList).map (embed ι) :=
  TL4.Mdl117.memLC_eq ι b

theorem mem_localList_iff (b : Bool) (a : Wr 4) :
    a ∈ (if b then kList else kStarList) ↔ a ∈ (bif b then kQ else kQStar) := by
  cases b <;> rfl

theorem mem_memBar_iff' (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) (x : AEQ n) :
    x ∈ memBar α h b ↔ ∃ a ∈ (bif b then kQ else kQStar), mkQ n (embed (emb α h) a) = x := by
  cases b
  · constructor
    · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  · constructor
    · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨_, ⟨a, ha, rfl⟩, rfl⟩

theorem exists_memBar_eq_memLC (e : Fin 4 ↪ Fin n) (α : Finset (Fin n)) (h : α.card = 4)
    (he : Set.range e = (α : Set (Fin n))) (b : Bool) : ∃ b' : Bool, ∀ x : AEQ n,
      x ∈ memBar α h b ↔ ∃ a ∈ memLC (e 0) (e 1) (e 2) (e 3) b', mkQ n a = x := by
  classical
  obtain ⟨ρ, hρ⟩ := exists_perm_trans_eq e (emb α h) (by rw [he, range_emb])
  have hk : kQ ≠ kQStar := by
    intro hk
    have h1 : (⟨vec4 [0, 2], d₁⟩ : Wr 4) ∈ kQ := (by decide : (⟨vec4 [0, 2], d₁⟩ : Wr 4) ∈ kList)
    rw [hk] at h1
    exact absurd (show (⟨vec4 [0, 2], d₁⟩ : Wr 4) ∈ kStarList from h1) (by decide)
  have hperm : ∃ b' : Bool,
      (bif b' then kQ else kQStar).map (MulAut.conj (ofPerm ρ)).toMonoidHom =
        bif b then kQ else kQStar := by
    obtain ⟨c₁, hc₁⟩ := exists_perm_conj_local ρ true
    obtain ⟨c₂, hc₂⟩ := exists_perm_conj_local ρ false
    have hne : c₁ ≠ c₂ := by
      intro hc
      rw [hc] at hc₁
      exact hk (Subgroup.map_injective (MulAut.conj (ofPerm ρ)).injective (hc₁.trans hc₂.symm))
    cases b
    · by_cases h1 : c₁ = false
      · exact ⟨true, by rw [hc₁, h1]⟩
      · have h2 : c₂ = false := by cases c₁ <;> cases c₂ <;> simp_all
        exact ⟨false, by rw [hc₂, h2]⟩
    · by_cases h1 : c₁ = true
      · exact ⟨true, by rw [hc₁, h1]⟩
      · have h2 : c₂ = true := by cases c₁ <;> cases c₂ <;> simp_all
        exact ⟨false, by rw [hc₂, h2]⟩
  obtain ⟨b', hb'⟩ := hperm
  refine ⟨b', fun x => ?_⟩
  rw [mem_memBar_iff', memLC_eq' e b']
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [← hb'] at ha
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    refine ⟨embed e a₀, List.mem_map.mpr ⟨a₀, (mem_localList_iff b' a₀).mpr ha₀, rfl⟩, ?_⟩
    rw [hρ, embed_perm_trans]
    rfl
  · rintro ⟨_, hmem, rfl⟩
    obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp hmem
    refine ⟨(MulAut.conj (ofPerm ρ)).toMonoidHom a₀, ?_, ?_⟩
    · rw [← hb']
      exact ⟨a₀, (mem_localList_iff b' a₀).mp ha₀, rfl⟩
    · rw [hρ, embed_perm_trans]
      rfl

theorem conj_mem_memLC (e : Fin 4 ↪ Fin n) (σ : Equiv.Perm (Fin n)) (b : Bool) {x : Wr n}
    (hx : x ∈ memLC (e 0) (e 1) (e 2) (e 3) b) :
    ofPerm σ * x * (ofPerm σ)⁻¹ ∈
      memLC (σ (e 0)) (σ (e 1)) (σ (e 2)) (σ (e 3)) b := by
  rw [memLC_eq'] at hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  have := memLC_eq' (e.trans σ.toEmbedding) b
  simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding] at this
  rw [this, ofPerm_conj_embed_trans]
  exact List.mem_map.mpr ⟨a, ha, rfl⟩

theorem embW_mem_memLC (c : Fin k ↪ Fin n) (ι : Fin 4 ↪ Fin k) (b : Bool) {x : Wr k}
    (hx : x ∈ memLC (ι 0) (ι 1) (ι 2) (ι 3) b) :
    embW c x ∈ memLC (c (ι 0)) (c (ι 1)) (c (ι 2)) (c (ι 3)) b := by
  rw [memLC_eq'] at hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  have := memLC_eq' (ι.trans c) b
  simp only [Function.Embedding.trans_apply] at this
  rw [this, embW_embed]
  exact List.mem_map.mpr ⟨a, ha, rfl⟩

theorem mem_memLC_embW {c : Fin k ↪ Fin n} {ι : Fin 4 ↪ Fin k} {b : Bool} {y : Wr n}
    (hy : y ∈ memLC (c (ι 0)) (c (ι 1)) (c (ι 2)) (c (ι 3)) b) :
    ∃ x ∈ memLC (ι 0) (ι 1) (ι 2) (ι 3) b, embW c x = y := by
  have := memLC_eq' (ι.trans c) b
  simp only [Function.Embedding.trans_apply] at this
  rw [this] at hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
  refine ⟨embed ι a, ?_, embW_embed c ι a⟩
  rw [memLC_eq']
  exact List.mem_map.mpr ⟨a, ha, rfl⟩

theorem conf₃ : ∃ b ∈ [true, false], ∃ b' ∈ [true, false], ∃ x ∈ memLC (0 : Fin 8) 1 2 3 b,
    ∃ x' ∈ memLC (0 : Fin 8) 1 2 4 b', (x * x') ^ 5 = 1 ∧ x * x' ≠ 1 := by
  decide +kernel

theorem perm_memLC (a₀ a₁ a₂ a₃ : Fin n) (b : Bool) {x : Wr n}
    (hx : x ∈ memLC a₀ a₁ a₂ a₃ b) :
    x.perm ∈ [1, Equiv.swap a₀ a₁ * Equiv.swap a₂ a₃, Equiv.swap a₀ a₂ * Equiv.swap a₁ a₃,
      Equiv.swap a₀ a₃ * Equiv.swap a₁ a₂] := by
  cases b <;> simp only [memLC, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
    List.not_mem_nil, or_false] at hx <;>
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem eq_one_of_pow_five_of_perm {w : Wr n} (h5 : w ^ 5 = 1)
    (hp : w.perm ^ 5 = 1 → w.perm = 1) : w = 1 := by
  have hperm : ∀ j : ℕ, (w ^ j).perm = w.perm ^ j := fun j => map_pow (permHom n) w j
  have hp1 : w.perm = 1 := hp (by rw [← hperm, h5]; rfl)
  have h2 : w * w = 1 := by
    refine Wr.ext (funext fun i => ?_) ?_
    · show w.vec i + w.vec (w.perm.symm i) = 0
      rw [hp1]
      exact zmod_two_add_self _
    · show w.perm * w.perm = 1
      rw [hp1, mul_one]
  calc w = w ^ 5 * ((w * w) * (w * w))⁻¹ := by group
    _ = 1 := by rw [h5, h2, mul_one, inv_one, mul_one]

@[expose] def permList (p : Equiv.Perm (Fin 8)) : List (Fin 8) := List.ofFn fun i => p i

theorem eq_of_permList_eq {p q : Equiv.Perm (Fin 8)} (h : permList p = permList q) : p = q :=
  Equiv.ext fun i => congrFun (List.ofFn_injective h) i

theorem perm_conf₂_list : ∀ p ∈ [(1 : Equiv.Perm (Fin 8)), Equiv.swap 0 1 * Equiv.swap 2 3,
      Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 0 3 * Equiv.swap 1 2],
    ∀ p' ∈ [(1 : Equiv.Perm (Fin 8)), Equiv.swap 0 1 * Equiv.swap 4 5,
      Equiv.swap 0 4 * Equiv.swap 1 5, Equiv.swap 0 5 * Equiv.swap 1 4],
    permList ((p * p') ^ 5) = permList 1 → permList (p * p') = permList 1 := by
  intro p hp p' hp'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hp'
  rcases hp with rfl | rfl | rfl | rfl <;> rcases hp' with rfl | rfl | rfl | rfl <;>
    decide +kernel

theorem perm_conf₁_list : ∀ p ∈ [(1 : Equiv.Perm (Fin 8)), Equiv.swap 0 1 * Equiv.swap 2 3,
      Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 0 3 * Equiv.swap 1 2],
    ∀ p' ∈ [(1 : Equiv.Perm (Fin 8)), Equiv.swap 0 4 * Equiv.swap 5 6,
      Equiv.swap 0 5 * Equiv.swap 4 6, Equiv.swap 0 6 * Equiv.swap 4 5],
    permList ((p * p') ^ 5) = permList 1 → permList (p * p') = permList 1 := by
  intro p hp p' hp'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hp'
  rcases hp with rfl | rfl | rfl | rfl <;> rcases hp' with rfl | rfl | rfl | rfl <;>
    decide +kernel

theorem perm_conf₂ : ∀ p ∈ [(1 : Equiv.Perm (Fin 8)), Equiv.swap 0 1 * Equiv.swap 2 3,
      Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 0 3 * Equiv.swap 1 2],
    ∀ p' ∈ [(1 : Equiv.Perm (Fin 8)), Equiv.swap 0 1 * Equiv.swap 4 5,
      Equiv.swap 0 4 * Equiv.swap 1 5, Equiv.swap 0 5 * Equiv.swap 1 4],
    (p * p') ^ 5 = 1 → p * p' = 1 := fun p hp p' hp' h5 =>
  eq_of_permList_eq (perm_conf₂_list p hp p' hp' (by rw [h5]))

theorem perm_conf₁ : ∀ p ∈ [(1 : Equiv.Perm (Fin 8)), Equiv.swap 0 1 * Equiv.swap 2 3,
      Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 0 3 * Equiv.swap 1 2],
    ∀ p' ∈ [(1 : Equiv.Perm (Fin 8)), Equiv.swap 0 4 * Equiv.swap 5 6,
      Equiv.swap 0 5 * Equiv.swap 4 6, Equiv.swap 0 6 * Equiv.swap 4 5],
    (p * p') ^ 5 = 1 → p * p' = 1 := fun p hp p' hp' h5 =>
  eq_of_permList_eq (perm_conf₁_list p hp p' hp' (by rw [h5]))

theorem conf₂ (b b' : Bool) {x x' : Wr 8} (hx : x ∈ memLC 0 1 2 3 b)
    (hx' : x' ∈ memLC 0 1 4 5 b') (h5 : (x * x') ^ 5 = 1) : x * x' = 1 :=
  eq_one_of_pow_five_of_perm h5 (perm_conf₂ _ (perm_memLC _ _ _ _ b hx) _
    (perm_memLC _ _ _ _ b' hx'))

theorem conf₁ (b b' : Bool) {x x' : Wr 8} (hx : x ∈ memLC 0 1 2 3 b)
    (hx' : x' ∈ memLC 0 4 5 6 b') (h5 : (x * x') ^ 5 = 1) : x * x' = 1 :=
  eq_one_of_pow_five_of_perm h5 (perm_conf₁ _ (perm_memLC _ _ _ _ b hx) _
    (perm_memLC _ _ _ _ b' hx'))

section Transport

@[expose] def inc8 (hn : 9 ≤ n) : Fin 8 ↪ Fin n := Fin.castLEEmb (by omega)

theorem inc8_misses (hn : 9 ≤ n) : ∃ x, x ∉ Set.range (inc8 hn) :=
  ⟨(⟨8, by omega⟩ : Fin n), fun ⟨i, hi⟩ => by
    have := congrArg Fin.val hi
    simp [inc8] at this
    omega⟩

@[expose] noncomputable def phiConf (hn : 9 ≤ n) (σ : Equiv.Perm (Fin n)) : Wr 8 →* AEQ n :=
  ((mkQ n).comp (MulAut.conj (ofPerm σ)).toMonoidHom).comp (embW (inc8 hn))

theorem phiConf_apply (hn : 9 ≤ n) (σ : Equiv.Perm (Fin n)) (w : Wr 8) :
    phiConf hn σ w = mkQ n (ofPerm σ * embW (inc8 hn) w * (ofPerm σ)⁻¹) := rfl

theorem orderOf_phiConf (hn : 9 ≤ n) (σ : Equiv.Perm (Fin n)) (w : Wr 8) :
    orderOf (phiConf hn σ w) = orderOf w := by
  rw [phiConf_apply, map_mul, map_mul, map_inv, ← MulAut.conj_apply]
  have := orderOf_injective (MulAut.conj (mkQ n (ofPerm σ))).toMonoidHom
    (MulAut.conj (mkQ n (ofPerm σ))).injective (mkQ n (embW (inc8 hn) w))
  rw [MulEquiv.coe_toMonoidHom] at this
  rw [this, orderOf_mkQ_embW _ (inc8_misses hn)]

theorem memBar_iff_phiConf (hn : 9 ≤ n) (σ : Equiv.Perm (Fin n)) (s : Fin 4 ↪ Fin 8)
    (α : Finset (Fin n))
    (h : α.card = 4)
    (hr : Set.range ((s.trans (inc8 hn)).trans σ.toEmbedding) = (α : Set (Fin n))) :
    (∀ b₀ (k : AEQ n), k ∈ memBar α h b₀ →
      ∃ b, ∃ x ∈ memLC (s 0) (s 1) (s 2) (s 3) b, phiConf hn σ x = k) ∧
    (∀ b (x : Wr 8), x ∈ memLC (s 0) (s 1) (s 2) (s 3) b →
      ∃ b₀, phiConf hn σ x ∈ memBar α h b₀) := by
  set e := (s.trans (inc8 hn)).trans σ.toEmbedding with he
  have hfwd : ∀ b (x : Wr 8), x ∈ memLC (s 0) (s 1) (s 2) (s 3) b →
      ofPerm σ * embW (inc8 hn) x * (ofPerm σ)⁻¹ ∈ memLC (e 0) (e 1) (e 2) (e 3) b :=
    fun b x hx => conj_mem_memLC (s.trans (inc8 hn)) σ b (embW_mem_memLC (inc8 hn) s b hx)
  have hbwd : ∀ b (y : Wr n), y ∈ memLC (e 0) (e 1) (e 2) (e 3) b →
      ∃ x ∈ memLC (s 0) (s 1) (s 2) (s 3) b, ofPerm σ * embW (inc8 hn) x * (ofPerm σ)⁻¹ = y := by
    intro b y hy
    have hy' := conj_mem_memLC e σ⁻¹ b hy
    have he' : ∀ i, σ⁻¹ (e i) = (inc8 hn) (s i) := fun i => by
      rw [he]
      simp
    rw [he' 0, he' 1, he' 2, he' 3] at hy'
    obtain ⟨x, hx, hxy⟩ := mem_memLC_embW hy'
    refine ⟨x, hx, ?_⟩
    rw [hxy, show (ofPerm σ⁻¹ : Wr n) = (ofPerm σ)⁻¹ from
      (inv_eq_of_mul_eq_one_right (by rw [ofPerm_mul, mul_inv_cancel, ofPerm_one])).symm]
    group
  obtain ⟨c₁, hc₁⟩ := exists_memBar_eq_memLC e α h hr true
  obtain ⟨c₂, hc₂⟩ := exists_memBar_eq_memLC e α h hr false
  have hne : c₁ ≠ c₂ := by
    intro hc
    apply memBar_true_ne_false (by omega) α h
    ext x
    rw [hc₁, hc₂, hc]
  refine ⟨fun b₀ k hk => ?_, fun b x hx => ?_⟩
  · have hk' : ∃ a ∈ memLC (e 0) (e 1) (e 2) (e 3) (if b₀ then c₁ else c₂), mkQ n a = k := by
      cases b₀
      · exact (hc₂ k).mp hk
      · exact (hc₁ k).mp hk
    obtain ⟨a, ha, rfl⟩ := hk'
    obtain ⟨x, hx, hxa⟩ := hbwd _ a ha
    exact ⟨_, x, hx, by rw [phiConf_apply, hxa]⟩
  · have hy := hfwd b x hx
    by_cases hb : b = c₁
    · subst hb
      exact ⟨true, (hc₁ _).mpr ⟨_, hy, rfl⟩⟩
    · have hb2 : b = c₂ := by cases b <;> cases c₁ <;> cases c₂ <;> simp_all
      subst hb2
      exact ⟨false, (hc₂ _).mpr ⟨_, hy, rfl⟩⟩

end Transport

@[expose] def s₀ : Fin 4 ↪ Fin 8 := ⟨![0, 1, 2, 3], by decide⟩
@[expose] def s₃ : Fin 4 ↪ Fin 8 := ⟨![0, 1, 2, 4], by decide⟩
@[expose] def s₂ : Fin 4 ↪ Fin 8 := ⟨![0, 1, 4, 5], by decide⟩
@[expose] def s₁ : Fin 4 ↪ Fin 8 := ⟨![0, 4, 5, 6], by decide⟩

theorem exists_perm_points (hn : 9 ≤ n) {r : ℕ} (std : Fin r → Fin 8) (hstd : Function.Injective std)
    (g : Fin r → Fin n) (hg : Function.Injective g) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, σ (inc8 hn (std i)) = g i :=
  Equiv.Perm.exists_extending_pair (fun i => inc8 hn (std i)) g
    ((inc8 hn).injective.comp hstd) hg

theorem range_conf_eq (hn : 9 ≤ n) {r : ℕ} {std : Fin r → Fin 8} {g : Fin r → Fin n}
    {σ : Equiv.Perm (Fin n)} (hσ : ∀ i, σ (inc8 hn (std i)) = g i) (s : Fin 4 ↪ Fin 8)
    (idx : Fin 4 → Fin r) (hs : ∀ i, s i = std (idx i)) :
    Set.range ((s.trans (inc8 hn)).trans σ.toEmbedding) = Set.range fun i => g (idx i) := by
  ext x
  simp only [Set.mem_range, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, by rw [hs, hσ]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, by rw [hs, hσ]⟩

theorem card_sdiff_of_inter {α α' : Finset (Fin n)} (h : α.card = 4) {t : ℕ}
    (ht : (α ∩ α').card = t) : (α \ α').card = 4 - t := by
  have := Finset.card_sdiff_add_card_inter α α'
  omega

theorem coe_eq_of_parts {β β' : Finset (Fin n)} {S : Set (Fin n)}
    (hS1 : ∀ x, x ∈ β ∩ β' → x ∈ S) (hS2 : ∀ x, x ∈ β \ β' → x ∈ S) (hS3 : ∀ x ∈ S, x ∈ β) :
    (β : Set (Fin n)) = S := by
  ext x
  refine ⟨fun hx => ?_, hS3 x⟩
  by_cases hx' : x ∈ β'
  · exact hS1 x (Finset.mem_inter.mpr ⟨hx, hx'⟩)
  · exact hS2 x (Finset.mem_sdiff.mpr ⟨hx, hx'⟩)

theorem exists_conf₃ (hn : 9 ≤ n) {α α' : Finset (Fin n)} (h : α.card = 4) (h' : α'.card = 4)
    (h3 : (α ∩ α').card = 3) : ∃ σ : Equiv.Perm (Fin n),
      Set.range ((s₀.trans (inc8 hn)).trans σ.toEmbedding) = (α : Set (Fin n)) ∧
      Set.range ((s₃.trans (inc8 hn)).trans σ.toEmbedding) = (α' : Set (Fin n)) := by
  classical
  obtain ⟨c₁, c₂, c₃, h12, h13, h23, hc⟩ := Finset.card_eq_three.mp h3
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (card_sdiff_of_inter h h3)
  obtain ⟨a', ha'⟩ := Finset.card_eq_one.mp
    (card_sdiff_of_inter (α' := α) h' (t := 3) (by rw [Finset.inter_comm]; exact h3))
  have hmem : ∀ x, x ∈ α ∩ α' ↔ x = c₁ ∨ x = c₂ ∨ x = c₃ := fun x => by
    rw [hc]; simp
  have hA : a ∈ α ∧ a ∉ α' := Finset.mem_sdiff.mp (by rw [ha]; simp)
  have hA' : a' ∈ α' ∧ a' ∉ α := Finset.mem_sdiff.mp (by rw [ha']; simp)
  have hci : ∀ x, (x = c₁ ∨ x = c₂ ∨ x = c₃) → x ∈ α ∧ x ∈ α' := fun x hx =>
    Finset.mem_inter.mp ((hmem x).mpr hx)
  set g : Fin 5 → Fin n := ![c₁, c₂, c₃, a, a'] with hg
  have hg : Function.Injective g := by
    intro i j hij
    have h1 := hci c₁ (Or.inl rfl)
    have h2 := hci c₂ (Or.inr (Or.inl rfl))
    have h3' := hci c₃ (Or.inr (Or.inr rfl))
    fin_cases i <;> fin_cases j <;> simp [g] at hij ⊢ <;> subst_vars <;> simp_all
  obtain ⟨σ, hσ⟩ := exists_perm_points hn ![0, 1, 2, 3, 4] (by decide) g hg
  refine ⟨σ, ?_, ?_⟩
  · rw [range_conf_eq hn hσ s₀ ![0, 1, 2, 3] (by decide)]
    refine (coe_eq_of_parts (β' := α') (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)).symm
    · rcases (hmem x).mp hx with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · rw [ha, Finset.mem_singleton] at hx
      exact ⟨3, by rw [hx]; rfl⟩
    · obtain ⟨i, rfl⟩ := hx
      fin_cases i
      · exact (hci c₁ (Or.inl rfl)).1
      · exact (hci c₂ (Or.inr (Or.inl rfl))).1
      · exact (hci c₃ (Or.inr (Or.inr rfl))).1
      · exact hA.1
  · rw [range_conf_eq hn hσ s₃ ![0, 1, 2, 4] (by decide)]
    refine (coe_eq_of_parts (β' := α) (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)).symm
    · rw [Finset.inter_comm] at hx
      rcases (hmem x).mp hx with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · rw [ha', Finset.mem_singleton] at hx
      exact ⟨3, by rw [hx]; rfl⟩
    · obtain ⟨i, rfl⟩ := hx
      fin_cases i
      · exact (hci c₁ (Or.inl rfl)).2
      · exact (hci c₂ (Or.inr (Or.inl rfl))).2
      · exact (hci c₃ (Or.inr (Or.inr rfl))).2
      · exact hA'.1

theorem exists_conf₂ (hn : 9 ≤ n) {α α' : Finset (Fin n)} (h : α.card = 4) (h' : α'.card = 4)
    (h2 : (α ∩ α').card = 2) : ∃ σ : Equiv.Perm (Fin n),
      Set.range ((s₀.trans (inc8 hn)).trans σ.toEmbedding) = (α : Set (Fin n)) ∧
      Set.range ((s₂.trans (inc8 hn)).trans σ.toEmbedding) = (α' : Set (Fin n)) := by
  classical
  obtain ⟨c₁, c₂, h12, hc⟩ := Finset.card_eq_two.mp h2
  obtain ⟨a₁, a₂, ha12, ha⟩ := Finset.card_eq_two.mp (card_sdiff_of_inter h h2)
  obtain ⟨b₁, b₂, hb12, hb⟩ := Finset.card_eq_two.mp
    (card_sdiff_of_inter (α' := α) h' (t := 2) (by rw [Finset.inter_comm]; exact h2))
  have hmem : ∀ x, x ∈ α ∩ α' ↔ x = c₁ ∨ x = c₂ := fun x => by rw [hc]; simp
  have hmemA : ∀ x, x ∈ α \ α' ↔ x = a₁ ∨ x = a₂ := fun x => by rw [ha]; simp
  have hmemB : ∀ x, x ∈ α' \ α ↔ x = b₁ ∨ x = b₂ := fun x => by rw [hb]; simp
  have hc₁ := Finset.mem_inter.mp ((hmem c₁).mpr (Or.inl rfl))
  have hc₂ := Finset.mem_inter.mp ((hmem c₂).mpr (Or.inr rfl))
  have ha₁ := Finset.mem_sdiff.mp ((hmemA a₁).mpr (Or.inl rfl))
  have ha₂ := Finset.mem_sdiff.mp ((hmemA a₂).mpr (Or.inr rfl))
  have hb₁ := Finset.mem_sdiff.mp ((hmemB b₁).mpr (Or.inl rfl))
  have hb₂ := Finset.mem_sdiff.mp ((hmemB b₂).mpr (Or.inr rfl))
  set g : Fin 6 → Fin n := ![c₁, c₂, a₁, a₂, b₁, b₂] with hg
  have hg : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [g] at hij ⊢ <;> subst_vars <;> simp_all
  obtain ⟨σ, hσ⟩ := exists_perm_points hn ![0, 1, 2, 3, 4, 5] (by decide) g hg
  refine ⟨σ, ?_, ?_⟩
  · rw [range_conf_eq hn hσ s₀ ![0, 1, 2, 3] (by decide)]
    refine (coe_eq_of_parts (β' := α') (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)).symm
    · rcases (hmem x).mp hx with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · rcases (hmemA x).mp hx with rfl | rfl
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    · obtain ⟨i, rfl⟩ := hx
      fin_cases i
      · exact hc₁.1
      · exact hc₂.1
      · exact ha₁.1
      · exact ha₂.1
  · rw [range_conf_eq hn hσ s₂ ![0, 1, 4, 5] (by decide)]
    refine (coe_eq_of_parts (β' := α) (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)).symm
    · rw [Finset.inter_comm] at hx
      rcases (hmem x).mp hx with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · rcases (hmemB x).mp hx with rfl | rfl
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    · obtain ⟨i, rfl⟩ := hx
      fin_cases i
      · exact hc₁.2
      · exact hc₂.2
      · exact hb₁.1
      · exact hb₂.1

theorem exists_conf₁ (hn : 9 ≤ n) {α α' : Finset (Fin n)} (h : α.card = 4) (h' : α'.card = 4)
    (h1 : (α ∩ α').card = 1) : ∃ σ : Equiv.Perm (Fin n),
      Set.range ((s₀.trans (inc8 hn)).trans σ.toEmbedding) = (α : Set (Fin n)) ∧
      Set.range ((s₁.trans (inc8 hn)).trans σ.toEmbedding) = (α' : Set (Fin n)) := by
  classical
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp h1
  obtain ⟨a₁, a₂, a₃, ha12, ha13, ha23, ha⟩ := Finset.card_eq_three.mp (card_sdiff_of_inter h h1)
  obtain ⟨b₁, b₂, b₃, hb12, hb13, hb23, hb⟩ := Finset.card_eq_three.mp
    (card_sdiff_of_inter (α' := α) h' (t := 1) (by rw [Finset.inter_comm]; exact h1))
  have hmem : ∀ x, x ∈ α ∩ α' ↔ x = c := fun x => by rw [hc]; simp
  have hmemA : ∀ x, x ∈ α \ α' ↔ x = a₁ ∨ x = a₂ ∨ x = a₃ := fun x => by rw [ha]; simp
  have hmemB : ∀ x, x ∈ α' \ α ↔ x = b₁ ∨ x = b₂ ∨ x = b₃ := fun x => by rw [hb]; simp
  have hc₀ := Finset.mem_inter.mp ((hmem c).mpr rfl)
  have ha₁ := Finset.mem_sdiff.mp ((hmemA a₁).mpr (Or.inl rfl))
  have ha₂ := Finset.mem_sdiff.mp ((hmemA a₂).mpr (Or.inr (Or.inl rfl)))
  have ha₃ := Finset.mem_sdiff.mp ((hmemA a₃).mpr (Or.inr (Or.inr rfl)))
  have hb₁ := Finset.mem_sdiff.mp ((hmemB b₁).mpr (Or.inl rfl))
  have hb₂ := Finset.mem_sdiff.mp ((hmemB b₂).mpr (Or.inr (Or.inl rfl)))
  have hb₃ := Finset.mem_sdiff.mp ((hmemB b₃).mpr (Or.inr (Or.inr rfl)))
  set g : Fin 7 → Fin n := ![c, a₁, a₂, a₃, b₁, b₂, b₃] with hg
  have hg : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [g] at hij ⊢ <;> subst_vars <;> simp_all
  obtain ⟨σ, hσ⟩ := exists_perm_points hn ![0, 1, 2, 3, 4, 5, 6] (by decide) g hg
  refine ⟨σ, ?_, ?_⟩
  · rw [range_conf_eq hn hσ s₀ ![0, 1, 2, 3] (by decide)]
    refine (coe_eq_of_parts (β' := α') (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)).symm
    · rw [(hmem x).mp hx]
      exact ⟨0, rfl⟩
    · rcases (hmemA x).mp hx with rfl | rfl | rfl
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    · obtain ⟨i, rfl⟩ := hx
      fin_cases i
      · exact hc₀.1
      · exact ha₁.1
      · exact ha₂.1
      · exact ha₃.1
  · rw [range_conf_eq hn hσ s₁ ![0, 4, 5, 6] (by decide)]
    refine (coe_eq_of_parts (β' := α) (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)).symm
    · rw [Finset.inter_comm] at hx
      rw [(hmem x).mp hx]
      exact ⟨0, rfl⟩
    · rcases (hmemB x).mp hx with rfl | rfl | rfl
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    · obtain ⟨i, rfl⟩ := hx
      fin_cases i
      · exact hc₀.2
      · exact hb₁.1
      · exact hb₂.1
      · exact hb₃.1

theorem kList_pow_four : ∀ a ∈ kList, a * a * a * a = 1 := by decide +kernel

theorem kStarList_pow_four : ∀ a ∈ kStarList, a * a * a * a = 1 := by decide +kernel

theorem pow_four_of_mem_memBar {α : Finset (Fin n)} {h : α.card = 4} {b : Bool} {x : AEQ n}
    (hx : x ∈ memBar α h b) : x ^ 4 = 1 := by
  obtain ⟨a, ha, rfl⟩ := (mem_memBar_iff' α h b x).mp hx
  have h4 : a * a * a * a = 1 := by
    cases b
    · exact kStarList_pow_four a ha
    · exact kList_pow_four a ha
  rw [← map_pow, ← map_pow, show a ^ 4 = a * a * a * a by simp only [pow_succ, pow_zero, one_mul],
    h4, map_one, map_one]

theorem comm_memBar_true_false {α : Finset (Fin n)} {h : α.card = 4} :
    ∀ x ∈ memBar α h true, ∀ y ∈ memBar α h false, x * y = y * x := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
  rw [← map_mul, ← map_mul, comm_memK_memKStar _ a ha a' ha']

theorem pow_four_of_comm {x y : AEQ n} (hxy : x * y = y * x) (hx : x ^ 4 = 1) (hy : y ^ 4 = 1) :
    (x * y) ^ 4 = 1 := by
  rw [(Commute.mul_pow hxy 4), hx, hy, one_mul]

theorem orderOf_ne_five_of_pow_four {x : AEQ n} (h4 : x ^ 4 = 1) : orderOf x ≠ 5 := by
  intro h5
  have := orderOf_dvd_of_pow_eq_one h4
  rw [h5] at this
  norm_num at this

theorem adjInv_of_nine_le (hn : 9 ≤ n) : TL4.Mdl117.AdjInv n := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro α h α' h'
  constructor
  · intro h3
    obtain ⟨σ, hr, hr'⟩ := exists_conf₃ hn h h' h3
    obtain ⟨b, -, b', -, x, hx, x', hx', h5, h1⟩ := conf₃
    obtain ⟨b₀, hb₀⟩ := (memBar_iff_phiConf hn σ s₀ α h hr).2 b x hx
    obtain ⟨b₀', hb₀'⟩ := (memBar_iff_phiConf hn σ s₃ α' h' hr').2 b' x' hx'
    refine ⟨b₀, b₀', _, hb₀, _, hb₀', ?_⟩
    rw [← map_mul, orderOf_phiConf]
    exact orderOf_eq_prime h5 h1
  · rintro ⟨b, b', k, hk, k', hk', h5⟩
    by_contra h3
    have ht : (α ∩ α').card ≤ 4 := (Finset.card_le_card Finset.inter_subset_left).trans h.le
    have hk4 := pow_four_of_mem_memBar hk
    have hk4' := pow_four_of_mem_memBar hk'
    interval_cases ht' : (α ∩ α').card
    ·
      have hd : Disjoint α α' := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp ht')
      exact orderOf_ne_five_of_pow_four
        (pow_four_of_comm (comm_memBar_of_disjoint hd b b' k hk k' hk') hk4 hk4') h5
    · obtain ⟨σ, hr, hr'⟩ := exists_conf₁ hn h h' ht'
      obtain ⟨b₁, x, hx, rfl⟩ := (memBar_iff_phiConf hn σ s₀ α h hr).1 b k hk
      obtain ⟨b₂, x', hx', rfl⟩ := (memBar_iff_phiConf hn σ s₁ α' h' hr').1 b' k' hk'
      rw [← map_mul, orderOf_phiConf] at h5
      have h1 := conf₁ b₁ b₂ hx hx' (by rw [← h5]; exact pow_orderOf_eq_one _)
      rw [h1, orderOf_one] at h5
      norm_num at h5
    · obtain ⟨σ, hr, hr'⟩ := exists_conf₂ hn h h' ht'
      obtain ⟨b₁, x, hx, rfl⟩ := (memBar_iff_phiConf hn σ s₀ α h hr).1 b k hk
      obtain ⟨b₂, x', hx', rfl⟩ := (memBar_iff_phiConf hn σ s₂ α' h' hr').1 b' k' hk'
      rw [← map_mul, orderOf_phiConf] at h5
      have h1 := conf₂ b₁ b₂ hx hx' (by rw [← h5]; exact pow_orderOf_eq_one _)
      rw [h1, orderOf_one] at h5
      norm_num at h5
    · exact h3 rfl
    ·
      have hαα : α = α' := by
        have e1 : α ∩ α' = α := Finset.eq_of_subset_of_card_le Finset.inter_subset_left
          (by rw [h, ht'])
        have e2 : α ∩ α' = α' := Finset.eq_of_subset_of_card_le Finset.inter_subset_right
          (by rw [h', ht'])
        rw [← e1, e2]
      subst hαα
      have hcomm : k * k' = k' * k ∨ k * k' ∈ memBar α h b := by
        cases b <;> cases b'
        · exact Or.inr ((memBar α h false).mul_mem hk hk')
        · exact Or.inl (comm_memBar_true_false k' hk' k hk).symm
        · exact Or.inl (comm_memBar_true_false k hk k' hk')
        · exact Or.inr ((memBar α h true).mul_mem hk hk')
      rcases hcomm with hc | hc
      · exact orderOf_ne_five_of_pow_four (pow_four_of_comm hc hk4 hk4') h5
      · exact orderOf_ne_five_of_pow_four (pow_four_of_mem_memBar hc) h5

end CFSG.ClassicalInvolution.Q3.AE
