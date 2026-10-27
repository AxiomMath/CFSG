module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Blk

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {n : ℕ}

@[expose] def sets (n : ℕ) : List (Finset (Fin n)) :=
  ((List.finRange n).sublistsLen 4).map List.toFinset

@[expose] def swapsPerm (sw : List (Fin n × Fin n)) : Equiv.Perm (Fin n) :=
  (sw.map fun ab => Equiv.swap ab.1 ab.2).prod

theorem sign_swapsPerm (sw : List (Fin n × Fin n)) (hne : ∀ ab ∈ sw, ab.1 ≠ ab.2)
    (hev : sw.length % 2 = 0) : Equiv.Perm.sign (swapsPerm sw) = 1 := by
  suffices h : ∀ sw : List (Fin n × Fin n), (∀ ab ∈ sw, ab.1 ≠ ab.2) →
      Equiv.Perm.sign (swapsPerm sw) = (-1) ^ sw.length by
    rw [h sw hne]
    obtain ⟨k, hk⟩ : ∃ k, sw.length = 2 * k := ⟨sw.length / 2, by omega⟩
    rw [hk, pow_mul]; simp
  intro sw
  induction sw with
  | nil => intro _; simp [swapsPerm]
  | cons ab rest ih =>
    intro h
    have h1 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have h2 : swapsPerm (ab :: rest) = Equiv.swap ab.1 ab.2 * swapsPerm rest := by
      simp [swapsPerm]
    rw [h2, map_mul, h1, Equiv.Perm.sign_swap (h ab (List.mem_cons_self))]
    simp [pow_succ]

abbrev Step (n : ℕ) := ℕ × ℕ × List (Fin n × Fin n)

@[expose] def imgSet (sw : List (Fin n × Fin n)) (s : Finset (Fin n)) : Finset (Fin n) :=
  s.map (swapsPerm sw).toEmbedding

@[expose] def runStep (S : List (Finset (Fin n))) (st : Step n) : Option (List (Finset (Fin n))) :=
  match (sets n)[st.1]?, (sets n)[st.2.1]? with
  | some x, some y =>
    if x ∈ S ∧ y ∈ S ∧ imgSet st.2.2 x ∈ S ∧ (∀ ab ∈ st.2.2, ab.1 ≠ ab.2) ∧ st.2.2.length % 2 = 0 then
      some (imgSet st.2.2 y :: S)
    else none
  | _, _ => none

@[expose] def runChain (S : List (Finset (Fin n))) : List (Step n) → Option (List (Finset (Fin n)))
  | [] => some S
  | st :: rest => (runStep S st).bind fun S' => runChain S' rest

theorem runChain_sound {X : Set (Finset (Fin n))}
    (rule : ∀ x ∈ X, ∀ y ∈ X, ∀ p : Equiv.Perm (Fin n), Equiv.Perm.sign p = 1 →
      x.map p.toEmbedding ∈ X → y.map p.toEmbedding ∈ X) :
    ∀ (steps : List (Step n)) (S T : List (Finset (Fin n))), (∀ s ∈ S, s ∈ X) →
      runChain S steps = some T → ∀ s ∈ T, s ∈ X := by
  intro steps
  induction steps with
  | nil =>
    intro S T hS h
    simp only [runChain, Option.some.injEq] at h
    subst h; exact hS
  | cons st rest ih =>
    intro S T hS h
    simp only [runChain] at h
    obtain ⟨S', hS', hT⟩ := Option.bind_eq_some_iff.mp h
    refine ih S' T ?_ hT
    unfold runStep at hS'
    split at hS'
    · rename_i x y hx hy
      split_ifs at hS' with hc
      · simp only [Option.some.injEq] at hS'
        subst hS'
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact rule x (hS x hc.1) y (hS y hc.2.1) _ (sign_swapsPerm _ hc.2.2.2.1 hc.2.2.2.2)
            (hS _ hc.2.2.1)
        · exact hS s hs
    · simp at hS'

@[expose] def okAt (n : ℕ) (chains : List (List (Step n))) (i : ℕ) : Bool :=
  match (sets n)[0]?, (sets n)[i]?, chains[i - 1]? with
  | some a, some b, some st =>
    match runChain [a, b] st with
    | some T => (sets n).all fun s => decide (s ∈ T)
    | none => false
  | _, _, _ => false

@[expose] def checkAll (n : ℕ) (chains : List (List (Step n))) (_ : Unit) : Bool :=
  (List.range (sets n).length).all fun i => i == 0 || okAt n chains i

theorem prim0 {chains : List (List (Step n))} (hck : checkAll n chains () = true)
    (hcomp : ∀ γ : Finset (Fin n), γ.card = 4 → γ ∈ sets n)
    {X : Set (Finset (Fin n))} (hXc : ∀ x ∈ X, x.card = 4) {a0 : Finset (Fin n)}
    (ha0 : (sets n)[0]? = some a0) (hα : a0 ∈ X) (hex : ∃ β ∈ X, β ≠ a0)
    (rule : ∀ x ∈ X, ∀ y ∈ X, ∀ p : Equiv.Perm (Fin n), Equiv.Perm.sign p = 1 →
      x.map p.toEmbedding ∈ X → y.map p.toEmbedding ∈ X) :
    ∀ γ : Finset (Fin n), γ.card = 4 → γ ∈ X := by
  obtain ⟨β, hβX, hβne⟩ := hex
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (hcomp β (hXc β hβX))
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [ha0] at hi
    exact hβne (Option.some.inj hi).symm
  have hlt : i < (sets n).length := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    exact this
  have hall := List.all_eq_true.mp hck i (List.mem_range.mpr hlt)
  simp only [Bool.or_eq_true, beq_iff_eq] at hall
  rcases hall with h | h
  · exact absurd h hi0
  · unfold okAt at h
    rw [ha0, hi] at h
    cases hc : chains[i - 1]? with
    | none => rw [hc] at h; simp at h
    | some st =>
      rw [hc] at h
      simp only at h
      cases hr : runChain [a0, β] st with
      | none => rw [hr] at h; simp at h
      | some T =>
        rw [hr] at h
        simp only [List.all_eq_true, decide_eq_true_eq] at h
        have hTX := runChain_sound rule st [a0, β] T (by
          intro s hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · exact hα
          · exact hβX) hr
        intro γ hγ
        exact hTX γ (h γ (hcomp γ hγ))

theorem map_map_perm (s : Finset (Fin n)) (a b : Equiv.Perm (Fin n)) :
    (s.map a.toEmbedding).map b.toEmbedding = s.map (b * a).toEmbedding := by
  rw [Finset.map_map]
  rfl

theorem map_perm_one (s : Finset (Fin n)) : s.map (1 : Equiv.Perm (Fin n)).toEmbedding = s := by
  ext x
  simp only [Finset.mem_map, Equiv.coe_toEmbedding, Equiv.Perm.coe_one, id_eq, exists_eq_right]

theorem exists_even_perm {α a0 : Finset (Fin n)} (hα : α.card = 4) (ha0 : a0.card = 4) :
    ∃ q : Equiv.Perm (Fin n), Equiv.Perm.sign q = 1 ∧ α.map q.toEmbedding = a0 := by
  classical
  let ι := emb α hα
  let ι0 := emb a0 ha0
  let e : {x // x ∈ Set.range ι} ≃ {x // x ∈ Set.range ι0} :=
    ι.toEquivRange.symm.trans ι0.toEquivRange
  let q0 : Equiv.Perm (Fin n) := Equiv.extendSubtype e
  have hq0 : ∀ i, q0 (ι i) = ι0 i := fun i => by
    have h1 := Equiv.extendSubtype_apply_of_mem e (ι i) (Set.mem_range_self i)
    have h2 : (e ⟨ι i, Set.mem_range_self i⟩ : Fin n) = ι0 i := by
      show (ι0.toEquivRange (ι.toEquivRange.symm ⟨ι i, Set.mem_range_self i⟩) : Fin n) = _
      rw [toEquivRange_symm_apply]; rfl
    rw [h1, h2]
  have himg : ∀ q : Equiv.Perm (Fin n), (∀ i, q (ι i) = ι0 i) → α.map q.toEmbedding = a0 := by
    intro q hq
    ext x
    simp only [Finset.mem_map, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : y ∈ Set.range ι := by rw [range_emb]; exact hy
      obtain ⟨i, rfl⟩ := this
      rw [hq]
      have : ι0 i ∈ Set.range ι0 := Set.mem_range_self i
      rw [range_emb] at this
      exact this
    · intro hx
      have : x ∈ Set.range ι0 := by rw [range_emb]; exact hx
      obtain ⟨i, rfl⟩ := this
      refine ⟨ι i, ?_, hq i⟩
      have : ι i ∈ Set.range ι := Set.mem_range_self i
      rw [range_emb] at this
      exact this
  have hswap : ∀ x, Equiv.swap (ι0 0) (ι0 1) x ∈ a0 ↔ x ∈ a0 := by
    have h0 : ι0 0 ∈ a0 := by
      have : ι0 0 ∈ Set.range ι0 := Set.mem_range_self 0
      rw [range_emb] at this; exact this
    have h1 : ι0 1 ∈ a0 := by
      have : ι0 1 ∈ Set.range ι0 := Set.mem_range_self 1
      rw [range_emb] at this; exact this
    intro x
    by_cases hx0 : x = ι0 0
    · subst hx0; rw [Equiv.swap_apply_left]; exact ⟨fun _ => h0, fun _ => h1⟩
    · by_cases hx1 : x = ι0 1
      · subst hx1; rw [Equiv.swap_apply_right]; exact ⟨fun _ => h1, fun _ => h0⟩
      · rw [Equiv.swap_apply_of_ne_of_ne hx0 hx1]
  rcases Int.units_eq_one_or (Equiv.Perm.sign q0) with h | h
  · exact ⟨q0, h, himg q0 hq0⟩
  · refine ⟨Equiv.swap (ι0 0) (ι0 1) * q0, ?_, ?_⟩
    · rw [map_mul, h, Equiv.Perm.sign_swap (fun h => by
        have := ι0.injective h; exact absurd this (by decide))]
      rfl
    · rw [← map_map_perm, himg q0 hq0]
      ext x
      simp only [Finset.mem_map, Equiv.coe_toEmbedding]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (hswap y).mpr hy
      · intro hx
        exact ⟨Equiv.swap (ι0 0) (ι0 1) x, (hswap x).mpr hx, Equiv.swap_apply_self _ _ _⟩

theorem fourSetPrim_of_check {chains : List (List (Step n))} (hck : checkAll n chains () = true)
    (hcomp : ∀ γ : Finset (Fin n), γ.card = 4 → γ ∈ sets n) {a0 : Finset (Fin n)}
    (ha0 : (sets n)[0]? = some a0) (ha0c : a0.card = 4) : FourSetPrim n := by
  intro X hXc α hαX hex rule γ hγ
  obtain ⟨q, hq, hqα⟩ := exists_even_perm (hXc α hαX) ha0c
  let X' : Set (Finset (Fin n)) := (fun x => x.map q.toEmbedding) '' X
  have hinj : Function.Injective (fun x : Finset (Fin n) => x.map q.toEmbedding) :=
    fun x y h => Finset.map_injective _ h
  have hX'c : ∀ x ∈ X', x.card = 4 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Finset.card_map]; exact hXc x hx
  have hmain := prim0 hck hcomp hX'c ha0 ⟨α, hαX, hqα⟩ (by
      obtain ⟨β, hβ, hne⟩ := hex
      refine ⟨β.map q.toEmbedding, ⟨β, hβ, rfl⟩, fun h => hne (hinj (h.trans hqα.symm))⟩) (by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ p hp ⟨z, hz, hzp⟩
    have hp'' : Equiv.Perm.sign (q⁻¹ * p * q) = 1 := by
      rw [map_mul, map_mul, map_inv, hq, hp]; simp
    have h1 : (x.map (p * q).toEmbedding).map q⁻¹.toEmbedding =
        x.map (q⁻¹ * (p * q)).toEmbedding := map_map_perm _ _ _
    have h2 : x.map (p * q).toEmbedding = z.map q.toEmbedding := by
      rw [← map_map_perm x q p]; exact hzp.symm
    have h3 : (z.map q.toEmbedding).map q⁻¹.toEmbedding = z := by
      rw [map_map_perm, inv_mul_cancel, map_perm_one]
    have hxz : x.map (q⁻¹ * p * q).toEmbedding = z := by
      rw [mul_assoc, ← h1, h2, h3]
    have hw := rule x hx y hy _ hp'' (by rw [hxz]; exact hz)
    refine ⟨_, hw, ?_⟩
    show (y.map (q⁻¹ * p * q).toEmbedding).map q.toEmbedding = (y.map q.toEmbedding).map p.toEmbedding
    rw [map_map_perm, map_map_perm]
    congr 2
    group)
  obtain ⟨x, hx, hxγ⟩ := hmain (γ.map q.toEmbedding) (by rw [Finset.card_map]; exact hγ)
  have := hinj hxγ
  rw [← this]; exact hx

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10
