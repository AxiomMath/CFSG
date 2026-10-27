module

public import CFSG.CGT.PushingUpLit.A78.LQ4Bits
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.CGT.PushingUpLit.A78.LQ4

open CFSG.CGT.PushingUpLit.A78.LQ4Fin

@[expose] def subOfMask (m : ℕ) (hm : m ∈ subs) : Subgroup (Bits 4) where
  carrier := {v | m.testBit v.1 = true}
  mul_mem' := fun {a b} ha hb => by
    have := (subs_closed m hm).2 a.1 a.lt16 b.1 b.lt16 ha hb
    simpa using this
  one_mem' := by simpa using (subs_closed m hm).1
  inv_mem' := fun {a} ha => by simpa using ha

theorem mem_subOfMask {m : ℕ} {hm : m ∈ subs} {v : Bits 4} :
    v ∈ subOfMask m hm ↔ m.testBit v.1 = true := Iff.rfl

theorem testBit_join {m : ℕ} (hm : m ∈ subs) {v : ℕ} (hv : v < 16) {w : ℕ} (hw : w < 16) :
    (joinMask m v).testBit w = true ↔ m.testBit w = true ∨ m.testBit (w ^^^ v) = true := by
  have := join_spec m hm v hv w hw
  rw [this]; simp

theorem foldl_join_mem {l : List ℕ} (hl : ∀ x ∈ l, x < 16) :
    ∀ acc ∈ subs, l.foldl joinMask acc ∈ subs := by
  induction l with
  | nil => intro acc h; exact h
  | cons v l ih =>
    intro acc h
    simp only [List.foldl_cons]
    exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) _
      (join_mem_subs acc h v (hl v List.mem_cons_self))

theorem foldl_join_ge {l : List ℕ} (hl : ∀ x ∈ l, x < 16) :
    ∀ acc ∈ subs, ∀ w, w < 16 → acc.testBit w = true → (l.foldl joinMask acc).testBit w = true := by
  induction l with
  | nil => intro acc _ w _ h; exact h
  | cons v l ih =>
    intro acc h w hw hb
    simp only [List.foldl_cons]
    refine ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) _
      (join_mem_subs acc h v (hl v List.mem_cons_self)) w hw ?_
    exact (testBit_join h (hl v List.mem_cons_self) hw).2 (Or.inl hb)

theorem foldl_join_gen {l : List ℕ} (hl : ∀ x ∈ l, x < 16) :
    ∀ acc ∈ subs, ∀ x ∈ l, (l.foldl joinMask acc).testBit x = true := by
  induction l with
  | nil => intro acc _ x hx; simp at hx
  | cons v l ih =>
    intro acc h x hx
    simp only [List.foldl_cons]
    have hv := hl v List.mem_cons_self
    have hl' : ∀ x ∈ l, x < 16 := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have hj := join_mem_subs acc h v hv
    rcases List.mem_cons.1 hx with rfl | hx
    · refine foldl_join_ge hl' _ hj x hv ?_
      refine (testBit_join h hv hv).2 (Or.inr ?_)
      simpa using (subs_closed acc h).1
    · exact ih hl' _ hj x hx

theorem foldl_join_min (K : Subgroup (Bits 4)) {l : List ℕ} (hl : ∀ x ∈ l, x < 16 ∧ dec4 x ∈ K) :
    ∀ acc ∈ subs, (∀ w, w < 16 → acc.testBit w = true → dec4 w ∈ K) →
      ∀ w, w < 16 → (l.foldl joinMask acc).testBit w = true → dec4 w ∈ K := by
  induction l with
  | nil => intro acc _ h w hw hb; exact h w hw hb
  | cons v l ih =>
    intro acc h hK w hw hb
    simp only [List.foldl_cons] at hb
    have hv := hl v List.mem_cons_self
    have hl' : ∀ x ∈ l, x < 16 ∧ dec4 x ∈ K := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    refine ih hl' _ (join_mem_subs acc h v hv.1) ?_ w hw hb
    intro u hu hub
    rcases (testBit_join h hv.1 hu).1 hub with h1 | h1
    · exact hK u hu h1
    · have hxor : u ^^^ v < 16 := xor_lt16 hu hv.1
      have h2 := hK _ hxor h1
      have h3 : dec4 u = dec4 (u ^^^ v) * dec4 v := by
        rw [← dec4_xor hxor hv.1]
        congr 1
        simp
      rw [h3]
      exact K.mul_mem h2 hv.2

theorem span_mem {l : List ℕ} (hl : ∀ x ∈ l, x < 16) : spanMask l ∈ subs :=
  foldl_join_mem hl 1 one_mem_subs

theorem span_gen {l : List ℕ} (hl : ∀ x ∈ l, x < 16) : ∀ x ∈ l, (spanMask l).testBit x = true :=
  foldl_join_gen hl 1 one_mem_subs

theorem span_min (K : Subgroup (Bits 4)) {l : List ℕ} (hl : ∀ x ∈ l, x < 16 ∧ dec4 x ∈ K) :
    ∀ w, w < 16 → (spanMask l).testBit w = true → dec4 w ∈ K := by
  refine foldl_join_min K hl 1 one_mem_subs ?_
  intro w hw hb
  have : w = 0 := by
    have h1 : (1 : ℕ).testBit w = true := hb
    rw [Nat.testBit_one_eq_true_iff_self_eq_zero] at h1
    exact h1
  subst this
  rw [dec4_zero]; exact K.one_mem

open Classical in
theorem exists_mask (H : Subgroup (Bits 4)) :
    ∃ m ∈ subs, ∀ w, w < 16 → (m.testBit w = true ↔ dec4 w ∈ H) := by
  set l : List ℕ := (List.range 16).filter (fun i => decide (dec4 i ∈ H)) with hlℓ
  have hl : ∀ x ∈ l, x < 16 ∧ dec4 x ∈ H := by
    intro x hx
    simp only [hlℓ, List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
    exact hx
  refine ⟨spanMask l, span_mem (fun x hx => (hl x hx).1), ?_⟩
  intro w hw
  constructor
  · exact span_min H hl w hw
  · intro hwH
    refine span_gen (fun x hx => (hl x hx).1) w ?_
    simp only [hlℓ, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨hw, hwH⟩

theorem card_eq_popc (H : Subgroup (Bits 4)) {m : ℕ}
    (hm : ∀ w, w < 16 → (m.testBit w = true ↔ dec4 w ∈ H)) : Nat.card H = popc m := by
  classical
  have h1 : popc m = ((Finset.range 16).filter (fun w => m.testBit w = true)).card := by
    simp only [popc, members, Finset.card, Finset.filter_val, Finset.range_val, Multiset.range,
      Multiset.filter_coe, Multiset.coe_card]
    simp
  have h2 : Nat.card H = (Finset.univ.filter (fun v : Bits 4 => v ∈ H)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [h1, h2]
  refine Finset.card_bij (fun v _ => v.1) ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨v.lt16, (hm v.1 v.lt16).2 ?_⟩
    rw [dec4_val']; exact hv
  · intro a _ b _ h; exact Subtype.ext h
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_range] at hw
    refine ⟨dec4 w, ?_, dec4_val hw.1⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hm w hw.1).1 hw.2

theorem closure_mask {T : Set (Bits 4)} {l : List ℕ} (hl : ∀ x ∈ l, x < 16)
    (hT : ∀ v : Bits 4, v ∈ T ↔ v.1 ∈ l) :
    ∀ w, w < 16 → ((spanMask l).testBit w = true ↔ dec4 w ∈ Subgroup.closure T) := by
  intro w hw
  constructor
  · refine span_min (Subgroup.closure T) (fun x hx => ⟨hl x hx, ?_⟩) w hw
    exact Subgroup.subset_closure ((hT _).2 (by rw [dec4_val (hl x hx)]; exact hx))
  · intro h
    have hle : Subgroup.closure T ≤ subOfMask (spanMask l) (span_mem hl) := by
      rw [Subgroup.closure_le]
      intro v hv
      exact span_gen hl v.1 ((hT v).1 hv)
    have := hle h
    rwa [mem_subOfMask, dec4_val hw] at this

theorem card_closure {T : Set (Bits 4)} {l : List ℕ} (hl : ∀ x ∈ l, x < 16)
    (hT : ∀ v : Bits 4, v ∈ T ↔ v.1 ∈ l) :
    Nat.card (Subgroup.closure T) = popc (spanMask l) :=
  card_eq_popc _ (closure_mask hl hT)

@[expose] def colsOf (f : Bits 4 →* Bits 4) : List ℕ :=
  [(f (dec4 1)).1, (f (dec4 2)).1, (f (dec4 4)).1, (f (dec4 8)).1]

theorem mulVec_colsOf (f : Bits 4 →* Bits 4) (v : Bits 4) :
    mulVec (colsOf f) v.1 = (f v).1 := by
  have key : ∀ (a b c : ℕ), a < 16 → b < 16 → c < 16 → a ^^^ b = c →
      (f (dec4 c)).1 = (f (dec4 a)).1 ^^^ (f (dec4 b)).1 := by
    intro a b c ha hb hc h
    have : dec4 c = dec4 a * dec4 b := by rw [← h]; exact dec4_xor ha hb
    rw [this, map_mul]; rfl
  have hv16 := v.lt16
  rw [← dec4_val' v]
  generalize v.1 = k at hv16
  rw [dec4_val hv16]
  have k3 := key 1 2 3 (by decide) (by decide) (by decide) (by decide)
  have k5 := key 1 4 5 (by decide) (by decide) (by decide) (by decide)
  have k6 := key 2 4 6 (by decide) (by decide) (by decide) (by decide)
  have k7 := key 3 4 7 (by decide) (by decide) (by decide) (by decide)
  have k9 := key 1 8 9 (by decide) (by decide) (by decide) (by decide)
  have k10 := key 2 8 10 (by decide) (by decide) (by decide) (by decide)
  have k11 := key 3 8 11 (by decide) (by decide) (by decide) (by decide)
  have k12 := key 4 8 12 (by decide) (by decide) (by decide) (by decide)
  have k13 := key 5 8 13 (by decide) (by decide) (by decide) (by decide)
  have k14 := key 6 8 14 (by decide) (by decide) (by decide) (by decide)
  have k15 := key 7 8 15 (by decide) (by decide) (by decide) (by decide)
  have k0 : (f (dec4 0)).1 = 0 := by rw [dec4_zero, map_one]; rfl
  interval_cases k <;> simp [colsOf, mulVec, Nat.xor_assoc, *]

theorem colsOf_injective {f g : Bits 4 →* Bits 4} (h : colsOf f = colsOf g) : f = g := by
  ext v
  have h1 := mulVec_colsOf f v
  have h2 := mulVec_colsOf g v
  rw [h] at h1
  exact Subtype.ext (h1.symm.trans h2)

theorem colsOf_comp (f g : Bits 4 →* Bits 4) : colsOf (f.comp g) = mul (colsOf f) (colsOf g) := by
  have h : ∀ v : Bits 4, mulVec (colsOf f) v.1 = (f v).1 := mulVec_colsOf f
  unfold mul
  conv_rhs =>
    rw [show colsOf g = [(g (dec4 1)).1, (g (dec4 2)).1, (g (dec4 4)).1, (g (dec4 8)).1] from rfl]
  simp only [List.map, h]
  rfl

theorem colsOf_id : colsOf (MonoidHom.id (Bits 4)) = idM := by
  simp only [colsOf, idM, MonoidHom.id_apply]
  rw [dec4_val (by decide), dec4_val (by decide), dec4_val (by decide), dec4_val (by decide)]

@[expose] def dec2 (w : ℕ) : Bits 2 :=
  ⟨w % 4, by have := Nat.mod_lt w (show 0 < 4 by decide); simpa using this⟩

theorem dec2_val {w : ℕ} (h : w < 4) : (dec2 w).1 = w := Nat.mod_eq_of_lt h

@[expose] def colsOf2 (f : Bits 2 →* Bits 2) : List ℕ := [(f (dec2 1)).1, (f (dec2 2)).1]

theorem mulVec_colsOf2 (f : Bits 2 →* Bits 2) (v : Bits 2) :
    mulVec (colsOf2 f) v.1 = (f v).1 := by
  have hv4 := v.lt4
  have hv : v = dec2 v.1 := Subtype.ext (dec2_val hv4).symm
  have k3 : (f (dec2 3)).1 = (f (dec2 1)).1 ^^^ (f (dec2 2)).1 := by
    have : dec2 3 = dec2 1 * dec2 2 := Subtype.ext (by decide)
    rw [this, map_mul]; rfl
  have k0 : (f (dec2 0)).1 = 0 := by
    have : dec2 0 = 1 := Subtype.ext rfl
    rw [this, map_one]; rfl
  rw [hv]
  rw [dec2_val hv4]
  generalize v.1 = k at hv4
  interval_cases k <;> simp [colsOf2, mulVec, *]

theorem mulVec_zero (A : List ℕ) : mulVec A 0 = 0 := by
  induction A with
  | nil => rfl
  | cons a as ih => simp [mulVec, ih]

theorem A0_of_linear (c₀ c₁ c₂ c₃ : ℕ) (h₀ : c₀ < 16) (h₁ : c₁ < 16) (h₂ : c₂ < 16)
    (h₃ : c₃ < 16) (g : List ℕ) (hg : g ∈ gl2)
    (hq : ∀ v, v < 16 → qv (mulVec [c₀, c₁, c₂, c₃] v) = mulVec g (qv v))
    (hi : ∀ v, v < 16 → v ≠ 0 → mulVec [c₀, c₁, c₂, c₃] v ≠ 0) :
    [c₀, c₁, c₂, c₃] ∈ A0 := by
  have q1 : qv c₀ = 0 := by
    have := hq 1 (by decide)
    have e : qv 1 = 0 := by decide
    simpa [mulVec, e, mulVec_zero] using this
  have q2 : qv c₁ = 0 := by
    have := hq 2 (by decide)
    have e : qv 2 = 0 := by decide
    simpa [mulVec, e, mulVec_zero] using this
  have q4 : qv c₂ = 0 := by
    have := hq 4 (by decide)
    have e : qv 4 = 0 := by decide
    simpa [mulVec, e, mulVec_zero] using this
  have q8 : qv c₃ = 0 := by
    have := hq 8 (by decide)
    have e : qv 8 = 0 := by decide
    simpa [mulVec, e, mulVec_zero] using this
  have q3 : qv (c₀ ^^^ c₁) = 0 := by
    have := hq 3 (by decide)
    have e : qv 3 = 0 := by decide
    simpa [mulVec, e, mulVec_zero] using this
  have q12 : qv (c₂ ^^^ c₃) = 0 := by
    have := hq 12 (by decide)
    have e : qv 12 = 0 := by decide
    simpa [mulVec, e, mulVec_zero] using this
  refine A0_complete c₀ (zero0_of h₀ q1) c₁ (zero0_of h₁ q2) (zero0_of (xor_lt16 h₀ h₁) q3)
    c₂ (zero0_of h₂ q4) c₃ (zero0_of h₃ q8) (zero0_of (xor_lt16 h₂ h₃) q12) ?_ ?_
  · simp only [okQ, List.any_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq]
    exact ⟨g, hg, fun v hv => hq v hv⟩
  · simp only [okInj, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, bne_iff_ne,
      ne_eq]
    intro v hv
    by_cases h : v = 0
    · exact Or.inl h
    · exact Or.inr (hi v hv h)

theorem colsOf_mem_A0 (σ : Bits 4 →* Bits 4) (hσ : Function.Injective σ) (γ : Bits 2 →* Bits 2)
    (hγ : Function.Injective γ) (hq : ∀ v : Bits 4, γ (qB v) = qB (σ v)) : colsOf σ ∈ A0 := by
  have hcols : colsOf σ = [(σ (dec4 1)).1, (σ (dec4 2)).1, (σ (dec4 4)).1, (σ (dec4 8)).1] := rfl
  have hg : colsOf2 γ ∈ gl2 := by
    have e : colsOf2 γ = [(γ (dec2 1)).1, (γ (dec2 2)).1] := rfl
    have n1 : dec2 1 ≠ 1 := fun h => by have := congrArg Subtype.val h; simp [dec2] at this
    have n2 : dec2 2 ≠ 1 := fun h => by have := congrArg Subtype.val h; simp [dec2] at this
    have n12 : dec2 1 ≠ dec2 2 := fun h => by have := congrArg Subtype.val h; simp [dec2] at this
    rw [e]
    refine gl2_of (γ (dec2 1)).lt4 (γ (dec2 2)).lt4 ?_ ?_ ?_
    · intro h
      have : γ (dec2 1) = γ 1 := by rw [map_one]; exact Subtype.ext h
      exact n1 (hγ this)
    · intro h
      have : γ (dec2 2) = γ 1 := by rw [map_one]; exact Subtype.ext h
      exact n2 (hγ this)
    · intro h
      exact n12 (hγ (Subtype.ext h))
  have e1 : ∀ v, v < 16 → mulVec [(σ (dec4 1)).1, (σ (dec4 2)).1, (σ (dec4 4)).1,
      (σ (dec4 8)).1] v = (σ (dec4 v)).1 := by
    intro v hv
    have := mulVec_colsOf σ (dec4 v)
    rwa [dec4_val hv] at this
  rw [hcols]
  refine A0_of_linear _ _ _ _ (σ _).lt16 (σ _).lt16 (σ _).lt16 (σ _).lt16 (colsOf2 γ) hg ?_ ?_
  · intro v hv
    rw [e1 v hv]
    have e2 := mulVec_colsOf2 γ (qB (dec4 v))
    have e3 : (qB (dec4 v)).1 = qv v := by rw [qB_val, dec4_val hv]
    rw [e3] at e2
    rw [e2, hq, qB_val]
  · intro v hv hv0 h
    rw [e1 v hv] at h
    have h1 : σ (dec4 v) = σ 1 := by rw [map_one]; exact Subtype.ext h
    have h2 := hσ h1
    have h3 := congrArg Subtype.val h2
    rw [dec4_val hv] at h3
    exact hv0 h3
