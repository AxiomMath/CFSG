module

public import Certificates.Data.Kernel.J3Coset
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Certificates.Kernel.Spor.Loops
public import Mathlib.GroupTheory.Index

public section

namespace CFSG.KC.J3C

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb

theorem wv_nil (T : Nat → Nat → Nat) (y : Nat) : wv T [] y = y := rfl

theorem wv_cons (T : Nat → Nat → Nat) (c : Nat) (w : List Nat) (y : Nat) :
    wv T (c :: w) y = T c (wv T w y) :=
  strictN_eq _ _

theorem wv_append (T : Nat → Nat → Nat) (u v : List Nat) (y : Nat) :
    wv T (u ++ v) y = wv T u (wv T v y) := by
  induction u with
  | nil => rfl
  | cons c u ih => rw [List.cons_append, wv_cons, wv_cons, ih]

@[expose] def ev {G : Type*} [Group G] (g : ℕ → G) (w : List ℕ) : G := (w.map g).prod

theorem ev_nil {G : Type*} [Group G] (g : ℕ → G) : ev g [] = 1 := rfl

theorem ev_cons {G : Type*} [Group G] (g : ℕ → G) (c : ℕ) (w : List ℕ) :
    ev g (c :: w) = g c * ev g w := by
  simp [ev]

theorem ev_append {G : Type*} [Group G] (g : ℕ → G) (u v : List ℕ) :
    ev g (u ++ v) = ev g u * ev g v := by
  simp [ev]

theorem map_ev {G H : Type*} [Group G] [Group H] (f : G →* H) (g : ℕ → G) (w : List ℕ) :
    f (ev g w) = ev (fun c => f (g c)) w := by
  simp [ev, map_list_prod, Function.comp_def]

theorem ev_mem {G : Type*} [Group G] {S : Subgroup G} {g : ℕ → G} {w : List ℕ}
    (h : ∀ c ∈ w, g c ∈ S) : ev g w ∈ S := by
  induction w with
  | nil => exact S.one_mem
  | cons c w ih =>
    rw [ev_cons]
    exact S.mul_mem (h c List.mem_cons_self) (ih fun d hd => h d (List.mem_cons_of_mem c hd))

theorem act_ev {G : Type*} [Group G] {n : ℕ} (ρ : G →* Equiv.Perm (Fin n)) (g : ℕ → G)
    (T : Nat → Nat → Nat) (w : List ℕ)
    (h : ∀ c ∈ w, ∀ i : Fin n, (ρ (g c) i).val = T c i.val) :
    ∀ i : Fin n, (ρ (ev g w) i).val = wv T w i.val := by
  induction w with
  | nil => intro i; rw [ev_nil, map_one]; rfl
  | cons c w ih =>
    intro i
    rw [ev_cons, map_mul, Equiv.Perm.mul_apply, wv_cons,
      h c List.mem_cons_self, ih fun d hd => h d (List.mem_cons_of_mem c hd)]

theorem fgen_lt (e : Nat) : fgen e < 4 := by
  unfold fgen
  have := Nat.and_le_right (n := Nat.shiftRight e 15) (m := 3)
  change Nat.land (Nat.shiftRight e 15) 3 < 4
  exact Nat.lt_of_le_of_lt this (by decide)

theorem fOK_spec {n : Nat} {FE : Nat → Nat} {G : Nat → Nat → Nat} {R : Nat → Nat} {p : Nat}
    (h : fOK n FE G R p = true) :
    R (frt (FE p)) = p ∨ (fpar (FE p) < n ∧ ford (FE (fpar (FE p))) < ford (FE p) ∧
      frt (FE (fpar (FE p))) = frt (FE p) ∧ G (fgen (FE p)) (fpar (FE p)) = p) := by
  unfold fOK at h
  rw [strictB_eq] at h
  by_cases hr : R (frt (FE p)) = p
  · exact Or.inl hr
  · right
    have hb : Nat.beq (R (frt (FE p))) p = false := by
      rw [Bool.eq_false_iff]
      intro h'
      exact hr (Nat.eq_of_beq_eq_true h')
    rw [hb] at h
    change strictB (fpar (FE p)) _ = true at h
    rw [strictB_eq, bAnd_iff, strictB_eq, bAnd_iff, bAnd_iff, Nat.blt_eq, Nat.blt_eq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨h1, h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4⟩

theorem forest_reach {G' : Type*} [Group G'] {n : ℕ} (ρ : G' →* Equiv.Perm (Fin n))
    {FE : ℕ → ℕ} {Gm : ℕ → ℕ → ℕ} {R : ℕ → ℕ} (hf : ∀ p < n, fOK n FE Gm R p = true)
    (S : Subgroup G') (gens : ℕ → G') (hgS : ∀ j < 4, gens j ∈ S)
    (hg : ∀ j < 4, ∀ i : Fin n, (ρ (gens j) i).val = Gm j i.val) :
    ∀ p (hp : p < n), ∃ r, ∃ hr : r < n, R (frt (FE p)) = r ∧
      ∃ k ∈ S, ρ k ⟨r, hr⟩ = ⟨p, hp⟩ := by
  have key : ∀ d, ∀ p (hp : p < n), ford (FE p) = d → ∃ r, ∃ hr : r < n,
      R (frt (FE p)) = r ∧ ∃ k ∈ S, ρ k ⟨r, hr⟩ = ⟨p, hp⟩ := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro p hp hd
      rcases fOK_spec (hf p hp) with hroot | ⟨hq, hord, hrt, hgen⟩
      · exact ⟨p, hp, hroot, 1, S.one_mem, by simp⟩
      · obtain ⟨r, hr, hRr, k, hk, hkr⟩ := ih _ (hd ▸ hord) _ hq rfl
        refine ⟨r, hr, hrt ▸ hRr, gens (fgen (FE p)) * k,
          S.mul_mem (hgS _ (fgen_lt _)) hk, ?_⟩
        rw [map_mul, Equiv.Perm.mul_apply, hkr]
        apply Fin.ext
        rw [hg _ (fgen_lt _)]
        exact hgen
  exact fun p hp => key _ p hp rfl

theorem relPt_spec {T : Nat → Nat → Nat} {rs : List (List Nat)} {y : Nat}
    (h : relPt T rs y = true) : ∀ r ∈ rs, wv T r y = y := by
  induction rs with
  | nil => intro r hr; exact absurd hr List.not_mem_nil
  | cons r rs ih =>
    change Bool.rec (motive := fun _ => Bool) false (relPt T rs y) (Nat.beq (wv T r y) y) =
      true at h
    rw [bAnd_iff] at h
    intro r' hr'
    rcases List.mem_cons.1 hr' with rfl | hr'
    · exact Nat.eq_of_beq_eq_true h.1
    · exact ih h.2 r' hr'

theorem baseEq_spec {T : Nat → Nat → Nat} {b : Nat} {w v : List Nat}
    (h : baseEq T b w v = true) : wv T w 0 = wv T v 0 ∧ wv T w b = wv T v b := by
  unfold baseEq at h
  rw [bAnd_iff] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem baseEq_of {T : Nat → Nat → Nat} {b : Nat} {w v : List Nat}
    (h0 : wv T w 0 = wv T v 0) (hb : wv T w b = wv T v b) : baseEq T b w v = true := by
  unfold baseEq
  rw [bAnd_iff, h0, hb]
  exact ⟨Nat.beq_refl _, Nat.beq_refl _⟩

theorem sortedAux_pairwise : ∀ (l : List Nat) (x : Nat),
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun y _ ih x => Bool.rec (motive := fun _ => Bool) false (ih y) (Nat.blt x y)) l x = true →
    (x :: l).Pairwise (· < ·)
  | [], x, _ => List.pairwise_singleton _ x
  | y :: l, x, h => by
    change Bool.rec (motive := fun _ => Bool) false _ (Nat.blt x y) = true at h
    rw [bAnd_iff, Nat.blt_eq] at h
    have hp := sortedAux_pairwise l y h.2
    refine List.Pairwise.cons ?_ hp
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact h.1
    · exact Nat.lt_trans h.1 (List.rel_of_pairwise_cons hp hz)

theorem sortedB_pairwise {l : List Nat} (h : sortedB l = true) : l.Pairwise (· < ·) := by
  cases l with
  | nil => exact List.Pairwise.nil
  | cons x l => exact sortedAux_pairwise l x h

theorem memB_iff (m x : Nat) : memB m x = true ↔ m.testBit x = true := by
  unfold memB
  rw [Nat.testBit, Nat.beq_eq]
  have h1 : Nat.land (Nat.shiftRight m x) 1 = (m >>> x) % 2 := Nat.and_one_is_mod _
  rw [h1]
  have h2 : 1 &&& (m >>> x) = (m >>> x) % 2 := by
    rw [Nat.and_comm]; exact Nat.and_one_is_mod _
  rw [h2]
  rcases Nat.mod_two_eq_zero_or_one (m >>> x) with h | h <;> simp [h]

theorem testBit_maskOf {α : Type} (l : List (Nat × α)) (x : Nat) :
    (maskOf l).testBit x = true ↔ ∃ r ∈ l, r.1 = x := by
  induction l with
  | nil =>
    change Nat.testBit 0 x = true ↔ _
    simp
  | cons r l ih =>
    change (Nat.lor (maskOf l) (Nat.shiftLeft 1 r.1)).testBit x = true ↔ _
    have e : Nat.lor (maskOf l) (Nat.shiftLeft 1 r.1) = maskOf l ||| (1 <<< r.1) := rfl
    rw [e, Nat.testBit_or, Bool.or_eq_true, ih, Nat.testBit_shiftLeft]
    simp only [List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · left
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hge, hb⟩ := h
        have : x - r.1 = 0 := by
          by_contra hne
          rw [Nat.testBit_one_eq_true_iff_self_eq_zero] at hb
          exact hne hb
        omega
    · rintro (h | h)
      · right
        rw [h]
        simp
      · exact Or.inl h

theorem memB_maskOf {α : Type} (l : List (Nat × α)) (x : Nat) :
    memB (maskOf l) x = true ↔ ∃ r ∈ l, r.1 = x := by
  rw [memB_iff, testBit_maskOf]

theorem ncard_val_mem {n : ℕ} {L : List ℕ} (hL : L.Nodup) (hlt : ∀ x ∈ L, x < n) :
    {q : Fin n | q.val ∈ L}.ncard = L.length := by
  have himg : Fin.val '' {q : Fin n | q.val ∈ L} = (L.toFinset : Set ℕ) := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, Finset.mem_coe, List.mem_toFinset]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hx
      exact ⟨⟨x, hlt x hx⟩, hx, rfl⟩
  rw [← Set.ncard_image_of_injective _ Fin.val_injective, himg, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hL]

theorem eq_one_of_orbit {G Ω : Type*} [Group G] [MulAction G Ω] [Finite Ω] {K : Subgroup G}
    [Finite K] {b : Ω} {S : Set Ω} (hS : S ⊆ MulAction.orbit K b) (hcard : Nat.card K ≤ S.ncard)
    {k : G} (hk : k ∈ K) (hkb : k • b = b) : k = 1 := by
  have hidx := Subgroup.card_mul_index (MulAction.stabilizer K b)
  rw [MulAction.index_stabilizer] at hidx
  have hle : S.ncard ≤ (MulAction.orbit K b).ncard := Set.ncard_le_ncard hS (Set.toFinite _)
  have hpos : 0 < (MulAction.orbit K b).ncard :=
    Set.ncard_pos (Set.toFinite _) |>.2 ⟨b, MulAction.mem_orbit_self b⟩
  have hst : Nat.card (MulAction.stabilizer K b) ≤ 1 := by
    by_contra hc
    push Not at hc
    have : (MulAction.orbit K b).ncard * 2 ≤ Nat.card K := by
      rw [← hidx, Nat.mul_comm]
      exact Nat.mul_le_mul_right _ hc
    omega
  have hmem : (⟨k, hk⟩ : K) ∈ MulAction.stabilizer K b := hkb
  have := (Finite.card_le_one_iff_subsingleton.1 hst)
  have h1 : (⟨⟨k, hk⟩, hmem⟩ : MulAction.stabilizer K b) = 1 := Subsingleton.elim _ _
  have h2 := congrArg (fun x : MulAction.stabilizer K b => ((x : K) : G)) h1
  simpa using h2

end CFSG.KC.J3C

end
