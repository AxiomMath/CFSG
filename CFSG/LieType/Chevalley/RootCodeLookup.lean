module

public import CFSG.Blueprint.ChevalleyRootsInputs

public section

namespace CFSG.Blueprint.Chevalley.RootCode

@[expose] def codeL : List Int → Nat
  | [] => 0
  | x :: xs => (x + 8).toNat + 16 * codeL xs

@[expose] def code {n : Nat} (v : Fin n → Int) : Nat := codeL (List.ofFn v)

@[expose] def inRange {n : Nat} (v : Fin n → Int) : Bool :=
  (List.ofFn v).all fun x => decide (-8 ≤ x) && decide (x < 8)

@[expose] def dec (n c : Nat) : Fin n → Int := fun j => ((c / 16 ^ (j : Nat) % 16 : Nat) : Int) - 8

theorem code_succ {n : Nat} (v : Fin (n + 1) → Int) :
    code v = (v 0 + 8).toNat + 16 * code (fun i : Fin n => v i.succ) := by
  simp only [code, List.ofFn_succ, codeL]

theorem inRange_succ {n : Nat} (v : Fin (n + 1) → Int) :
    inRange v = ((decide (-8 ≤ v 0) && decide (v 0 < 8)) && inRange (fun i : Fin n => v i.succ)) := by
  simp only [inRange, List.ofFn_succ, List.all_cons]

theorem dec_code : ∀ (n : Nat) (v : Fin n → Int), inRange v = true → dec n (code v) = v
  | 0, v, _ => funext fun j => j.elim0
  | n + 1, v, h => by
    rw [inRange_succ] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have ih := dec_code n _ h3
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [dec, Fin.val_zero, Nat.pow_zero, Nat.div_one]
      rw [code_succ]
      have : (v 0 + 8).toNat < 16 := by omega
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt this]
      omega
    · have hj := congrFun ih j
      simp only [dec, Fin.val_succ] at hj ⊢
      rw [code_succ, Nat.pow_succ, Nat.mul_comm (16 ^ (j : Nat)) 16, ← Nat.div_div_eq_div_mul]
      have : (v 0 + 8).toNat < 16 := by omega
      rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt this, Nat.zero_add]
      exact hj

theorem code_dec : ∀ (n c : Nat), c < 16 ^ n → code (dec n c) = c
  | 0, c, h => by simp only [Nat.pow_zero] at h; simp only [code, List.ofFn_zero, codeL]; omega
  | n + 1, c, h => by
    rw [code_succ]
    have e : (fun i : Fin n => dec (n + 1) c i.succ) = dec n (c / 16) := by
      funext i
      simp only [dec, Fin.val_succ, Nat.pow_succ, Nat.mul_comm (16 ^ (i : Nat)) 16,
        Nat.div_div_eq_div_mul]
    rw [e, code_dec n (c / 16) (by rw [Nat.pow_succ] at h; omega)]
    simp only [dec, Fin.val_zero, Nat.pow_zero, Nat.div_one]
    have : ((((c % 16 : Nat) : Int) - 8 + 8).toNat) = c % 16 := by omega
    rw [this]
    omega

theorem dec_range (n c : Nat) : inRange (dec n c) = true := by
  simp only [inRange, List.all_eq_true, List.mem_ofFn, Bool.and_eq_true, decide_eq_true_eq]
  rintro x ⟨j, rfl⟩
  simp only [dec]
  omega

theorem mem_iff {n : Nat} (L : List Nat) (hL : L.all (fun c => decide (c < 16 ^ n)) = true)
    (v : Fin n → Int) : (∃ c ∈ L, dec n c = v) ↔ (inRange v && L.contains (code v)) = true := by
  simp only [List.all_eq_true, decide_eq_true_eq] at hL
  simp only [Bool.and_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨dec_range n c, by rw [code_dec n c (hL c hc)]; exact hc⟩
  · rintro ⟨h1, h2⟩
    exact ⟨_, h2, dec_code n v h1⟩


theorem getD0_of_lt {L : List Nat} {k : Nat} (hk : k < L.length) : L.getD k 0 = L[k] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem any_range_getD (L : List Nat) (f : Nat → Bool) :
    (List.range L.length).any (fun k => f (L.getD k 0)) = L.any f := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨k, hk, h⟩
    exact ⟨L[k], List.getElem_mem hk, by rwa [getD0_of_lt hk] at h⟩
  · rintro ⟨c, hc, h⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    exact ⟨k, hk, by rwa [getD0_of_lt hk]⟩

theorem all_range_getD (L : List Nat) (f : Nat → Bool) :
    (List.range L.length).all (fun k => f (L.getD k 0)) = L.all f := by
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro h c hc
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    have := h k hk
    rwa [getD0_of_lt hk] at this
  · intro h k hk
    rw [getD0_of_lt hk]
    exact h _ (List.getElem_mem hk)


theorem dec_eq {τ : Tag} (c : Nat) : (decodeVec c : Fin τ.rank → Int) = dec τ.rank c := rfl

@[expose] def CodesFit {τ : Tag} (C : RootCertificate τ) : Bool :=
  C.roots.all fun c => decide (c < 16 ^ τ.rank)

theorem exists_root_iff {τ : Tag} (C : RootCertificate τ) (hL : CodesFit C = true)
    (w : Fin τ.rank → Int) :
    (∃ k, k < C.roots.length ∧ C.root k = w) ↔ (inRange w && C.roots.contains (code w)) = true := by
  rw [← mem_iff C.roots hL w]
  constructor
  · rintro ⟨k, hk, hkw⟩
    exact ⟨C.roots[k], List.getElem_mem hk, by rw [← hkw, RootCertificate.root, getD0_of_lt hk, dec_eq]⟩
  · rintro ⟨c, hc, hcw⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    exact ⟨k, hk, by rw [RootCertificate.root, getD0_of_lt hk, dec_eq]; exact hcw⟩

theorem any_root_eq {τ : Tag} (C : RootCertificate τ) (hL : CodesFit C = true)
    (w : Fin τ.rank → Int) [∀ k, Decidable (C.root k = w)] :
    ((List.range C.roots.length).any fun k => decide (C.root k = w)) =
      (inRange w && C.roots.contains (code w)) := by
  apply Bool.eq_iff_iff.2
  rw [← exists_root_iff C hL w]
  simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq]

@[expose] def buckets (L : List Nat) : List (List Nat) :=
  (List.range 64).map fun b => L.filter fun c => c % 64 == b

@[expose] def memB (L : List Nat) (x : Nat) : Bool := ((buckets L).getD (x % 64) []).contains x

theorem memB_eq (L : List Nat) (x : Nat) : memB L x = L.contains x := by
  have hx : x % 64 < (buckets L).length := by
    simp only [buckets, List.length_map, List.length_range]; exact Nat.mod_lt _ (by decide)
  have hb : (buckets L).getD (x % 64) [] = L.filter fun c => c % 64 == x % 64 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx, Option.getD_some]
    simp only [buckets, List.getElem_map, List.getElem_range]
  apply Bool.eq_iff_iff.2
  rw [memB, hb, List.contains_iff_mem, List.contains_iff_mem, List.mem_filter]
  simp only [beq_self_eq_true, and_true]

theorem all_swap_any (N : Nat) (g : Nat → Nat → Bool) (e : Nat → Nat → Nat → Bool) :
    ((List.range N).all fun k => (List.range 7).all fun a => (List.range 7).all fun b =>
      !(g a b && e k a b)) =
    ((List.range 7).all fun a => (List.range 7).all fun b =>
      !(g a b) || !((List.range N).any fun k => e k a b)) := by
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_false_iff,
    Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false]
  constructor
  · intro h a ha b hb
    cases hg : g a b
    · exact Or.inl rfl
    · refine Or.inr fun k hk hkw => ?_
      rcases h k hk a ha b hb with h' | h'
      · rw [hg] at h'; exact Bool.noConfusion h'
      · rw [hkw] at h'; exact Bool.noConfusion h'
  · intro h k hk a ha b hb
    rcases h a ha b hb with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Bool.eq_false_iff.2 (h' k hk))

end CFSG.Blueprint.Chevalley.RootCode
