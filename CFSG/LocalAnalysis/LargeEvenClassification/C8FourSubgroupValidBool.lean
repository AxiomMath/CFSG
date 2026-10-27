module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupCertificate

public section

namespace CFSG.LargeEvenClassification.Helpers

@[expose] noncomputable def c8K_bit (m i : ℕ) : Bool := Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 i))

theorem c8K_bit_iff (m i : ℕ) : c8K_bit m i = true ↔ m.testBit i = true := by
  change Nat.blt 0 (m &&& 1 <<< i) = true ↔ _
  rw [Nat.blt_eq, Nat.one_shiftLeft, Nat.and_two_pow]
  cases m.testBit i <;> simp

@[expose] noncomputable def c8K_mulN (a b : ℕ) : ℕ :=
  Nat.mod (Nat.add (Nat.add (Nat.add
    (Nat.mul (Nat.div (Nat.mod (Nat.add
      (Nat.mul (Nat.add (Nat.mul 2 (Nat.div a 32)) 1) (Nat.add (Nat.mul 2 (Nat.div b 32)) 1))
      (Nat.mul 2 (Nat.mul (Nat.mod (Nat.div a 8) 4) (Nat.mod (Nat.div b 2) 4)))) 8) 2) 32)
    (Nat.mul (Nat.mod (Nat.add
      (Nat.mul (Nat.add (Nat.mul 2 (Nat.div a 32)) 1) (Nat.mod (Nat.div b 8) 4))
      (Nat.mul (Nat.mod (Nat.div a 8) 4) (Nat.add (Nat.mul 2 (Nat.mod b 2)) 1))) 4) 8))
    (Nat.mul (Nat.mod (Nat.add
      (Nat.mul (Nat.mod (Nat.div a 2) 4) (Nat.add (Nat.mul 2 (Nat.div b 32)) 1))
      (Nat.mul (Nat.add (Nat.mul 2 (Nat.mod a 2)) 1) (Nat.mod (Nat.div b 2) 4))) 4) 2))
    (Nat.div (Nat.mod (Nat.add
      (Nat.mul 2 (Nat.mul (Nat.mod (Nat.div a 2) 4) (Nat.mod (Nat.div b 8) 4)))
      (Nat.mul (Nat.add (Nat.mul 2 (Nat.mod a 2)) 1) (Nat.add (Nat.mul 2 (Nat.mod b 2)) 1))) 4) 2))
    128

set_option maxRecDepth 10000 in
theorem c8K_mulN_eq : ∀ g h : C8FourCode,
    (c8FourMultiply g h).index.val = c8K_mulN g.index.val h.index.val := by
  decide +kernel

theorem c8K_and_eq (a b : Bool) : Bool.and' a b = (a && b) := by
  cases a <;> rfl

@[expose] noncomputable def c8K_all {α : Type} (p : α → Bool) (L : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => Bool.and' (p x) ih) L

theorem c8K_all_iff {α : Type} (p : α → Bool) :
    ∀ L : List α, c8K_all p L = true ↔ ∀ x ∈ L, p x = true
  | [] => by simp [c8K_all]
  | x :: L => by
    change (p x && c8K_all p L) = true ↔ _
    rw [Bool.and_eq_true, c8K_all_iff p L, List.forall_mem_cons]

@[expose] noncomputable def c8K_keysEq (W : List (C8FourCode × ℕ × Fin 32)) :
    List C8FourCode → Bool :=
  List.rec (motive := fun _ => List C8FourCode → Bool)
    (fun E => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) E)
    (fun e _ ih E => List.rec (motive := fun _ => Bool) false
      (fun g E' _ => Bool.and' (Nat.beq e.1.index.val g.index.val) (ih E')) E) W

theorem c8K_keysEq_spec : ∀ (W : List (C8FourCode × ℕ × Fin 32)) (E : List C8FourCode),
    c8K_keysEq W E = true → W.map Prod.fst = E
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | e :: W, g :: E, h => by
    change (Nat.beq e.1.index.val g.index.val && c8K_keysEq W E) = true at h
    rw [Bool.and_eq_true, Nat.beq_eq] at h
    rw [List.map_cons, c8K_keysEq_spec W E h.2]
    congr 1
    cases e with
    | mk c _ =>
      cases c with
      | mk ci =>
        cases g with
        | mk gi =>
          exact congrArg C8FourCode.mk (Fin.ext h.1)

@[expose] noncomputable def c8K_lane (V i : ℕ) : ℕ := Nat.land (Nat.shiftRight V (Nat.mul 5 i)) 31

@[expose] noncomputable def c8K_vt (W : List (C8FourCode × ℕ × Fin 32)) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun e _ ih => Nat.lor (Nat.shiftLeft e.2.2.val (Nat.mul 5 e.1.index.val)) ih) W

@[expose] noncomputable def c8K_force (x : ℕ) (k : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) x

theorem c8K_force_eq (x : ℕ) (k : ℕ → Bool) : c8K_force x k = k x := by
  cases x <;> rfl

@[expose] noncomputable def c8K_chk (r : C8FourSubgroupRecord) : Bool :=
  Bool.and' (c8K_all (fun g => Bool.and' (c8K_bit r.mask (c8FourInverse g).index.val)
      (c8K_all (fun h => c8K_bit r.mask (c8K_mulN g.index.val h.index.val)) r.elements)) r.elements)
    (Bool.and' (c8K_keysEq r.wordData r.elements)
      (c8K_force (c8K_vt r.wordData) (fun V =>
        Bool.and' (c8K_all (fun e => Nat.beq (c8K_lane V e.1.index.val) e.2.2.val) r.wordData)
          (c8K_all (fun g => c8K_all (fun h =>
            Nat.beq (c8K_lane V (c8K_mulN g.index.val h.index.val))
              (Nat.xor (c8K_lane V g.index.val) (c8K_lane V h.index.val))) r.elements) r.elements))))

theorem c8K_find_vec (V : ℕ) : ∀ (W : List (C8FourCode × ℕ × Fin 32)),
    (∀ e ∈ W, c8K_lane V e.1.index.val = e.2.2.val) → ∀ g ∈ W.map Prod.fst,
      ((W.find? (fun entry => entry.1 = g)).getD (g, 0, 0)).2.2.val = c8K_lane V g.index.val
  | [], _, g, hg => by simp at hg
  | e :: W, hW, g, hg => by
    by_cases he : e.1 = g
    · rw [List.find?_cons_of_pos (by simpa using he), Option.getD_some, ← he]
      exact (hW e List.mem_cons_self).symm
    · rw [List.find?_cons_of_neg (by simpa using he)]
      have hg' : g ∈ W.map Prod.fst := by
        rw [List.map_cons, List.mem_cons] at hg
        rcases hg with h | h
        · exact absurd h.symm he
        · exact h
      exact c8K_find_vec V W (fun x hx => hW x (List.mem_cons_of_mem _ hx)) g hg'

theorem c8K_valid (r : C8FourSubgroupRecord)
    (h1 : ∀ g : C8FourCode, c8FourRecordMem r g ↔ g ∈ r.elements)
    (h2 : c8FourRecordMem r 1)
    (h4 : certificateListAll r.generators (c8FourRecordMem r))
    (h5 : certificateListAll r.elements (fun g =>
      c8FourRecordWordProduct r g = g ∧
      certificateListAll (c8FourRecordWord r g) (fun i => i < r.generators.length) ∧
      c8FourWordVector (c8FourRecordWord r g) = c8FourVector r g))
    (h6 : c8FourVector r 1 = 0)
    (h8 : r.generators.length ≤ 5)
    (hc : c8K_chk r = true) : c8FourRecordValid r := by
  unfold c8K_chk at hc
  rw [c8K_force_eq] at hc
  simp only [c8K_and_eq, Bool.and_eq_true, c8K_all_iff, c8K_bit_iff, Nat.beq_eq] at hc
  obtain ⟨hcl, hk, hwd, hv⟩ := hc
  have hkeys := c8K_keysEq_spec _ _ hk
  have hmem : ∀ g h, g ∈ r.elements → h ∈ r.elements →
      c8FourCertificateProduct g h ∈ r.elements := by
    intro g h hg hh
    have := (hcl g hg).2 h hh
    rw [← c8K_mulN_eq] at this
    exact (h1 _).1 this
  have hvec : ∀ g ∈ r.elements, (c8FourVector r g).val = c8K_lane (c8K_vt r.wordData) g.index.val := by
    intro g hg
    refine c8K_find_vec _ r.wordData hwd g ?_
    rw [hkeys]
    exact hg
  refine ⟨h1, h2, ?_, h4, h5, h6, ?_, h8⟩
  · exact (certificateListAll_iff _ _).2 fun g hg => ⟨(hcl g hg).1, (certificateListAll_iff _ _).2
      fun h hh => (h1 _).2 (hmem g h hg hh)⟩
  · refine (certificateListAll_iff _ _).2 fun g hg => (certificateListAll_iff _ _).2 fun h hh => ?_
    have he := hv g hg h hh
    apply Fin.ext
    rw [hvec _ (hmem g h hg hh), hvec g hg, hvec h hh, Fin.val_ofNat]
    change c8K_lane _ (c8FourMultiply g h).index.val = _
    rw [c8K_mulN_eq, he]
    have ha : c8K_lane (c8K_vt r.wordData) g.index.val < 2 ^ 5 := by
      change Nat.land _ 31 < 32
      exact lt_of_le_of_lt Nat.and_le_right (by norm_num)
    have hb : c8K_lane (c8K_vt r.wordData) h.index.val < 2 ^ 5 := by
      change Nat.land _ 31 < 32
      exact lt_of_le_of_lt Nat.and_le_right (by norm_num)
    exact (Nat.mod_eq_of_lt (Nat.xor_lt_two_pow ha hb)).symm

end CFSG.LargeEvenClassification.Helpers
