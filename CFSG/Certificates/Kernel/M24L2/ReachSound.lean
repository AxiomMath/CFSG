
module

public import CFSG.Certificates.Kernel.M24L2.CtxSound
public import CFSG.Certificates.Kernel.M24L2.BfsClose
public import Certificates.Data.Kernel.M24L2.Gl
public import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.M24L2

open CFSG.Sporadic.Th.Native CFSG.CGT.M24R

@[expose] def InvL (m : Nat) : Prop := ∀ x < 16, lap m x = 0 → x = 0

theorem invB_iff (m : Nat) : invB m = true ↔ InvL m := by
  unfold invB InvL
  rw [letN_eq, CFSG.KS.Raw.Orb.allN_iff]
  constructor
  · intro h x hx h0
    by_contra hne
    have := h (x - 1) (by omega)
    rw [show Nat.add (x - 1) 1 = x by change x - 1 + 1 = x; omega, lapT_fld m x hx, h0] at this
    simp at this
  · intro h x hx
    rw [show Nat.add x 1 = x + 1 from rfl, lapT_fld m (x + 1) (by omega)]
    have h1 : lap m (x + 1) ≠ 0 := fun h0 => by have := h (x + 1) (by omega) h0; omega
    have h2 : Nat.beq (lap m (x + 1)) 0 = false :=
      Bool.eq_false_iff.2 fun h' => h1 (Nat.eq_of_beq_eq_true h')
    rw [h2]
    rfl

theorem lap_mulC_lin {c d : Nat} (hc : c % 16 = 0) (hd : d % 16 = 0) {x : Nat} (hx : x < 16) :
    lap (mulC c d / 16) x = lap (c / 16) (lap (d / 16) x) := by
  have h1 : mulC c d % 16 = 0 := by rw [mulC_mod16, hd, aff_zero_lin hc]
  have := aff_mulC c d x
  rw [aff_eq (mulC c d), aff_eq c, aff_eq d, h1, hc, hd, Nat.zero_xor, Nat.zero_xor, Nat.zero_xor]
    at this
  exact this

theorem invL_mulC {c d : Nat} (hc : c % 16 = 0) (hd : d % 16 = 0) (h1 : InvL (c / 16))
    (h2 : InvL (d / 16)) : InvL (mulC c d / 16) := by
  intro x hx h0
  rw [lap_mulC_lin hc hd hx] at h0
  exact h2 x hx (h1 _ (lap_lt _ _) h0)

theorem invL_letters : ∀ l ∈ xLetters, invB (lcC l / 16) = true := by
  decide +kernel

theorem invL_word (w : List (Fin 10 × Bool)) (hw : ∀ l ∈ w, l ∈ xLetters) :
    ∀ c, c % 16 = 0 → InvL (c / 16) →
      InvL ((w.foldl (fun c l => mulC c (lcC l)) c) / 16) := by
  induction w with
  | nil => intro c _ h; exact h
  | cons l w ih =>
    intro c hc h
    rw [List.foldl_cons]
    have hl := hw l List.mem_cons_self
    refine ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) _ ?_ ?_
    · rw [mulC_mod16, lcC_lin l hl, aff_zero_lin hc]
    · exact invL_mulC hc (lcC_lin l hl) h ((invB_iff _).1 (invL_letters l hl))

theorem invL_id : InvL (idC / 16) := by
  intro x hx h0
  rw [show idC / 16 = 33825 from rfl, lap_id x hx] at h0
  exact h0

theorem twin_inv {e : Nat × List (Fin 10 × Bool)} (he : e ∈ lTwin.all) :
    e.1 % 16 = 0 ∧ InvL (keyL e.1) := by
  obtain ⟨_, he1, hl⟩ := lBFS_twin.2.2 e he
  have h16 : e.1 % 16 = 0 := by rw [he1]; exact foldl_lin e.2 hl idC (by decide)
  refine ⟨h16, ?_⟩
  rw [keyL_eq, he1]
  exact invL_word e.2 hl idC (by decide) invL_id

theorem twin_closed {e : Nat × List (Fin 10 × Bool)} (he : e ∈ lTwin.all) :
    Closed keyL lcC xLetters lTwin.all e :=
  bfsT_closed (N := 65536) (fun c hc => by rw [keyL_eq]; omega) idC_lt (le_refl _) e he

@[expose] def KeyT (k : Nat) : Prop := ∃ e ∈ lTwin.all, keyL e.1 = k

theorem keyT_mulX {p : Nat} (hp : KeyT p) {i : Nat} (hi : i < 12) : KeyT (mulX p i) := by
  obtain ⟨e, he, rfl⟩ := hp
  have hl : xLetters.getD i ((0 : Fin 10), true) ∈ xLetters := by
    rw [List.getD_eq_getElem _ _ (by simpa [xLetters] using hi)]
    exact List.getElem_mem _
  obtain ⟨e', he', hk⟩ := twin_closed he _ hl
  refine ⟨e', he', ?_⟩
  rw [hk]
  unfold mulX lcX
  have h16 := (twin_inv he).1
  rw [keyL_eq e.1, show Nat.mul 16 (e.1 / 16) = e.1 by change 16 * (e.1 / 16) = e.1; omega]
  rfl

@[expose] def TreeInv (s : Nat) (S : List Nat) : Prop :=
  s = 0 ∨ ((∀ k, s.testBit (k + 64) = S.contains k) ∧ S.Nodup ∧ ∀ k ∈ S, k < 65536 ∧ KeyT k)

theorem treeStep_inv {s : Nat} {S : List Nat} (h : TreeInv s S) (e : Nat × Nat × Nat) :
    TreeInv (treeStep s e) (S ++ [e.1]) := by
  unfold treeStep
  simp only [letN_eq]
  unfold treeStepL TreeInv
  rcases h with rfl | ⟨hb, hnd, hS⟩
  · left
    have : Nat.beq (Nat.land 0 (Nat.shiftLeft 1 (Nat.add e.2.1 64))) 0 = true := by
      rw [land_pow_beq, Nat.zero_testBit]
      rfl
    simp only [this, Bool.not_true, Bool.and_false, Bool.false_and]
  · rcases hc : (Nat.blt e.1 65536 &&
      Nat.beq (Nat.land s (Nat.shiftLeft 1 (Nat.add e.1 64))) 0 &&
      !(Nat.beq (Nat.land s (Nat.shiftLeft 1 (Nat.add e.2.1 64))) 0) &&
      Nat.blt e.2.2 12 && Nat.beq (mulX e.2.1 e.2.2) e.1) with _ | _
    · left
      rfl
    · right
      simp only [Bool.and_eq_true, land_pow_beq, Bool.not_eq_true', Bool.not_not, Nat.blt_eq,
        Nat.beq_eq] at hc
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
      change s.testBit (e.1 + 64) = false at h2
      change s.testBit (e.2.1 + 64) = true at h3
      rw [hb] at h2 h3
      change (∀ k, (addKey s e.1).testBit (k + 64) = (S ++ [e.1]).contains k) ∧ _
      refine ⟨?_, ?_, ?_⟩
      · intro k
        rw [testBit_addKey, hb, List.contains_append, List.contains_cons, List.contains_nil,
          Bool.or_false]
      · rw [List.nodup_append]
        refine ⟨hnd, List.nodup_singleton _, ?_⟩
        intro a ha b hb'
        rw [List.mem_singleton] at hb'
        subst hb'
        intro hab
        subst hab
        have := List.contains_iff_mem.2 ha
        rw [h2] at this
        exact absurd this (by simp)
      · intro k hk
        rcases List.mem_append.1 hk with hk | hk
        · exact hS k hk
        · rw [List.mem_singleton] at hk
          subst hk
          refine ⟨h1, ?_⟩
          rw [← h5]
          exact keyT_mulX (hS _ (List.contains_iff_mem.1 h3)).2 h4

theorem treeK_inv : ∀ (E : List (Nat × Nat × Nat)) (s : Nat) (S : List Nat), TreeInv s S →
    TreeInv (treeK E s) (S ++ E.map Prod.fst)
  | [], s, S, h => by
    change TreeInv s (S ++ [])
    simpa using h
  | e :: E, s, S, h => by
    change TreeInv (letN (treeStep s e) (treeK E)) _
    rw [letN_eq]
    have := treeK_inv E (treeStep s e) (S ++ [e.1]) (treeStep_inv h e)
    simpa using this

theorem treeS_inv : ∀ (ES : List (List (Nat × Nat × Nat))) (s : Nat) (S : List Nat),
    TreeInv s S → TreeInv (treeS ES s) (S ++ ES.flatten.map Prod.fst)
  | [], s, S, h => by
    change TreeInv s (S ++ [])
    simpa using h
  | E :: ES, s, S, h => by
    change TreeInv (letN (treeK E s) (treeS ES)) _
    rw [letN_eq]
    have := treeS_inv ES (treeK E s) (S ++ E.map Prod.fst) (treeK_inv E s S h)
    simpa [List.flatten_cons, List.map_append, List.append_assoc] using this

theorem keyT_root : KeyT 33825 :=
  ⟨(idC, []), bfsT_root (N := 65536) (fun c hc => by rw [keyL_eq]; omega) idC_lt 65536, rfl⟩

theorem treeInv_root : TreeInv (Nat.shiftLeft 1 (Nat.add 33825 64)) [33825] := by
  right
  refine ⟨?_, List.nodup_singleton _, ?_⟩
  · intro k
    change (1 <<< (33825 + 64)).testBit (k + 64) = _
    have h : ∀ j, (1 <<< (j + 64)).testBit (k + 64) = [j].contains k := by
      intro j
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
      simp only [List.contains_cons, List.contains_nil, Bool.or_false]
      rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq, Nat.add_right_cancel_iff, eq_comm]
    exact h 33825
  · intro k hk
    rw [List.mem_singleton] at hk
    subst hk
    exact ⟨by norm_num, keyT_root⟩

theorem invChk_spec {G lo n : Nat} (h : invChk G lo n = true) {m : Nat} (hm1 : lo ≤ m)
    (hm2 : m < lo + n) (hinv : InvL m) : G.testBit m = true := by
  unfold invChk at h
  rw [CFSG.KS.Raw.Orb.allN_iff] at h
  have := h (m - lo) (by omega)
  rw [letN_eq, show Nat.add lo (m - lo) = m by change lo + (m - lo) = m; omega,
    (invB_iff m).2 hinv, land_pow_beq] at this
  revert this
  cases G.testBit m <;> simp

theorem reachL_of {G : Nat} {ES : List (List (Nat × Nat × Nat))}
    (hinv : ∀ k < 16, invChk G (Nat.mul 4096 k) 4096 = true)
    (htree : Nat.beq (Nat.shiftRight (treeS ES (Nat.shiftLeft 1 (Nat.add 33825 64))) 64) G = true) :
    ReachL (33825 :: ES.flatten.map Prod.fst) ∧ (33825 :: ES.flatten.map Prod.fst).Nodup ∧
      ∀ m ∈ (33825 :: ES.flatten.map Prod.fst), m < 65536 := by
  have hG : G.testBit 33825 = true := by
    refine invChk_spec (hinv 8 (by norm_num)) (by norm_num) (by norm_num) ?_
    have := invL_id
    exact this
  have ht := treeS_inv ES _ [33825] treeInv_root
  rw [List.singleton_append] at ht
  have htG := Nat.eq_of_beq_eq_true htree
  rcases ht with h0 | ⟨hb, hnd, hS⟩
  · rw [h0] at htG
    rw [← htG] at hG
    simp at hG
  · refine ⟨?_, hnd, fun m hm => (hS m hm).1⟩
    intro k hk
    rw [lBFS_twin.2.1 k hk]
    have hs : (look keyL k lTwin.all.reverse).isSome =
        !(look keyL k lTwin.all.reverse).isNone := by
      cases look keyL k lTwin.all.reverse <;> rfl
    rw [hs, look_isNone, Bool.not_not, List.any_reverse, Bool.eq_iff_iff, List.any_eq_true]
    constructor
    · rintro ⟨e, he, hek⟩
      have hek' : keyL e.1 = k := by simpa using hek
      have hinvk : InvL k := hek' ▸ (twin_inv he).2
      have hGk := invChk_spec (hinv (k / 4096) (by omega)) (by change 4096 * (k / 4096) ≤ k; omega)
        (by change k < 4096 * (k / 4096) + 4096; omega) hinvk
      rw [← htG] at hGk
      change ((treeS ES (Nat.shiftLeft 1 (Nat.add 33825 64))) >>> 64).testBit k = true at hGk
      rw [Nat.testBit_shiftRight, Nat.add_comm] at hGk
      rw [← hb k]
      exact hGk
    · intro hc
      obtain ⟨e, he, hek⟩ := (hS k (List.contains_iff_mem.1 hc)).2
      exact ⟨e, he, by simpa using hek⟩

end CFSG.KC.M24L2
