module

public import Certificates.Data.Kernel.SmithD6.KcCheck
public import CFSG.Certificates.Kernel.KeyTreeChunksSound
public import Certificates.Data.SmithD6Model
import CFSG.Certificates.Kernel.SmithD6WtSound

public section

namespace CFSG.KD.SmithD6

open CFSG.SmithD6 CFSG.KC.KeyTree

@[expose] def selF (g : Nat → Bool) : List Nat → Nat
  | [] => 0
  | b :: bs => (bif g 0 then b else 0) ^^^ selF (fun m => g (m + 1)) bs

theorem selF_congr : ∀ (bs : List Nat) {g g' : Nat → Bool}, (∀ m < bs.length, g m = g' m) →
    selF g bs = selF g' bs
  | [], _, _, _ => rfl
  | b :: bs, g, g', h => by
    simp only [selF]
    rw [h 0 (by simp), selF_congr bs (g := fun m => g (m + 1)) (g' := fun m => g' (m + 1))
      fun m hm => h (m + 1) (by simp; omega)]

theorem foldl_range_selF : ∀ (bs : List Nat) (g : Nat → Bool) (a : Nat),
    (List.range bs.length).foldl (fun acc m => if g m then acc ^^^ bs.getD m 0 else acc) a =
      a ^^^ selF g bs
  | [], _, a => by simp [selF]
  | b :: bs, g, a => by
    rw [List.length_cons, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    have e := foldl_range_selF bs (fun m => g (m + 1))
      (if g 0 then a ^^^ (b :: bs).getD 0 0 else a)
    simp only [List.getD_cons_succ] at e ⊢
    rw [e]
    simp only [selF, List.getD_cons_zero]
    cases g 0 <;> simp [Nat.xor_assoc]

theorem arr_getElem!_eq_getD (bs : List Nat) (m : Nat) : (⟨bs⟩ : Array Nat)[m]! = bs.getD m 0 := by
  simp [List.getD_eq_getElem?_getD]

theorem xorComb_eq_selF {bs : List Nat} (hb : bs.length = 6) (d : Nat) :
    xorComb ⟨bs⟩ d = selF d.testBit bs := by
  unfold xorComb
  simp only [arr_getElem!_eq_getD]
  rw [← hb, foldl_range_selF, Nat.zero_xor]

theorem testBit_coefOf {ps : List Nat} (x : Nat) {m : Nat} (hm : m < 6) :
    (coefOf ⟨ps⟩ x).testBit m = x.testBit (ps.getD m 0) := by
  have key : ∀ n ≤ 6, ((List.range n).foldl
      (fun c k => if x.testBit (⟨ps⟩ : Array Nat)[k]! then c ||| 2 ^ k else c) 0).testBit m =
      (decide (m < n) && x.testBit (ps.getD m 0)) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        arr_getElem!_eq_getD]
      have h0 := ih (by omega)
      by_cases hx : x.testBit (ps.getD n 0) = true
      · rw [if_pos hx, Nat.testBit_or, h0, Nat.testBit_two_pow]
        rcases Nat.lt_trichotomy m n with h | rfl | h
        · simp [h, show m < n + 1 by omega, show n ≠ m by omega]
        · simpa [List.getD_eq_getElem?_getD] using hx
        · simp [show ¬ m < n by omega, show ¬ m < n + 1 by omega, show n ≠ m by omega]
      · rw [if_neg hx, h0]
        rcases Nat.lt_trichotomy m n with h | rfl | h
        · simp [h, show m < n + 1 by omega]
        · simpa [List.getD_eq_getElem?_getD] using hx
        · simp [show ¬ m < n by omega, show ¬ m < n + 1 by omega]
  unfold coefOf
  simpa [hm] using key 6 (Nat.le_refl 6)

theorem kcPick_eq : ∀ (x : Nat) (bs ps : List Nat), bs.length = ps.length →
    kcPick x bs ps = selF (fun m => x.testBit (ps.getD m 0)) bs
  | _, [], _, _ => rfl
  | _, _ :: _, [], h => absurd h (by simp)
  | x, b :: bs, p :: ps, h => by
    change Nat.xor (Nat.mul b (fld(x, p, 1))) (kcPick x bs ps) = _
    rw [kcPick_eq x bs ps (by simpa using h), fld_one_eq]
    simp only [selF, List.getD_cons_zero, List.getD_cons_succ]
    cases x.testBit p <;> simp

theorem memR_eq_kcMem {bs ps : List Nat} (hb : bs.length = 6) (hp : ps.length = 6) (x : Nat) :
    memR ⟨bs⟩ ⟨ps⟩ x = kcMem bs ps x := by
  have e : xorComb ⟨bs⟩ (coefOf ⟨ps⟩ x) = kcPick x bs ps := by
    rw [xorComb_eq_selF hb, kcPick_eq x bs ps (by omega)]
    exact selF_congr bs fun m hm => testBit_coefOf x (by omega)
  unfold memR kcMem
  rw [e]
  cases h : Nat.beq (kcPick x bs ps) x
  · have := Nat.ne_of_beq_eq_false h
    simpa using this
  · have := Nat.eq_of_beq_eq_true h
    simpa using this

theorem kcThrGo_eq : ∀ (Bs Ps : List (Array Nat)), Bs.length = Ps.length →
    kcThrGo Bs Ps = (List.zipWith kcThrA Bs Ps).sum
  | [], _, _ => rfl
  | _ :: _, [], h => absurd h (by simp)
  | B :: Bs, P :: Ps, h => by
    change Nat.add (kcThrA B P) (kcThrGo Bs Ps) = _
    rw [kcThrGo_eq Bs Ps (by simpa using h)]
    simp

theorem kcThrC_eq : ∀ (Bss Pss : List (List (Array Nat))), Bss.length = Pss.length →
    (∀ c < Bss.length, (Bss.getD c []).length = (Pss.getD c []).length) →
    kcThrC Bss Pss = (List.zipWith kcThrA Bss.flatten Pss.flatten).sum
  | [], _, _, _ => rfl
  | _ :: _, [], h, _ => absurd h (by simp)
  | Bs :: Bss, Ps :: Pss, h, hc => by
    change Nat.add (kcThrGo Bs Ps) (kcThrC Bss Pss) = _
    have h0 : Bs.length = Ps.length := by simpa using hc 0 (by simp)
    rw [kcThrGo_eq Bs Ps h0, kcThrC_eq Bss Pss (by simpa using h)
      fun c hc' => by simpa using hc (c + 1) (by simpa using hc'),
      List.flatten_cons, List.flatten_cons, List.zipWith_append h0, List.sum_append]
    rfl

theorem kcRk2Go_sound : ∀ (bs : List Nat) (a : Nat), kcRk2Go bs a = true →
    ∃ x ∈ bs, x &&& 63 ≠ 0 ∧ x &&& 63 ≠ a ∧
      (a ≠ 0 ∨ ∃ y ∈ bs, y &&& 63 ≠ 0 ∧ y &&& 63 ≠ x &&& 63)
  | [], _, h => absurd h (by simp [kcRk2Go])
  | b :: bs, a, h => by
    change bIf(Nat.beq (Nat.land b 63) 0, kcRk2Go bs a, bIf(Nat.beq a 0, kcRk2Go bs (Nat.land b 63),
      bIf(Nat.beq (Nat.land b 63) a, kcRk2Go bs a, true))) = true at h
    have hl : Nat.land b 63 = b &&& 63 := rfl
    cases h1 : Nat.beq (Nat.land b 63) 0
    · rw [h1] at h
      have hb0 : b &&& 63 ≠ 0 := by rw [← hl]; exact Nat.ne_of_beq_eq_false h1
      cases h2 : Nat.beq a 0
      · rw [h2] at h
        have ha0 : a ≠ 0 := Nat.ne_of_beq_eq_false h2
        cases h3 : Nat.beq (Nat.land b 63) a
        · exact ⟨b, List.mem_cons_self, hb0, by rw [← hl]; exact Nat.ne_of_beq_eq_false h3,
            Or.inl ha0⟩
        · rw [h3] at h
          obtain ⟨x, hx, h4, h5, h6⟩ := kcRk2Go_sound bs a h
          exact ⟨x, List.mem_cons_of_mem _ hx, h4, h5, Or.inl ha0⟩
      · rw [h2] at h
        have ha0 : a = 0 := Nat.eq_of_beq_eq_true h2
        obtain ⟨x, hx, h4, h5, -⟩ := kcRk2Go_sound bs _ h
        refine ⟨x, List.mem_cons_of_mem _ hx, h4, by rw [ha0]; exact h4, Or.inr ⟨b,
          List.mem_cons_self, hb0, ?_⟩⟩
        rw [← hl]
        exact fun e => h5 e.symm
    · rw [h1] at h
      obtain ⟨x, hx, h4, h5, h6⟩ := kcRk2Go_sound bs a h
      refine ⟨x, List.mem_cons_of_mem _ hx, h4, h5, ?_⟩
      rcases h6 with h6 | ⟨y, hy, h7, h8⟩
      · exact Or.inl h6
      · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, h7, h8⟩

theorem kcRk2A_sound {B : Array Nat} (h : kcRk2A B = true) :
    ∃ x ∈ B.toList, ∃ y ∈ B.toList, x &&& 63 ≠ 0 ∧ y &&& 63 ≠ 0 ∧ x &&& 63 ≠ y &&& 63 := by
  rcases B with ⟨bs⟩
  obtain ⟨x, hx, h1, -, h3⟩ := kcRk2Go_sound bs 0 h
  rcases h3 with h3 | ⟨y, hy, h4, h5⟩
  · exact absurd rfl h3
  · exact ⟨x, hx, y, hy, h1, h4, fun e => h5 e.symm⟩

theorem kcMeetGo_sound : ∀ (Bs : List (Array Nat)) (sk : Bool), kcMeetGo Bs sk = true →
    ∀ i < Bs.length, (sk = false ∨ i ≠ 0) → kcRk2A (Bs.getD i #[]) = true
  | [], _, _, i, hi, _ => absurd hi (by simp)
  | B :: Bs, sk, h, i, hi, hs => by
    change bAnd(bIf(sk, true, kcRk2A B), kcMeetGo Bs false) = true at h
    obtain ⟨h1, h2⟩ := band_true h
    rcases i with _ | i
    · rcases hs with rfl | hs
      · exact h1
      · exact absurd rfl hs
    · rw [List.getD_cons_succ]
      exact kcMeetGo_sound Bs false h2 i (by simpa using hi) (Or.inl rfl)

theorem kcSpanGo_sound {t : KT} : ∀ (ix : List Nat) (m : Nat), kcSpanGo t ix m = true →
    ∀ k < ix.length, t.find (2 ^ (m + k)) = ix.getD k 0 + 1
  | [], _, _, _, hk => absurd hk (by simp)
  | i :: ix, m, h, k, hk => by
    change bAnd(Nat.beq (KT.find (Nat.pow 2 m) t) (Nat.succ i), kcSpanGo t ix (Nat.succ m)) =
      true at h
    obtain ⟨h1, h2⟩ := band_true h
    rcases k with _ | k
    · rw [Nat.add_zero, List.getD_cons_zero]
      exact Nat.eq_of_beq_eq_true h1
    · rw [List.getD_cons_succ, show m + (k + 1) = Nat.succ m + k by omega]
      exact kcSpanGo_sound ix (Nat.succ m) h2 k (by simpa using hk)

end CFSG.KD.SmithD6

end
