
module

public import Certificates.Data.Kernel.SporSch.J4SSylow
public import CFSG.Certificates.Kernel.SporSch.J4SColsSound
public import CFSG.Sporadic.Schreier.J4SSylowData
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.SporSch.C11

open CFSG.KC.Enum CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2
open scoped Matrix

theorem distinctK_sound {E SO SOI : Nat → Nat} {n : Nat} (h : distinctK E SO SOI n = true) :
    ∀ e < n, ∀ e' < e, unpack11 (E e') ≠ unpack11 (E e) := by
  unfold distinctK at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hc, hs, ho⟩ := h
  have hcan : ∀ e < n, canonK (E e) = true := fun e he => CFSG.KS.allN_spec hc e he
  have hSO : ∀ i < n, SO i < n ∧ SOI (SO i) = i := by
    intro i hi
    have := CFSG.KS.allN_spec hs i hi
    simp only [CFSG.KS.Raw.Orb.strictB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
    exact this
  have hmono : ∀ i < n, i + 1 < n → E (SO i) < E (SO (i + 1)) := by
    intro i hi hi1
    have := CFSG.KS.allN_spec ho i hi
    simp only [CFSG.KS.Raw.Orb.bIf_eq, Nat.succ_eq_add_one, hi1, ↓reduceIte, Nat.blt_eq] at this
    exact this
  have hlt : ∀ i j, i < j → j < n → E (SO i) < E (SO j) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · exact lt_trans (ih h (by omega)) (hmono j (by omega) hj)
      · subst h
        exact hmono i (by omega) hj
  have hsurj : ∀ e < n, ∃ i < n, SO i = e := by
    intro e he
    let f : Fin n → Fin n := fun i => ⟨SO i, (hSO i i.2).1⟩
    have hf : Function.Injective f := by
      intro a b hab
      have : SO a = SO b := congrArg Fin.val hab
      apply Fin.ext
      rw [← (hSO a a.2).2, ← (hSO b b.2).2, this]
    obtain ⟨i, hi⟩ := Finite.surjective_of_injective hf ⟨e, he⟩
    exact ⟨i, i.2, congrArg Fin.val hi⟩
  intro e he e' he' heq
  obtain ⟨i, hi, rfl⟩ := hsurj e he
  obtain ⟨i', hi', rfl⟩ := hsurj e' (by omega)
  have hne : E (SO i') ≠ E (SO i) := by
    rcases Nat.lt_trichotomy i' i with h | h | h
    · exact (hlt i' i h hi).ne
    · subst h
      omega
    · exact (hlt i i' h hi').ne'
  have hb : Nat.beq (E (SO i')) (E (SO i)) = false := by
    rw [Bool.eq_false_iff]
    exact fun hb => hne (Nat.eq_of_beq_eq_true hb)
  exact ne_sound (by rw [hcan _ (hSO i' hi').1, hcan _ (hSO i hi).1, hb]; rfl) heq

private theorem bit_and_one (x j : Nat) :
    Nat.land (Nat.shiftRight x j) 1 = if x.testBit j then 1 else 0 := by
  have e : Nat.land (Nat.shiftRight x j) 1 = x / 2 ^ j % 2 := by
    change (x >>> j) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [e, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ j) with h | h <;> simp [h]

private theorem par_rec (x : Nat) : ∀ n,
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc => strictN acc (fun s => Nat.xor s (Nat.land (Nat.shiftRight x j) (nat_lit 1))))
      n = (List.range n).foldl (fun s j => s ^^^ (if x.testBit j then 1 else 0)) 0
  | 0 => rfl
  | n + 1 => by
    change strictN _ _ = _
    rw [CFSG.KS.Raw.Orb.strictN_eq, par_rec x n, List.range_succ, List.foldl_append,
      List.foldl_cons, List.foldl_nil, bit_and_one]
    rfl

private theorem par11_eq (x : Nat) :
    par11 x = (List.range 11).foldl (fun s j => s ^^^ (if x.testBit j then 1 else 0)) 0 :=
  par_rec x 11

private theorem par_spec (x : Nat) : ∀ n,
    (List.range n).foldl (fun s j => s ^^^ (if x.testBit j then 1 else 0)) 0 < 2 ∧
    (((List.range n).foldl (fun s j => s ^^^ (if x.testBit j then 1 else 0)) 0 : ℕ) : ZMod 2) =
      ∑ j ∈ Finset.range n, (if x.testBit j then 1 else 0 : ZMod 2)
  | 0 => ⟨by simp, by simp⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := par_spec x n
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ, ← h2]
    generalize (List.range n).foldl (fun s j => s ^^^ (if x.testBit j then 1 else 0)) 0 = a at h1 ⊢
    rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;> cases x.testBit n <;> decide

private theorem ellK_eq (a : Nat) : ellK a = ell a := by
  unfold ellK ell
  exact par11_eq _

theorem ellK_sound {a b : Nat} (h : Nat.beq (ellK a) (ellK b) = true) : ell a = ell b := by
  rw [← ellK_eq, ← ellK_eq]
  exact Nat.eq_of_beq_eq_true h

private theorem toVecD_and (x y : Nat) (i : Fin 11) :
    toVecD 11 x i * toVecD 11 y i = toVecD 11 (Nat.land x y) i := by
  simp only [toVecD_apply]
  change _ = if (x &&& y).testBit i.val then 1 else 0
  rw [Nat.testBit_and]
  cases x.testBit i.val <;> cases y.testBit i.val <;> simp

theorem vecK_sound {v P : Nat} (hv : v < 2048) (h : vecK v P = true) :
    toVecD 11 v ᵥ* colsMatrix (unpack11 P) = toVecD 11 v := by
  funext j
  have hj : Nat.beq (par11 (Nat.land v (colK P j))) (Nat.land (Nat.shiftRight v j) 1) = true :=
    CFSG.KS.allN_spec h j.val j.isLt
  have e := Nat.eq_of_beq_eq_true hj
  rw [par11_eq, bit_and_one] at e
  have hcol : (unpack11 P)[j.val]?.getD 0 = colK P j := by
    simp [unpack11, unpackW, j.isLt]
    rfl
  have hsum : (toVecD 11 v ᵥ* colsMatrix (unpack11 P)) j =
      ∑ i ∈ Finset.range 11, (if (Nat.land v (colK P j)).testBit i then 1 else 0 : ZMod 2) := by
    simp only [Matrix.vecMul, dotProduct, colsMatrix_apply, hcol, toVecD_and]
    rw [← Fin.sum_univ_eq_sum_range (fun i => (if (Nat.land v (colK P j)).testBit i then 1 else 0 :
      ZMod 2))]
    rfl
  rw [hsum, ← (par_spec (Nat.land v (colK P j)) 11).2, e, toVecD_apply]
  cases v.testBit j.val <;> simp

private theorem testBit_foldr_or (g : Nat → Nat) (k : Nat) : ∀ (l : List Nat),
    (l.foldr (fun c s => s ||| (1 <<< g c)) 0).testBit k = true ↔ ∃ c ∈ l, g c = k
  | [] => by simp
  | c :: l => by
    rw [List.foldr_cons, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
      testBit_foldr_or g k l, decide_eq_true_iff]
    simp only [List.mem_cons, exists_eq_or_imp]
    exact or_comm

private theorem full_cover (g : Nat → Nat) {N : Nat}
    (h : (List.range N).foldr (fun c s => s ||| (1 <<< g c)) 0 = (1 <<< N) - 1) :
    ∀ k < N, ∃ c < N, g c = k := by
  intro k hk
  have hb : ((List.range N).foldr (fun c s => s ||| (1 <<< g c)) 0).testBit k = true := by
    rw [h, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
    simpa using hk
  obtain ⟨c, hc, e⟩ := (testBit_foldr_or g k _).1 hb
  exact ⟨c, List.mem_range.1 hc, e⟩

theorem injK_sound {P : Nat} (h : injK P = true) :
    ∀ c < 2048, ∀ c' < c, app11 (unpack11 P) c' ≠ app11 (unpack11 P) c := by
  unfold injK at h
  have e := Nat.eq_of_beq_eq_true h
  rw [CFSG.KS.Raw.Orb.foldN_eq] at e
  have hsurj : ∀ k < 2048, ∃ c < 2048, appK P c = k := full_cover (appK P) (N := 2048) e
  have hinj : Set.InjOn (appK P) (Finset.range 2048 : Set ℕ) := by
    apply Finset.injOn_of_card_image_eq
    refine le_antisymm Finset.card_image_le ?_
    have hsub : Finset.range 2048 ⊆ (Finset.range 2048).image (appK P) := by
      intro k hk
      obtain ⟨c, hc, e⟩ := hsurj k (Finset.mem_range.1 hk)
      exact Finset.mem_image.2 ⟨c, Finset.mem_range.2 hc, e⟩
    exact Finset.card_le_card hsub
  intro c hc c' hc' e
  rw [app_eq, app_eq] at e
  have := hinj (by simp; omega) (by simp; omega) e
  omega

end CFSG.KS.SporSch.C11

end
