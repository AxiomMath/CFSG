module

public import CFSG.Certificates.Kernel.A6CK.Bridge
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.A6CK

open CFSG.KS.Fi22LH

@[expose] def st3 (k e : Nat) : Nat := k * 3 + e

theorem st3_app (k e : Nat) : st3 k e = k * 3 + e := rfl

theorem foldl3_eq : ∀ (L : List Nat) (a : Nat),
    L.foldl st3 a = a * 3 ^ L.length + L.foldl st3 0
  | [], a => by simp
  | x :: L, a => by
    rw [List.foldl_cons, List.foldl_cons, foldl3_eq L (st3 a x), foldl3_eq L (st3 0 x),
      List.length_cons, Nat.pow_succ, st3_app, st3_app]
    ring

theorem foldl3_lt : ∀ (L : List Nat), (∀ e ∈ L, e < 3) → L.foldl st3 0 < 3 ^ L.length
  | [], _ => by simp
  | x :: L, h => by
    rw [List.foldl_cons, foldl3_eq, List.length_cons, Nat.pow_succ]
    have h1 := foldl3_lt L (fun e he => h e (List.mem_cons_of_mem _ he))
    have h2 := h x List.mem_cons_self
    rw [st3_app, Nat.zero_mul, Nat.zero_add]
    have h3 : x * 3 ^ L.length ≤ 2 * 3 ^ L.length := Nat.mul_le_mul_right _ (by omega)
    omega

theorem foldl3_inj : ∀ (L M : List Nat), L.length = M.length → (∀ e ∈ L, e < 3) →
    (∀ e ∈ M, e < 3) → L.foldl st3 0 = M.foldl st3 0 → L = M
  | [], [], _, _, _, _ => rfl
  | x :: L, y :: M, hl, hL, hM, h => by
    rw [List.length_cons, List.length_cons] at hl
    have hl' : L.length = M.length := by omega
    rw [List.foldl_cons, List.foldl_cons, foldl3_eq L (st3 0 x), foldl3_eq M (st3 0 y), hl'] at h
    simp only [st3_app, Nat.zero_mul, Nat.zero_add] at h
    have hL' := foldl3_lt L (fun e he => hL e (List.mem_cons_of_mem _ he))
    have hM' := foldl3_lt M (fun e he => hM e (List.mem_cons_of_mem _ he))
    rw [hl'] at hL'
    have hp : 0 < 3 ^ M.length := Nat.pow_pos (by decide)
    have e1 : x = y := by
      have d1 : (3 ^ M.length * x + L.foldl st3 0) / 3 ^ M.length =
          (3 ^ M.length * y + M.foldl st3 0) / 3 ^ M.length := by
        rw [Nat.mul_comm _ x, Nat.mul_comm _ y, h]
      rw [Nat.mul_add_div hp, Nat.mul_add_div hp, Nat.div_eq_of_lt hL',
        Nat.div_eq_of_lt hM'] at d1
      omega
    subst e1
    have e2 : L.foldl st3 0 = M.foldl st3 0 := by omega
    rw [foldl3_inj L M hl' (fun e he => hL e (List.mem_cons_of_mem _ he))
      (fun e he => hM e (List.mem_cons_of_mem _ he)) e2]
  | [], _ :: _, hl, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _ => by simp at hl

theorem decM_lt3 {x : Nat} (hx : validK x = true) : ∀ e ∈ (decM x).toList, e < 3 := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 he
  have hi' : i < 36 := by simpa [decM_size] using hi
  rw [Array.getElem_toList]
  simp only [decM_eq, Array.getElem_ofFn]
  exact (validK_ent hx).1 _ (by omega) _ (by omega)

theorem packM_eq (X : Array Nat) : Certificates.A6C.packM X = X.toList.foldl st3 0 := by
  unfold Certificates.A6C.packM
  rw [Array.foldl_toList]
  rfl

theorem packM_inj {x y : Nat} (hx : validK x = true) (hy : validK y = true)
    (h : Certificates.A6C.packM (decM x) = Certificates.A6C.packM (decM y)) : x = y := by
  apply decM_inj hx hy
  rw [← Array.toList_inj]
  rw [packM_eq, packM_eq] at h
  exact foldl3_inj _ _ (by simp [decM_size]) (decM_lt3 hx) (decM_lt3 hy) h

theorem negK_negK {x : Nat} (hx : validK x = true) : negK (negK x) = x := by
  obtain ⟨hxe, hxp⟩ := validK_ent hx
  generalize ent x = a at hxe hxp
  subst hxp
  rw [negK_pk hxe, negK_pk (fun r _ c _ => Nat.mod_lt _ (by decide))]
  apply congrArg encS
  unfold pk
  apply lanes_congr
  intro q hq
  unfold flat
  split
  · have h := hxe (q / 8) (by omega) (q % 8) (by omega)
    dsimp only
    generalize a (q / 8) (q % 8) = v at h ⊢
    revert v
    decide
  · rfl

theorem keyK_eq_min (x : Nat) : keyK x = min x (negK x) := by
  unfold keyK
  dsimp only
  by_cases hc : x < negK x
  · have h : Nat.blt x (negK x) = true := by rw [Nat.blt_eq]; exact hc
    rw [h]
    change x = _
    omega
  · have h : Nat.blt x (negK x) = false := by
      cases hb : Nat.blt x (negK x)
      · rfl
      · rw [Nat.blt_eq] at hb
        exact absurd hb hc
    rw [h]
    change negK x = _
    omega

theorem keyM_decM {x : Nat} (hx : validK x = true) : Certificates.A6C.keyM (decM x) =
    min (Certificates.A6C.packM (decM x)) (Certificates.A6C.packM (decM (negK x))) := by
  unfold Certificates.A6C.keyM
  rw [(decM_negK hx).2]

theorem keyK_of_keyM {x y : Nat} (hx : validK x = true) (hy : validK y = true)
    (h : Certificates.A6C.keyM (decM x) = Certificates.A6C.keyM (decM y)) : keyK x = keyK y := by
  have vx := (decM_negK hx).1
  have vy := (decM_negK hy).1
  rw [keyM_decM hx, keyM_decM hy] at h
  rw [keyK_eq_min, keyK_eq_min]
  have hc : Certificates.A6C.packM (decM x) = Certificates.A6C.packM (decM y) ∨
      Certificates.A6C.packM (decM x) = Certificates.A6C.packM (decM (negK y)) ∨
      Certificates.A6C.packM (decM (negK x)) = Certificates.A6C.packM (decM y) ∨
      Certificates.A6C.packM (decM (negK x)) = Certificates.A6C.packM (decM (negK y)) := by
    omega
  rcases hc with h1 | h1 | h1 | h1
  · rw [packM_inj hx hy h1]
  · rw [packM_inj hx vy h1, negK_negK hy, Nat.min_comm]
  · rw [← packM_inj vx hy h1, negK_negK hx, Nat.min_comm]
  · have e := congrArg negK (packM_inj vx vy h1)
    rw [negK_negK hx, negK_negK hy] at e
    rw [e]

theorem zip_tail_all : ∀ (a : Nat) (t : List Nat), (a :: t).Pairwise (· < ·) →
    ((a :: t).zip t).all (fun p => decide (p.1 < p.2)) = true
  | _, [], _ => rfl
  | a, b :: t, h => by
    rw [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨List.rel_of_pairwise_cons h List.mem_cons_self, zip_tail_all b t h.of_cons⟩

theorem nodupKeys_of {ks : List Nat} (h : ks.Nodup) : Certificates.A6C.nodupKeys ks = true := by
  unfold Certificates.A6C.nodupKeys
  have hs := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) ks
  have hn : (ks.mergeSort fun a b => decide (a ≤ b)).Nodup :=
    (List.mergeSort_perm ks _).nodup_iff.2 h
  have hlt : (ks.mergeSort fun a b => decide (a ≤ b)).Pairwise (· < ·) :=
    (hs.and hn).imp (fun {a b} hab => by
    obtain ⟨h1, h2⟩ := hab
    simp only [decide_eq_true_eq] at h1
    omega)
  generalize ks.mergeSort (fun a b => decide (a ≤ b)) = s at hlt
  cases s with
  | nil => rfl
  | cons a t => exact zip_tail_all a t hlt

theorem keysNodup_of {E : List Nat} (hv : ∀ x ∈ E, validK x = true) (h : (E.map keyK).Nodup) :
    Certificates.A6C.keysNodup (E.map decM).toArray = true := by
  unfold Certificates.A6C.keysNodup
  rw [List.toList_toArray, List.map_map]
  apply nodupKeys_of
  apply List.Nodup.map_on _ (List.Nodup.of_map _ h)
  intro x hx y hy hxy
  exact List.inj_on_of_nodup_map h hx hy (keyK_of_keyM (hv x hx) (hv y hy) hxy)

end CFSG.KC.A6CK
