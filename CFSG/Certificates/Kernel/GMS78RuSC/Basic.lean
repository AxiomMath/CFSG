module

public import Certificates.Data.Kernel.GMS78RuSCent
import CFSG.Certificates.Kernel.GMS78RuP.Basic

public section

namespace CFSG.KC.GMS.SC

open CFSG.KLie.CT CFSG.KC.Loop

theorem fget_eq' (X i w : Nat) : fget X i w = X / 2 ^ (i * w) % 2 ^ w := by
  change (X >>> (i * w)) &&& (pw2 w - 1) = _
  rw [show pw2 w = 2 ^ w from Nat.one_shiftLeft w, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]

theorem fget_lt (X i w : Nat) : fget X i w < 2 ^ w := by
  rw [fget_eq']
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem neStrictB_eq (y : Nat) (k : Nat → Bool) : neStrictB y k = k y := by cases y <;> rfl

theorem neLen_eq {α : Type} : ∀ l : List α, neLen l = l.length
  | [] => rfl
  | _ :: l => by
    change strictN (neLen l) Nat.succ = _
    rw [P117.strictN_eq, neLen_eq l]
    rfl

theorem neGet_eq {α : Type} (d : α) : ∀ (l : List α) (k : Nat), neGet d l k = l.getD k d
  | [], k => by cases k <;> rfl
  | a :: l, 0 => rfl
  | a :: l, k + 1 => by
    change neGet d l k = _
    rw [neGet_eq d l k]
    rfl

theorem allN_iff (f : Nat → Bool) : ∀ n, allN n f = true ↔ ∀ i < n, f i = true
  | 0 => ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | n + 1 => by
    change andB (f n) (allN n f) = true ↔ _
    rw [P117.andB_iff, allN_iff f n]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact h2 i h
      · exact h ▸ h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem listRec_map {α : Type} (f : Nat → α) : ∀ C : List Nat,
    List.rec (motive := fun _ => List α) [] (fun q _ ih => List.cons (f q) ih) C = C.map f
  | [] => rfl
  | q :: C => by
    change List.cons (f q) _ = _
    rw [listRec_map f C]
    rfl

def pk (w : Nat) : List Nat → Nat
  | [] => 0
  | x :: l => x ||| (pk w l <<< w)

theorem pk_cons_add {w x : Nat} (l : List Nat) (hx : x < 2 ^ w) :
    pk w (x :: l) = x + 2 ^ w * pk w l := by
  change x ||| (pk w l <<< w) = _
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq, Nat.add_comm, Nat.mul_comm]

theorem czPack8_eq (l : List Nat) :
    czPack8 l = pk 8 l := by
  have key : ∀ (l : List Nat) (s : Nat),
      List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
        (fun x _ ih s => Nat.lor (Nat.shiftLeft x s) (ih (Nat.add s 8))) l s = pk 8 l <<< s := by
    intro l
    induction l with
    | nil => intro s; simp [pk]
    | cons x l ih =>
      intro s
      change Nat.lor (Nat.shiftLeft x s) (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
        (fun x _ ih s => Nat.lor (Nat.shiftLeft x s) (ih (Nat.add s 8))) l (s + 8)) = _
      rw [ih]
      change _ = (x ||| (pk 8 l <<< 8)) <<< s
      rw [Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add, Nat.add_comm 8 s, Nat.shiftLeft_add]
      rfl
  have := key l 0
  rw [Nat.shiftLeft_zero] at this
  exact this

theorem czPack9_eq (l : List Nat) :
    czPack9 l = pk 9 l := by
  have key : ∀ (l : List Nat) (s : Nat),
      List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
        (fun x _ ih s => Nat.lor (Nat.shiftLeft x s) (ih (Nat.add s 9))) l s = pk 9 l <<< s := by
    intro l
    induction l with
    | nil => intro s; simp [pk]
    | cons x l ih =>
      intro s
      change Nat.lor (Nat.shiftLeft x s) (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
        (fun x _ ih s => Nat.lor (Nat.shiftLeft x s) (ih (Nat.add s 9))) l (s + 9)) = _
      rw [ih]
      change _ = (x ||| (pk 9 l <<< 9)) <<< s
      rw [Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add, Nat.add_comm 9 s, Nat.shiftLeft_add]
      rfl
  have := key l 0
  rw [Nat.shiftLeft_zero] at this
  exact this

theorem pk_fget {w : Nat} : ∀ {l : List Nat}, (∀ x ∈ l, x < 2 ^ w) → ∀ j : Nat,
    fget (pk w l) j w = l.getD j 0
  | [], _, j => by simp [pk, fget_eq']
  | x :: l, hl, 0 => by
    have hx := hl x List.mem_cons_self
    rw [fget_eq', pk_cons_add l hx]
    simp only [Nat.zero_mul, Nat.pow_zero, Nat.div_one, List.getD_cons_zero]
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hx
  | x :: l, hl, j + 1 => by
    have hx := hl x List.mem_cons_self
    rw [List.getD_cons_succ, ← pk_fget (fun y hy => hl y (List.mem_cons_of_mem _ hy)) j,
      fget_eq', fget_eq', pk_cons_add l hx,
      show (j + 1) * w = w + j * w by rw [Nat.succ_mul, Nat.add_comm], Nat.pow_add, ← Nat.div_div_eq_div_mul]
    congr 2
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt hx, Nat.zero_add]

end CFSG.KC.GMS.SC

end
