module

public import CFSG.Certificates.Kernel.Spor.PK.Perm.Make
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Comp
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Fintype.EquivFin

public section

namespace CFSG.KS.PK

open CFSG.KC.Enum CFSG.KS

theorem surj_of_inj {n : Nat} {f : Nat → Nat} (hf : ∀ i < n, f i < n)
    (hinj : ∀ i < n, ∀ j < n, f i = f j → i = j) : ∀ y < n, ∃ x < n, f x = y := by
  let F : Fin n → Fin n := fun x => ⟨f x.val, hf x.val x.isLt⟩
  have hF : Function.Injective F := fun a b e =>
    Fin.ext (hinj a.val a.isLt b.val b.isLt (congrArg Fin.val e))
  intro y hy
  obtain ⟨x, hx⟩ := Finite.surjective_of_injective hF ⟨y, hy⟩
  exact ⟨x.val, x.isLt, congrArg Fin.val hx⟩

private theorem inv_fd_or (w a b j : Nat) : fd w (a ||| b) j = fd w a j ||| fd w b j := by
  unfold fd
  rw [Nat.or_div_two_pow, Nat.or_mod_two_pow]

private theorem inv_fd_zero (w j : Nat) : fd w 0 j = 0 := by
  simp [fd]

private theorem inv_fd_mul_pow {w v i : Nat} (hv : v < 2 ^ w) (j : Nat) :
    fd w (v * 2 ^ (w * i)) j = if j = i then v else 0 := by
  have h := fd_add_mul (w := w) (x := 0) (v := v) (i := i) (j := j) hv (inv_fd_zero w i)
  rwa [Nat.zero_add, inv_fd_zero] at h

private theorem inv_pinvS_fold {n w p : Nat} {g : Nat → Nat} (hw : n ≤ 2 ^ w)
    (hp : ∀ i < n, fd w p i < n) (hg : ∀ j < n, g j < n ∧ fd w p (g j) = j)
    (hgp : ∀ i < n, g (fd w p i) = i) (L : List Nat) (hL : ∀ a ∈ L, a < n) :
    L.foldr (fun i s => s ||| i * 2 ^ (w * fd w p i)) 0 < 2 ^ (w * n) ∧
      ∀ j < n, fd w (L.foldr (fun i s => s ||| i * 2 ^ (w * fd w p i)) 0) j =
        if g j ∈ L then g j else 0 := by
  induction L with
  | nil =>
    exact ⟨by simpa using Nat.two_pow_pos (w * n), fun j _ => by simp [inv_fd_zero]⟩
  | cons a L ih =>
    have haL : a < n := hL a List.mem_cons_self
    obtain ⟨ih1, ih2⟩ := ih fun b hb => hL b (List.mem_cons_of_mem _ hb)
    have haw : a < 2 ^ w := lt_of_lt_of_le haL hw
    have hj0 : fd w p a < n := hp a haL
    have hb : a * 2 ^ (w * fd w p a) < 2 ^ (w * n) :=
      calc a * 2 ^ (w * fd w p a) < 2 ^ w * 2 ^ (w * fd w p a) :=
            Nat.mul_lt_mul_of_pos_right haw (Nat.two_pow_pos _)
        _ = 2 ^ (w * (fd w p a + 1)) := by rw [← Nat.pow_add, Nat.mul_succ, Nat.add_comm]
        _ ≤ 2 ^ (w * n) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left w hj0)
    simp only [List.foldr_cons]
    refine ⟨Nat.or_lt_two_pow ih1 hb, fun j hj => ?_⟩
    rw [inv_fd_or, ih2 j hj, inv_fd_mul_pow haw j]
    by_cases hjj : j = fd w p a
    · have hga : g j = a := by rw [hjj]; exact hgp a haL
      rw [if_pos hjj, hga]
      by_cases haL' : a ∈ L <;> simp [haL']
    · have hne : g j ≠ a := fun e => hjj (by rw [← e]; exact (hg j hj).2.symm)
      rw [if_neg hjj, Nat.or_zero]
      simp [hne]

theorem pinvS_eq {n w p : Nat} {g : Nat → Nat} (hw : n ≤ 2 ^ w) (hp : ∀ i < n, fd w p i < n)
    (hg : ∀ j < n, g j < n ∧ fd w p (g j) = j) (hgp : ∀ i < n, g (fd w p i) = i) :
    pinvS n w (mask w) p = enc w g n := by
  have hfold : pinvS n w (mask w) p =
      (List.range n).foldr (fun i s => s ||| i * 2 ^ (w * fd w p i)) 0 := by
    have hf : (fun i s => Nat.lor s (Nat.shiftLeft i (Nat.mul w (pg w (mask w) p i)))) =
        fun i s => s ||| i * 2 ^ (w * fd w p i) := by
      funext i s
      change s ||| (i <<< (w * pg w (mask w) p i)) = _
      rw [Nat.shiftLeft_eq, pg_eq]
      rfl
    unfold pinvS
    rw [foldN_eq, hf]
  obtain ⟨h1, h2⟩ := inv_pinvS_fold hw hp hg hgp (List.range n) fun a ha => List.mem_range.1 ha
  rw [hfold]
  refine (enc_fd h1).symm.trans (enc_congr fun j hj => ?_)
  rw [h2 j hj, if_pos (List.mem_range.2 (hg j hj).1)]

theorem permOK_iff {n w p q : Nat} :
    permOK n w (mask w) (n * w) p q = true ↔
      p < 2 ^ (w * n) ∧ q < 2 ^ (w * n) ∧ ∀ i < n, fd w p i < n ∧ fd w q (fd w p i) = i := by
  unfold permOK
  simp only [bAnd_eq, strictB_eq, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, allN_iff,
    shiftRight_eq_zero_iff, Nat.mul_comm n w, pg_eq]
  exact Iff.rfl

private theorem inv_itr_lt {n w : Nat} (hw : n ≤ 2 ^ w) (p k : Nat) {i : Nat} (hi : i < n) :
    itr (fd w p) k i < 2 ^ w := by
  cases k with
  | zero => exact lt_of_lt_of_le hi hw
  | succ k => exact fd_lt w p _

theorem ppow_eq {n w : Nat} (hn : n < 2 ^ 32) (hn24 : n ≤ 2 ^ 24) (hw : n ≤ 2 ^ w) (p k : Nat) :
    ppow n w (mask w) (pidn n w) p k = enc w (fun i => itr (fd w p) k i) n := by
  induction k with
  | zero => exact pidn_eq hn24 hw
  | succ k ih =>
    have hs : ppow n w (mask w) (pidn n w) p (k + 1) =
        pcomp n w (mask w) p (ppow n w (mask w) (pidn n w) p k) := by
      show strictN _ _ = _
      exact strictN_eq _ _
    rw [hs, ih, pcomp_eq hn]
    refine enc_congr fun i hi => ?_
    rw [fd_enc (fun j hj => inv_itr_lt hw p k hj) hi]
    rfl

end CFSG.KS.PK

end
