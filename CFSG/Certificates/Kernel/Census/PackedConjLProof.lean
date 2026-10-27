module

public import Certificates.Data.Kernel.Census.PackedConjL
public import CFSG.Certificates.Kernel.Census.PackedLProof

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum

theorem packW_cons (W x : Nat) (l : List Nat) : packW W (x :: l) = x + 2 ^ W * packW W l := by
  have h : packW W (x :: l) = x + packW W l <<< W := rfl
  rw [h, Nat.shiftLeft_eq, Nat.mul_comm]

theorem getW_val (W P k : Nat) : getW W P k = P / 2 ^ (W * k) % 2 ^ W := by
  have h : getW W P k = (P >>> (W * k)) &&& (1 <<< W - 1) := rfl
  rw [h, Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem getW_packW (W : Nat) (l : List Nat) (h : ∀ x ∈ l, x < 2 ^ W) (k : Nat) :
    getW W (packW W l) k = l.getD k 0 := by
  induction l generalizing k with
  | nil =>
    rw [getW_val]
    simp [packW]
  | cons x l ih =>
    have hx := h x (List.mem_cons_self ..)
    have hl : ∀ y ∈ l, y < 2 ^ W := fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [getW_val, packW_cons]
    cases k with
    | zero =>
      simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, List.getD_cons_zero]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    | succ k =>
      rw [List.getD_cons_succ, ← ih hl k, getW_val, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (W * k)),
        ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (Nat.two_pow_pos W),
        Nat.div_eq_of_lt hx, Nat.zero_add]

theorem fitW_spec {W : Nat} {l : List Nat} (h : fitW W l = true) : ∀ x ∈ l, x < 2 ^ W := by
  intro x hx
  have := List.all_eq_true.1 h x hx
  rw [Nat.blt_eq] at this
  have e : Nat.shiftLeft 1 W = 2 ^ W := Nat.one_shiftLeft W
  rw [e] at this
  exact this

theorem getW_eq {W : Nat} {a : Array Nat} (h : fitW W a.toList = true) (k : Nat) :
    getW W (packW W a.toList) k = a[k]! := by
  rw [getW_packW W _ (fitW_spec h), getElem!_eq_toList_getDL]
  rfl

section Checks

variable {n w : Nat}

theorem prootL_eq {nodes : Array NodeP} {cN : Array ArrCertP}
    (hc : ∀ j < nodes.size, cN[j]! = pmaskCert n w nodes[j]!.basis) {cs ci : Array Nat}
    {C I : Nat → Nat} (hC : ∀ k, C k = cs[k]!) (hI : ∀ k, I k = ci[k]!) (u : Nat)
    (r : Nat × Nat) :
    prootL n w nodes.toList nodes.size C I cs.size (pid n w) u r =
      prootOKC n w (nodes.map NodeP.basis) cN cs ci u r := by
  unfold prootOKC prootL
  rw [Array.size_map, hC, hI]
  by_cases h1 : r.1 < nodes.size
  · have hb : Nat.blt r.1 nodes.size = true := by rw [Nat.blt_eq]; exact h1
    have hm : (nodes.map NodeP.basis)[r.1]! = nodes[r.1]!.basis := by
      rw [getElem!_pos _ r.1 (by simpa using h1), getElem!_pos nodes r.1 h1, Array.getElem_map]
    rw [hb, hm, hc r.1 h1, pmem_pmaskCert, ← getElem!_eq_toList_getDL]
    generalize nodes[r.1]! = nd
    cases nd with
    | mk b wt ch =>
      simp only [strictB_eqL, Bool.true_and]
      rw [range_all_getElem! b _ (fun x => Nat.beq x (pconjT n w cs[r.2]! ci[r.2]! u) ||
        Nat.beq x (pid n w)) (fun _ _ => rfl)]
      simp only [Bool.and_assoc]
  · have hb : Nat.blt r.1 nodes.size = false := by
      rw [Bool.eq_false_iff, Ne, Nat.blt_eq]
      exact h1
    simp only [hb, Bool.false_and]

theorem prootsL_eq {W : Nat} {nodes : Array NodeP} {cN : Array ArrCertP}
    (hc : ∀ j < nodes.size, cN[j]! = pmaskCert n w nodes[j]!.basis) {cs ci : Array Nat}
    (hcs : fitW W cs.toList = true) (hci : fitW W ci.toList = true)
    (l : List (Nat × (Nat × Nat))) :
    prootsL n w W nodes cs ci l =
      l.all fun ur => prootOKC n w (nodes.map NodeP.basis) cN cs ci ur.1 ur.2 := by
  unfold prootsL
  simp only [strictB_eqL]
  congr 1
  funext ur
  exact prootL_eq hc (getW_eq hcs) (getW_eq hci) ur.1 ur.2

end Checks

end CFSG.KC.Census
