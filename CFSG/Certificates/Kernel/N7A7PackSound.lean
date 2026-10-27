module

public import Certificates.Data.Kernel.N7A7Pack
public import CFSG.CGT.T75M23.A7Gens

public section

namespace CFSG.KernelN7

open Equiv CFSG.CGT.T75JM CFSG.CGT.T75M23

@[expose] def packP (σ : Perm (Fin 7)) : Nat :=
  (σ 0).val + 8 * (σ 1).val + 64 * (σ 2).val + 512 * (σ 3).val + 4096 * (σ 4).val +
    32768 * (σ 5).val + 262144 * (σ 6).val

@[expose] def keyN (l : List Nat) : Nat :=
  l.getD 0 0 + 8 * l.getD 1 0 + 64 * l.getD 2 0 + 512 * l.getD 3 0 + 4096 * l.getD 4 0 +
    32768 * l.getD 5 0 + 262144 * l.getD 6 0

theorem dig_packP (σ : Perm (Fin 7)) (j : Fin 7) : dig (packP σ) j.val = (σ j).val := by
  have h0 := (σ 0).isLt
  have h1 := (σ 1).isLt
  have h2 := (σ 2).isLt
  have h3 := (σ 3).isLt
  have h4 := (σ 4).isLt
  have h5 := (σ 5).isLt
  have h6 := (σ 6).isLt
  fin_cases j <;> simp only [dig, packP, Fin.isValue, Fin.mk_zero, Fin.reduceFinMk] <;> norm_num <;>
    omega

theorem packP_mul (σ τ : Perm (Fin 7)) : packP (σ * τ) = compP (packP σ) (packP τ) := by
  have e : ∀ i : Fin 7, dig (packP σ) (dig (packP τ) i.val) = ((σ * τ) i).val := fun i => by
    rw [dig_packP τ i, dig_packP σ (τ i), Perm.mul_apply]
  have e0 : dig (packP σ) (dig (packP τ) 0) = ((σ * τ) 0).val := e 0
  have e1 : dig (packP σ) (dig (packP τ) 1) = ((σ * τ) 1).val := e 1
  have e2 : dig (packP σ) (dig (packP τ) 2) = ((σ * τ) 2).val := e 2
  have e3 : dig (packP σ) (dig (packP τ) 3) = ((σ * τ) 3).val := e 3
  have e4 : dig (packP σ) (dig (packP τ) 4) = ((σ * τ) 4).val := e 4
  have e5 : dig (packP σ) (dig (packP τ) 5) = ((σ * τ) 5).val := e 5
  have e6 : dig (packP σ) (dig (packP τ) 6) = ((σ * τ) 6).val := e 6
  unfold compP
  rw [e0, e1, e2, e3, e4, e5, e6]
  rfl

theorem packP_one : packP 1 = idP := rfl

theorem packP_evalG (g h : Perm (Fin 7)) :
    ∀ w : List Nat, packP (evalG g h w) = wordP (packP g) (packP h) w
  | [] => packP_one
  | l :: w => by
    simp only [evalG, wordP]
    rw [packP_mul, packP_evalG g h w]
    split <;> rfl

theorem packP_eq_keyN (σ : Perm (Fin 7)) : packP σ = keyN (permKey7 σ) := rfl

theorem nodup_of_noDupB : ∀ (L : List Nat) (m : Nat), noDupB L m = true →
    (∀ x ∈ L, m.testBit x = false) ∧ L.Nodup
  | [], _, _ => ⟨fun _ h => absurd h (List.not_mem_nil), List.nodup_nil⟩
  | x :: xs, m, h => by
    simp only [noDupB, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hx, hrest⟩ := h
    obtain ⟨hxs, hnd⟩ := nodup_of_noDupB xs _ hrest
    have hbit : ∀ y ∈ xs, m.testBit y = false ∧ y ≠ x := by
      intro y hy
      have := hxs y hy
      rw [Nat.testBit_or, Bool.or_eq_false_iff, Nat.testBit_two_pow] at this
      exact ⟨this.1, fun e => by simp [e] at this⟩
    refine ⟨?_, List.nodup_cons.2 ⟨fun hm => (hbit x hm).2 rfl, hnd⟩⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hx
    · exact (hbit y hy).1

theorem a7Nodup_of_noDupB {X Y : Nat} (hX : packP a7x = X) (hY : packP a7y = Y)
    (h : noDupB (a7Words.map (wordP X Y)) 0 = true) : A7Nodup := by
  have e : a7Words.map (wordP X Y) =
      (a7Words.map fun w => permKey7 (evalG a7x a7y w)).map keyN := by
    rw [List.map_map]
    refine List.map_congr_left fun w _ => ?_
    simp only [Function.comp_apply, ← packP_eq_keyN, packP_evalG, hX, hY]
  have hnd := (nodup_of_noDupB _ 0 h).2
  rw [e] at hnd
  exact hnd.of_map keyN

end CFSG.KernelN7
