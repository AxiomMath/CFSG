module

public import CFSG.GH74.Generic.AltCerts

public section

namespace CFSG.GH74.Generic.BProg.B3.S3SL2AltV

open Equiv Equiv.Perm CFSG.SectionRank CFSG.GH74.Generic

variable {n : ℕ}

@[expose] noncomputable def vEmb (hn : 8 ≤ n) (i : Fin 4) : alternatingGroup (Fin n) :=
  altEmbed hn (v8Alt i)

theorem vEmb_sq (hn : 8 ≤ n) (i : Fin 4) : vEmb hn i * vEmb hn i = 1 := by
  rw [vEmb, ← map_mul]
  have : v8Alt i * v8Alt i = 1 := Subtype.ext (by have := v8_sq i; rw [pow_two] at this; exact this)
  rw [this, map_one]

theorem vEmb_comm (hn : 8 ≤ n) (i j : Fin 4) : vEmb hn i * vEmb hn j = vEmb hn j * vEmb hn i := by
  rw [vEmb, vEmb, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (v8_comm i j)

theorem vEmb_ker (hn : 8 ≤ n) :
    ∀ a : Fin 4 → Fin 2, a ≠ 0 → (List.ofFn fun i => vEmb hn i ^ (a i : ℕ)).prod ≠ 1 := by
  intro a ha h
  have h1 : (List.ofFn fun i => vEmb hn i ^ (a i : ℕ)).prod =
      altEmbed hn (List.ofFn fun i => v8Alt i ^ (a i : ℕ)).prod := by
    rw [map_list_prod, List.map_ofFn]
    refine congrArg (fun f => (List.ofFn f).prod) (funext fun i => ?_)
    simp [vEmb]
  rw [h1] at h
  have h2 : (List.ofFn fun i => v8Alt i ^ (a i : ℕ)).prod = 1 :=
    altEmbed_injective hn (by rw [h, map_one])
  refine v8_ker a ha ?_
  have := congrArg (alternatingGroup (Fin 8)).subtype h2
  rw [map_list_prod, List.map_ofFn] at this
  simpa [Function.comp_def, v8Alt] using this

theorem mul_swap_of_fix {g : Perm (Fin n)} {a b : Fin n} (ha : g a = a) (hb : g b = b) :
    g * swap a b = swap a b * g := by
  rw [Equiv.mul_swap_eq_swap_mul, ha, hb]

theorem vEmb_apply_of_le (hn : 8 ≤ n) (i : Fin 4) {a : Fin n} (ha : 8 ≤ a.val) :
    ((vEmb hn i : alternatingGroup (Fin n)) : Perm (Fin n)) a = a := by
  change (Equiv.Perm.extendDomain _ _) a = a
  exact Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simpa using ha)

theorem swap_mul_vEmb (hn : 8 ≤ n) (i : Fin 4) {a b : Fin n} (ha : 8 ≤ a.val) (hb : 8 ≤ b.val) :
    swap a b * ((vEmb hn i : alternatingGroup (Fin n)) : Perm (Fin n)) =
      ((vEmb hn i : alternatingGroup (Fin n)) : Perm (Fin n)) * swap a b :=
  (mul_swap_of_fix (vEmb_apply_of_le hn i ha) (vEmb_apply_of_le hn i hb)).symm

end CFSG.GH74.Generic.BProg.B3.S3SL2AltV
