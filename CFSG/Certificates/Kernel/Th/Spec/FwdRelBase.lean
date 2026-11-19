
module

public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Certificates.Kernel.Th.S.OutS
public import CFSG.Certificates.Kernel.Th.Spec.Big
public import CFSG.Certificates.Kernel.Th.Spec.DceHsw
public import CFSG.Sporadic.Bridge.Common
public import CFSG.Sporadic.Th.ChainBase
import CFSG.Certificates.Kernel.Th.Max3S.WordsBase
public import CFSG.Certificates.Kernel.Th.S.TcS
public import CFSG.Certificates.Kernel.Th.Spec.DceLce
public import CFSG.Sporadic.Th.BaseBase
public import CFSG.Sporadic.Th.IndexBase

@[expose] public section

namespace CFSG.KC.Th.Spec.FwdRel

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.Sporadic.Bridge CFSG.Sporadic.Th

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  {J : Subgroup (GL (Fin 248) (ZMod 2))}

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem mat_injective : Function.Injective fun g : J => 𝕄 g :=
  fun _ _ h => Subtype.ext (Units.ext h)

theorem byte_wdN : ∀ (r : List (ℕ × Bool)), (∀ l ∈ r, l.1 < 8) →
    ∀ (i : ℕ) (hi : i < r.length), Dce.wdN r / 256 ^ i % 256 = Dce.cdL (r[i]'hi)
  | [], _, i, hi => absurd hi (Nat.not_lt_zero _)
  | l :: w, hl, i, hi => by
    have hc : Dce.cdL l < 256 := by
      have := hl l (by simp)
      unfold Dce.cdL
      split_ifs <;> omega
    cases i with
    | zero =>
      show (Dce.cdL l + 256 * Dce.wdN w) / 256 ^ 0 % 256 = Dce.cdL l
      omega
    | succ j =>
      have ih := byte_wdN w (fun m hm => hl m (by simp [hm])) j (by simpa using hi)
      show (Dce.cdL l + 256 * Dce.wdN w) / 256 ^ (j + 1) % 256 = Dce.cdL (w[j]'(by simpa using hi))
      rw [pow_succ', ← Nat.div_div_eq_div_mul,
        show (Dce.cdL l + 256 * Dce.wdN w) / 256 = Dce.wdN w by omega]
      exact ih

theorem enT_decode (r : List (ℕ × Bool)) (hl : ∀ l ∈ r, l.1 < 8) (hlen : r.length < 1024) :
    bitsN (Dce.enT r) 2 10 = r.length ∧ ∀ (i : ℕ) (hi : i < r.length),
      Nat.land (Nat.shiftRight (Nat.shiftRight (Dce.enT r) 12) (Nat.mul 8 i)) 255 =
        2 * (r[i]'hi).1 + (if (r[i]'hi).2 then 0 else 1) := by
  have e : Dce.enT r = 4 * r.length + 4096 * Dce.wdN r := rfl
  constructor
  · rw [bitsN_eq, e, Nat.shiftRight_eq_div_pow]
    omega
  · intro i hi
    have h2 : Nat.shiftRight (Dce.enT r) 12 = Dce.wdN r := by
      rw [e]
      show (4 * r.length + 4096 * Dce.wdN r) >>> 12 = _
      rw [Nat.shiftRight_eq_div_pow]
      norm_num
      omega
    have h1 : Nat.shiftRight (Nat.shiftRight (Dce.enT r) 12) (Nat.mul 8 i) =
        Dce.wdN r / 256 ^ i := by
      rw [h2]
      show Dce.wdN r >>> (8 * i) = _
      rw [Nat.shiftRight_eq_div_pow, pow_mul]
      norm_num
    rw [h1]
    show Dce.wdN r / 256 ^ i &&& 255 = _
    rw [show (255 : ℕ) = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    have h3 := byte_wdN r hl i hi
    unfold Dce.cdL at h3
    simpa using h3

def codeLetter (x : ℕ) : ℕ × Bool := (x / 2, decide (x % 2 = 0))

noncomputable def codeWord (w n : ℕ) : List (ℕ × Bool) :=
  (List.range n).map fun i => codeLetter (bitsN w (4 * i) 4)

theorem codeWord_lt (w n : ℕ) : ∀ l ∈ codeWord w n, l.1 < 8 := by
  intro l hl
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hl
  show bitsN w (4 * i) 4 / 2 < 8
  rw [bitsN_eq]
  have : (w >>> (4 * i)) % 2 ^ 4 < 16 := Nat.mod_lt _ (by norm_num)
  omega

section Letters


end Letters

def digitOf (l : ℤ) : ℕ := if l = 1 ∨ l = -1 then 0 else if l = 2 then 1 else 2

section Words

variable (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
include hk

end Words

end CFSG.KC.Th.Spec.FwdRel

end
