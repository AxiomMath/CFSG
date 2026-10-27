module

public import Certificates.Data.Kernel.SporSch.HNXPtL
public import CFSG.Certificates.Kernel.SporSch.HNXPtSound

public section

set_option maxRecDepth 100000

namespace CFSG.KS.SporSch.HNXP

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KS.SporSch CFSG.KS.Ord Matrix

theorem packF_succ (f : Nat → Nat) (lo c : Nat) :
    packF f lo (c + 1) = packF f lo c ||| (f (lo + c) <<< (21 * c)) := rfl

theorem packF_get (f : Nat → Nat) (lo : Nat) : ∀ c, (∀ k < c, f (lo + k) < 2 ^ 21) →
    packF f lo c < 2 ^ (21 * c) ∧ ∀ j < c, packF f lo c / 2 ^ (21 * j) % 2 ^ 21 = f (lo + j)
  | 0, _ => ⟨by change 0 < 2 ^ 0; norm_num, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | c + 1, h => by
    obtain ⟨h1, h2⟩ := packF_get f lo c fun k hk => h k (by omega)
    have hx := h c (by omega)
    have e : packF f lo (c + 1) = 2 ^ (21 * c) * f (lo + c) + packF f lo c := by
      rw [packF_succ, Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt h1, Nat.shiftLeft_eq,
        Nat.mul_comm (f (lo + c))]
    rw [e]
    refine ⟨?_, fun j hj => ?_⟩
    · calc 2 ^ (21 * c) * f (lo + c) + packF f lo c < 2 ^ (21 * c) * f (lo + c) + 2 ^ (21 * c) :=
            by omega
        _ = 2 ^ (21 * c) * (f (lo + c) + 1) := by ring
        _ ≤ 2 ^ (21 * c) * 2 ^ 21 := Nat.mul_le_mul_left _ hx
        _ = 2 ^ (21 * (c + 1)) := by rw [← Nat.pow_add]; ring_nf
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · have e2 : 2 ^ (21 * c) = 2 ^ (21 * j) * (2 ^ 21 * 2 ^ (21 * (c - j - 1))) := by
          rw [← Nat.pow_add, ← Nat.pow_add]
          congr 1
          omega
        rw [e2, Nat.mul_assoc, Nat.add_comm, Nat.add_mul_div_left _ _ (by positivity),
          Nat.mul_assoc, Nat.add_mul_mod_self_left, h2 j hj]
      · rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt h1,
          Nat.zero_add, Nat.mod_eq_of_lt hx]

theorem fldW_packF {f : Nat → Nat} {lo c : Nat} (h : ∀ k < c, f (lo + k) < 2 ^ 21) {j : Nat}
    (hj : j < c) : fldW (packF f lo c) (21 * j) 21 = f (lo + j) := by
  rw [fldW_eq, (packF_get f lo c h).2 j hj]

theorem bCnt_eq (n b : Nat) : bCnt n b = if 64 * (b + 1) ≤ n then 64 else n - 64 * b := by
  change Bool.rec (motive := fun _ => Nat) (n - 64 * b) 64 (Nat.ble (64 * (b + 1)) n) = _
  cases h : Nat.ble (64 * (b + 1)) n
  · rw [if_neg (fun hc => absurd (Nat.ble_eq.mpr hc) (by rw [h]; decide))]
  · rw [if_pos (Nat.ble_eq.mp h)]

theorem ptsFn_sound {T : Nat → Nat} {MS CM3 M W : Nat} {f g : Nat → Nat} {n : Nat}
    (hc : constsOK CM3 M = true) (hm : masksOK MS = true) (hv : Canon 5 133 13 W)
    (h : ptsFn T MS CM3 M (trM W) f g n = true) (hf : ∀ k < n, f k < 2 ^ 21 ∧ g k < 2 ^ 21) :
    ∀ k < n, xvec T (g k) = ordMat 5 133 13 1729 W *ᵥ xvec T (f k) := by
  intro k hk
  have hb : k / 64 < (n + 63) / 64 := by omega
  have h1 := CFSG.KS.allN_spec h (k / 64) hb
  beta_reduce at h1
  have hcnt : k % 64 < bCnt n (k / 64) ∧ bCnt n (k / 64) ≤ 64 := by
    rw [bCnt_eq]
    split <;> omega
  have hlo : ∀ i < bCnt n (k / 64), 64 * (k / 64) + i < n := by
    intro i hi
    rw [bCnt_eq] at hi
    split at hi <;> omega
  have e : xvec T (fldW (packF g (64 * (k / 64)) (bCnt n (k / 64))) (21 * (k % 64)) 21) =
      ordMat 5 133 13 1729 W *ᵥ
        xvec T (fldW (packF f (64 * (k / 64)) (bCnt n (k / 64))) (21 * (k % 64)) 21) :=
    ptsImg_sound hc hm hv hcnt.2 h1 (k % 64) hcnt.1
  have ek : 64 * (k / 64) + k % 64 = k := Nat.div_add_mod k 64
  rw [fldW_packF (fun i hi => (hf _ (hlo i hi)).2) hcnt.1,
    fldW_packF (fun i hi => (hf _ (hlo i hi)).1) hcnt.1, ek] at e
  exact e

end CFSG.KS.SporSch.HNXP

end
