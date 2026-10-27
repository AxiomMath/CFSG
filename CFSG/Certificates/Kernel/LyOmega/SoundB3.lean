module

public import CFSG.Certificates.Kernel.LyOmega.Defs
public import Certificates.Data.Kernel.LyOmega.Small
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Basify

public section
namespace CFSG.KS.LyOm.SB3
open CFSG.KC.LyOm CFSG.KC.Ord CFSG.KC.LL CFSG.KS.LyOm

private theorem bAnd_true' {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> simp_all

private theorem recB_spec' {g : Nat → Bool} : ∀ n,
    Nat.rec (motive := fun _ => Bool) true
      (fun k ih => Bool.rec (motive := fun _ => Bool) false ih (g k)) n = true →
      ∀ k < n, g k = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, h, k, hk => by
    obtain ⟨h1, h2⟩ := bAnd_true' h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact recB_spec' n h2 k hk
    · exact h1

private theorem allBelow_spec'' {m hi : Nat} {f : Nat → Bool}
    (h : CFSG.KC.Loop.allBelow m hi f = true) :
    ∀ i < m, i < 64 * hi → f i = true := by
  intro i him hih
  have hq : i / 64 < hi := by omega
  have h1 := recB_spec' hi h (i / 64) hq
  have h2 := recB_spec' (g := fun l => Bool.rec (motive := fun _ => Bool) true
    (f (Nat.add (Nat.shiftLeft (i / 64) 6) l)) (Nat.blt (Nat.add (Nat.shiftLeft (i / 64) 6) l) m))
    64 h1 (i % 64) (Nat.mod_lt _ (by omega))
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq]
    omega
  simp only [e, Nat.blt_eq.mpr him] at h2
  exact h2

private theorem fldW_eq' (r o w : ℕ) : fldW r o w = r / 2 ^ o % 2 ^ w := by
  unfold fldW
  change (r >>> o) &&& ((1 <<< w) - 1) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

private theorem sEnt_eq' (X i j : ℕ) : sEnt X i j = X / 2 ^ (77 * i + 11 * j) % 2 ^ 11 := by
  unfold sEnt
  rw [fldW_eq']
  rfl

private theorem key (A B K : ℕ) (h : kronOK A B K = true) :
    K < 2 ^ 26411 ∧ ∀ r < 49, ∀ c < 49,
      K / 2 ^ (539 * r + 11 * c) % 2 ^ 11 =
        (sEnt A (r / 7) (c / 7) * sEnt B (r % 7) (c % 7)) % 5 := by
  unfold kronOK at h
  obtain ⟨h1, h2⟩ := bAnd_true' h
  refine ⟨?_, ?_⟩
  · have h1' : K / 2 ^ 26411 = 0 := by
      rw [← Nat.shiftRight_eq_div_pow]
      exact Nat.eq_of_beq_eq_true h1
    rcases Nat.div_eq_zero_iff.1 h1' with h0 | h0
    · exact absurd h0 (by positivity)
    · exact h0
  · intro r hr c hc
    have := allBelow_spec'' h2 (49 * r + c) (by change 49 * r + c < 2401; omega) (by change 49 * r + c < 64 * 38; omega)
    have e1 : Nat.div (49 * r + c) 49 = r := by change (49 * r + c) / 49 = r; omega
    have e2 : Nat.mod (49 * r + c) 49 = c := by change (49 * r + c) % 49 = c; omega
    simp only [e1, e2] at this
    have := Nat.eq_of_beq_eq_true this
    rw [fldW_eq'] at this
    exact this

theorem kronOK_sound {A B K : ℕ} (h : kronOK A B K = true) :
    LCanon 11 49 49 K ∧ ∀ i j k l : Fin 7, kM K ⟨7 * i + j, by omega⟩ ⟨7 * k + l, by omega⟩ =
      smM A i k * smM B j l := by
  obtain ⟨hK, hs⟩ := key A B K h
  refine ⟨⟨by simpa using hK, ?_⟩, ?_⟩
  · intro i hi j hj
    have := hs i hi j hj
    have e : 11 * 49 * i + 11 * j = 539 * i + 11 * j := by omega
    rw [e, this]
    exact Nat.mod_lt _ (by norm_num)
  · intro i j k l
    have := hs (7 * i + j) (by omega) (7 * k + l) (by omega)
    have e1 : (7 * (i : ℕ) + j) / 7 = i := by omega
    have e2 : (7 * (i : ℕ) + j) % 7 = j := by omega
    have e3 : (7 * (k : ℕ) + l) / 7 = k := by omega
    have e4 : (7 * (k : ℕ) + l) % 7 = l := by omega
    rw [e1, e2, e3, e4] at this
    simp only [kM, smM, ent]
    rw [this]
    rw [sEnt_eq', sEnt_eq']
    rw [ZMod.natCast_mod, Nat.cast_mul]

end CFSG.KS.LyOm.SB3
end
