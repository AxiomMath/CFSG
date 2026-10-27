module

public import CFSG.Certificates.Kernel.LceSTabSound
import CFSG.Certificates.Kernel.BindFProof
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Certificates.BindS

open CFSG.KC CFSG.KC.LceS CFSG.KC.Bind CFSG.Certificates.LCE

theorem mget_eq (M g : ℕ) : mget M g = M / 256 ^ g % 256 := HO.wLet_eq M g

set_option maxRecDepth 100000 in
theorem allFF_byte : ∀ x < 256, mget allFF x = 255 := by decide

theorem mset_spec {M x v : ℕ} (h : mset M x v ≠ 0) :
    0 < M ∧ v < 255 ∧ x < 256 ∧ mget M x = 255 ∧
      ∀ y, mget (mset M x v) y = if y = x then v else mget M y := by
  revert h
  unfold mset
  cases hc : andB (Nat.blt 0 M) (andB (Nat.blt v 255) (andB (Nat.blt x 256) (Nat.beq (mget M x) 255)))
  · intro h
    exact absurd rfl h
  · intro _
    simp only [HO.andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hc
    obtain ⟨hM, hv, hx, hb⟩ := hc
    refine ⟨hM, hv, hx, hb, fun y => ?_⟩
    change mget (M - (255 - v) <<< (8 * x)) y = _
    rw [Nat.shiftLeft_eq, HO.two_pow_eight_mul]
    rw [mget_eq] at hb
    obtain ⟨q, hq⟩ : ∃ q, M / 256 ^ x = q := ⟨_, rfl⟩
    rw [hq] at hb
    have hM' : M = M % 256 ^ x + q * 256 ^ x := by rw [← hq, Nat.mod_add_div']
    have hr : M % 256 ^ x < 256 ^ x := Nat.mod_lt _ (by positivity)
    have hqb : 255 - v ≤ q := by omega
    have hsub : M - (255 - v) * 256 ^ x = M % 256 ^ x + (q - (255 - v)) * 256 ^ x := by
      have h1 : (q - (255 - v)) * 256 ^ x = q * 256 ^ x - (255 - v) * 256 ^ x := Nat.sub_mul _ _ _
      have h2 : (255 - v) * 256 ^ x ≤ q * 256 ^ x := Nat.mul_le_mul_right _ hqb
      omega
    rw [mget_eq, mget_eq, hsub]
    conv_rhs => rw [hM']
    rw [HO.byte_concat hr, HO.byte_concat hr]
    rcases lt_trichotomy y x with h | rfl | h
    · simp only [h, Nat.ne_of_lt h, ↓reduceIte]
    · simp only [lt_irrefl, ↓reduceIte, Nat.sub_self, pow_zero, Nat.div_one]
      omega
    · obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_lt h
      have e : y - x = t + 1 := by omega
      simp only [Nat.not_lt_of_gt h, Nat.ne_of_gt h, ↓reduceIte]
      rw [e, pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
      have e2 : (q - (255 - v)) / 256 = q / 256 := by omega
      rw [e2]

theorem stMap_inv (ST : ℕ → ℕ) : ∀ K, stMap ST K ≠ 0 → ∀ x < 256, mget (stMap ST K) x = 255 ∨
    (mget (stMap ST K) x < K ∧ wLen (ST (mget (stMap ST K) x)) = 1 ∧
      wWord (ST (mget (stMap ST K) x)) = 2 * x)
  | 0, _ => fun x hx => Or.inl (allFF_byte x hx)
  | K + 1, h => by
    have e : stMap ST (K + 1) = Bool.rec (motive := fun _ => ℕ) 0
        (mset (stMap ST K) (Nat.shiftRight (wWord (ST K)) 1) K)
        (andB (Nat.beq (wLen (ST K)) 1) (andB (Nat.beq (Nat.land (wWord (ST K)) 1) 0)
          (Nat.blt (wWord (ST K)) 256))) := rfl
    revert h
    rw [e]
    cases hc : andB (Nat.beq (wLen (ST K)) 1) (andB (Nat.beq (Nat.land (wWord (ST K)) 1) 0)
        (Nat.blt (wWord (ST K)) 256))
    · intro h
      exact absurd rfl h
    · intro h
      change mset (stMap ST K) (Nat.shiftRight (wWord (ST K)) 1) K ≠ 0 at h
      change ∀ x < 256, mget (mset (stMap ST K) (Nat.shiftRight (wWord (ST K)) 1) K) x = 255 ∨ _
      simp only [HO.andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hc
      obtain ⟨hl, hev, hlt⟩ := hc
      have hev' : wWord (ST K) % 2 = 0 := by
        rw [← hev]
        exact (Nat.and_two_pow_sub_one_eq_mod _ 1).symm
      obtain ⟨hpos, hK, -, -, hset⟩ := mset_spec h
      have ih := stMap_inv ST K (Nat.pos_iff_ne_zero.mp hpos)
      intro x hx
      rw [hset x]
      split_ifs with hxe
      · refine Or.inr ⟨by omega, hl, ?_⟩
        have hs : Nat.shiftRight (wWord (ST K)) 1 = wWord (ST K) / 2 :=
          Nat.shiftRight_eq_div_pow _ 1
        rw [hxe, hs]
        omega
      · rcases ih x hx with h1 | ⟨h1, h2, h3⟩
        · exact Or.inl h1
        · exact Or.inr ⟨by omega, h2, h3⟩

theorem stMap_sound {ST : ℕ → ℕ} {K M : ℕ} (hM : M = stMap ST K) (h0 : M ≠ 0) :
    ∀ g < 128, mget M g < 255 →
      mget M g < K ∧ wLen (ST (mget M g)) = 1 ∧ wWord (ST (mget M g)) = 2 * g := by
  subst hM
  intro g hg hlt
  rcases stMap_inv ST K h0 g (by omega) with h | h
  · omega
  · exact h

theorem relsSub_sound {G : Type*} [Group G] (pg cg : ℕ → G) {CRT PRT : ℕ → ℕ} {M R PR Hs : ℕ}
    (h : relsSub CRT PRT M R PR Hs = true)
    (hM : ∀ g < 128, mget M g < 255 → mget M g < 127 ∧ cg (mget M g) = pg g)
    (hP : ∀ r < PR, bval pg (wWord (PRT r)) (wLen (PRT r)) = 1)
    (hPL : ∀ r < PR, ∀ q < wLen (PRT r), wLet (wWord (PRT r)) q < 254) :
    ∀ r < R, bval cg (wWord (CRT r)) (wLen (CRT r)) = 1 :=
  CFSG.Certificates.BindL.relsSub_sound' pg cg h hM hP hPL

theorem relsF_sound {G : Type*} [Group G] (pg cg : ℕ → G) {CRT PRT : ℕ → ℕ} {SB ns M R PR Hs : ℕ}
    (h : relsF CRT PRT SB ns M R PR Hs = true) (hsub : subsOK PRT SB ns false = true)
    (hSB : ∀ s < ns, Nat.shiftRight (Nat.land (Nat.shiftRight SB (24 * s)) 16777215) 8 < PR)
    (hM : ∀ g < 128, mget M g < 255 → mget M g < 127 ∧ cg (mget M g) = pg g)
    (hP : ∀ r < PR, bval pg (wWord (PRT r)) (wLen (PRT r)) = 1)
    (hPL : ∀ r < PR, wLen (PRT r) < 256 ∧ ∀ q < wLen (PRT r), wLet (wWord (PRT r)) q < 254) :
    ∀ r < R, bval cg (wWord (CRT r)) (wLen (CRT r)) = 1 :=
  CFSG.Certificates.BindF.relsF_sound' pg cg h hsub hSB hM hP hPL

end CFSG.Certificates.BindS

end
