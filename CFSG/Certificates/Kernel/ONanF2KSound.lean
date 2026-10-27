module

public import Certificates.Data.Kernel.ONanF2K.Defs

public section

namespace CFSG.KC.ONanF2K

open CFSG.OddStandard.ONanRec.F2

theorem dmul_lane : ∀ i j : Fin 8, dmul i j = Fin.ofNat 8 (lane dmulT (i.val * 8 + j.val) 3) := by
  decide +kernel

theorem ck_lane : ∀ i j : Fin 8, ck i j = ((lane ckT (i.val * 8 + j.val) 2 : ℕ) : ZMod 4) := by
  decide +kernel

theorem me_lane : ∀ (d : Fin 8) (i k : Fin 3),
    me d i k = ((lane meT (d.val * 9 + (i.val * 3 + k.val)) 2 : ℕ) : ZMod 4) := by
  decide +kernel

private theorem natCast_eq {m n : ℕ} (h : m % 4 = n % 4) : ((m : ℕ) : ZMod 4) = ((n : ℕ) : ZMod 4) :=
  (ZMod.natCast_eq_natCast_iff' m n 4).2 h

theorem decN_mk {a b c e : ℕ} (hb : b < 4) (hc : c < 4) (he : e < 4) :
    decN (a * 64 + b * 16 + c * 4 + e) =
      ⟨Fin.ofNat 8 a, ((b : ℕ) : ZMod 4), ((c : ℕ) : ZMod 4), ((e : ℕ) : ZMod 4)⟩ := by
  refine AlpE.ext ?_ ?_ ?_ ?_
  · change Fin.ofNat 8 _ = Fin.ofNat 8 a
    congr 1
    omega
  · exact natCast_eq (by omega)
  · exact natCast_eq (by omega)
  · exact natCast_eq (by omega)

theorem decN_mod (x : ℕ) : decN (x % 512) = decN x := by
  refine AlpE.ext ?_ ?_ ?_ ?_
  · change Fin.ofNat 8 _ = Fin.ofNat 8 _
    apply Fin.ext
    simp only [Fin.val_ofNat]
    omega
  · exact natCast_eq (by omega)
  · exact natCast_eq (by omega)
  · exact natCast_eq (by omega)

theorem decN_zero : decN 0 = 1 := by decide +kernel

theorem decN_cdN (a : AlpE) : decN (cdN a) = a := by
  have h0 := a.v0.val_lt
  have h1 := a.v1.val_lt
  have h2 := a.v2.val_lt
  unfold cdN
  rw [decN_mk h0 h1 h2]
  refine AlpE.ext ?_ ?_ ?_ ?_
  · exact Fin.ext (by simp [Fin.val_ofNat])
  · exact ZMod.natCast_zmod_val a.v0
  · exact ZMod.natCast_zmod_val a.v1
  · exact ZMod.natCast_zmod_val a.v2

theorem cdN_lt (a : AlpE) : cdN a < 512 := by
  have := a.d.isLt
  have h0 := a.v0.val_lt
  have h1 := a.v1.val_lt
  have h2 := a.v2.val_lt
  unfold cdN
  omega

theorem decN_eq_iff (x y : ℕ) : decN x = decN y ↔ x % 512 = y % 512 := by
  constructor
  · intro h
    have hd := congrArg (fun a => a.d.val) h
    have h0 := congrArg (fun a => a.v0.val) h
    have h1 := congrArg (fun a => a.v1.val) h
    have h2 := congrArg (fun a => a.v2.val) h
    simp only [decN, Fin.val_ofNat, ZMod.val_natCast] at hd h0 h1 h2
    omega
  · intro h
    rw [← decN_mod x, h, decN_mod]

theorem decN_mul (x y : ℕ) : decN x * decN y = decN (mulK x y) := by
  rw [mulK_eq, decN_mk (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num))]
  change AlpE.mul (decN x) (decN y) = _
  simp only [AlpE.mul, AlpE.act, decN, me_lane, ck_lane, dmul_lane, Fin.val_ofNat, Fin.val_zero,
    Fin.val_one, Fin.val_two]
  refine AlpE.ext ?_ ?_ ?_ ?_
  · rfl
  · push_cast [ZMod.natCast_mod]
    ring_nf
  · push_cast [ZMod.natCast_mod]
    ring_nf
  · push_cast [ZMod.natCast_mod]
    ring_nf

theorem decN_pow (x n : ℕ) : decN x ^ n = decN (powK x n) := by
  induction n with
  | zero => rw [pow_zero, ← decN_zero]; rfl
  | succ n ih =>
    rw [pow_succ, ih, decN_mul]
    rfl

theorem decN_inv (hexp : expK = true) (x : ℕ) : (decN x)⁻¹ = decN (invK x) := by
  have hx : powK (x % 512) 16 = 0 := by
    have := List.all_eq_true.1 hexp (x % 512) (List.mem_range.2 (Nat.mod_lt _ (by norm_num)))
    simpa using this
  have h16 : decN x ^ 16 = 1 := by
    rw [← decN_mod, decN_pow, hx, decN_zero]
  apply inv_eq_of_mul_eq_one_left
  unfold invK
  rw [← decN_pow, ← pow_succ, h16]

theorem unpackL_lt (n : ℕ) : ∀ P, ∀ c ∈ unpackL P n, c < 512 := by
  induction n with
  | zero => intro P c hc; simp [unpackL] at hc
  | succ n ih =>
    intro P c hc
    change c ∈ Nat.mod P 512 :: unpackL (Nat.shiftRight P 9) n at hc
    rcases List.mem_cons.1 hc with h | h
    · rw [h]
      exact Nat.mod_lt _ (by norm_num)
    · exact ih _ c h

theorem mem_map_decN {L : List ℕ} (hL : ∀ c ∈ L, c < 512) (x : ℕ) :
    decN x ∈ L.map decN ↔ x % 512 ∈ L := by
  rw [List.mem_map]
  constructor
  · rintro ⟨c, hc, h⟩
    rw [decN_eq_iff, Nat.mod_eq_of_lt (hL c hc)] at h
    rwa [← h]
  · intro h
    refine ⟨x % 512, h, ?_⟩
    rw [decN_mod]

theorem exists_decN (a : AlpE) : ∃ c < 512, decN c = a := ⟨cdN a, cdN_lt a, decN_cdN a⟩

end CFSG.KC.ONanF2K
