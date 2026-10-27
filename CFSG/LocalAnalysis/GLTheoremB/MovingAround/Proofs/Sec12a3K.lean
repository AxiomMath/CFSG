module

public import CFSG.Permutation.FinPackWalk
public import CFSG.LocalAnalysis.GLTheoremB.S7Decide

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Sec12a3K

open Equiv Equiv.Perm CFSG.LocalAnalysis.GLTheoremB CFSG.Permutation.FinPack

theorem h16 : 7 ≤ 16 := by norm_num

theorem enc_one : enc (1 : Perm (Fin 7)) = 106181136 := by decide +kernel
theorem enc_a : enc S7.a = 106180641 := by decide +kernel
theorem enc_a2 : enc (S7.a ^ 2) = 106180866 := by decide +kernel
theorem enc_dbl : enc (S7.a * S7.b) = 104153121 := by decide +kernel
theorem enc_x : enc S7.x = 90391056 := by decide +kernel
theorem enc_y : enc S7.y = 70668816 := by decide +kernel
theorem enc_xy : enc (S7.x * S7.y) = 54878736 := by decide +kernel
theorem enc_u : enc S7.u = 39073281 := by decide +kernel
theorem enc_w : enc S7.w = 22294626 := by decide +kernel

@[expose] noncomputable def commK (c d : ℕ) : Bool := Nat.beq (mulK 7 c d) (mulK 7 d c)

theorem commK_iff {σ τ : Perm (Fin 7)} : commK (enc σ) (enc τ) = true ↔ σ * τ = τ * σ :=
  comm_enc_iff h16

theorem enc_sq (σ : Perm (Fin 7)) : enc (σ * σ) = mulK 7 (enc σ) (enc σ) := enc_mul h16 σ σ

theorem enc_cube (σ : Perm (Fin 7)) : enc (σ ^ 3) = mulK 7 (mulK 7 (enc σ) (enc σ)) (enc σ) := by
  rw [pow_three', enc_mul h16, enc_mul h16]

theorem enc_pow_six (σ : Perm (Fin 7)) : enc (σ ^ 6) =
    mulK 7 (mulK 7 (mulK 7 (enc σ) (enc σ)) (enc σ)) (mulK 7 (mulK 7 (enc σ) (enc σ)) (enc σ)) := by
  have e : σ ^ 6 = σ ^ 3 * σ ^ 3 := pow_add σ 3 3
  rw [e, enc_mul h16, enc_cube]

@[expose] noncomputable def qDbl (c : ℕ) : Bool :=
  !(commK c 104153121 && Nat.beq (mulK 7 c c) 106181136 && evenK 7 c) || Nat.beq c 106181136

theorem qDbl_walk : walkK 7 qDbl 7 0 0 0 = true := by decide +kernel

theorem dbl_no_involution_K :
    ∀ g : Perm (Fin 7), Perm.sign g = 1 → g * (S7.a * S7.b) = (S7.a * S7.b) * g → g * g = 1 →
      g = 1 := by
  intro g hs hc hsq
  have h := walkK_sound qDbl_walk g
  have h1 : commK (enc g) 104153121 = true := by rw [← enc_dbl]; exact commK_iff.2 hc
  have h2 : Nat.beq (mulK 7 (enc g) (enc g)) 106181136 = true := by
    rw [← enc_sq, ← enc_one]; exact (beq_enc_iff h16).2 hsq
  have h3 : evenK 7 (enc g) = true := (sign_eq_one_iff_evenK h16 g).1 hs
  rw [qDbl.eq_1, h1, h2, h3] at h
  simp only [Bool.and_self, Bool.not_true, Bool.false_or] at h
  rw [← enc_one] at h
  exact (beq_enc_iff h16).1 h

@[expose] noncomputable def qSix (c : ℕ) : Bool :=
  !(commK c 106180641 && evenK 7 c) ||
    Nat.beq (mulK 7 (mulK 7 (mulK 7 c c) c) (mulK 7 (mulK 7 c c) c)) 106181136

theorem qSix_walk : walkK 7 qSix 7 0 0 0 = true := by decide +kernel

theorem three_cent_pow_six_K :
    ∀ g : Perm (Fin 7), Perm.sign g = 1 → g * S7.a = S7.a * g → g ^ 6 = 1 := by
  intro g hs hc
  have h := walkK_sound qSix_walk g
  have h1 : commK (enc g) 106180641 = true := by rw [← enc_a]; exact commK_iff.2 hc
  have h3 : evenK 7 (enc g) = true := (sign_eq_one_iff_evenK h16 g).1 hs
  rw [qSix.eq_1, h1, h3] at h
  simp only [Bool.and_self, Bool.not_true, Bool.false_or] at h
  rw [← enc_pow_six, ← enc_one] at h
  exact (beq_enc_iff h16).1 h

@[expose] noncomputable def qInv (c : ℕ) : Bool :=
  !(commK c 106180641 && Nat.beq (mulK 7 c c) 106181136 && evenK 7 c) ||
    (Nat.beq c 106181136 || Nat.beq c 90391056 || Nat.beq c 70668816 || Nat.beq c 54878736)

theorem qInv_walk : walkK 7 qInv 7 0 0 0 = true := by decide +kernel

theorem three_cent_involution_mem_K :
    ∀ g : Perm (Fin 7), Perm.sign g = 1 → g * S7.a = S7.a * g → g * g = 1 →
      g = 1 ∨ g = S7.x ∨ g = S7.y ∨ g = S7.x * S7.y := by
  intro g hs hc hsq
  have h := walkK_sound qInv_walk g
  have h1 : commK (enc g) 106180641 = true := by rw [← enc_a]; exact commK_iff.2 hc
  have h2 : Nat.beq (mulK 7 (enc g) (enc g)) 106181136 = true := by
    rw [← enc_sq, ← enc_one]; exact (beq_enc_iff h16).2 hsq
  have h3 : evenK 7 (enc g) = true := (sign_eq_one_iff_evenK h16 g).1 hs
  rw [qInv.eq_1, h1, h2, h3] at h
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h
  rw [← enc_one, ← enc_x, ← enc_y, ← enc_xy, beq_enc_iff h16, beq_enc_iff h16, beq_enc_iff h16,
    beq_enc_iff h16] at h
  rcases h with ((h | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

@[expose] noncomputable def qFpf (c : ℕ) : Bool :=
  !(commK c 106180641 && Nat.beq (mulK 7 (mulK 7 c c) c) 106181136 && !Nat.beq c 106181136 &&
      !Nat.beq c 106180641 && !Nat.beq c 106180866) ||
    (!commK c 90391056 && !commK c 70668816 && !commK c 54878736)

theorem qFpf_walk : walkK 7 qFpf 7 0 0 0 = true := by decide +kernel

theorem fix_comm {τ v : Perm (Fin 7)} (h : τ * v * τ⁻¹ = v) : τ * v = v * τ := by
  calc τ * v = τ * v * τ⁻¹ * τ := by group
    _ = v * τ := by rw [h]

theorem three_fpf_check_K :
    ∀ τ : Perm (Fin 7), τ * S7.a = S7.a * τ → τ ^ 3 = 1 → τ ≠ 1 → τ ≠ S7.a → τ ≠ S7.a ^ 2 →
      ∀ v : Perm (Fin 7), v ∈ [S7.x, S7.y, S7.x * S7.y] → τ * v * τ⁻¹ = v → v = 1 := by
  intro τ hc h3 n1 na na2 v hv hfix
  have h := walkK_sound qFpf_walk τ
  have h1 : commK (enc τ) 106180641 = true := by rw [← enc_a]; exact commK_iff.2 hc
  have h2 : Nat.beq (mulK 7 (mulK 7 (enc τ) (enc τ)) (enc τ)) 106181136 = true := by
    rw [← enc_cube, ← enc_one]; exact (beq_enc_iff h16).2 h3
  have h4 : Nat.beq (enc τ) 106181136 = false := by rw [← enc_one]; exact beq_enc_false h16 n1
  have h5 : Nat.beq (enc τ) 106180641 = false := by rw [← enc_a]; exact beq_enc_false h16 na
  have h6 : Nat.beq (enc τ) 106180866 = false := by rw [← enc_a2]; exact beq_enc_false h16 na2
  rw [qFpf.eq_1, h1, h2, h4, h5, h6] at h
  simp only [Bool.not_false, Bool.and_self, Bool.and_true, Bool.true_and, Bool.not_true,
    Bool.false_or, Bool.and_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨hx, hy⟩, hxy⟩ := h
  have hcv := fix_comm hfix
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
  exfalso
  rcases hv with rfl | rfl | rfl
  · rw [← enc_x, ← Bool.not_eq_true, commK_iff] at hx
    exact hx hcv
  · rw [← enc_y, ← Bool.not_eq_true, commK_iff] at hy
    exact hy hcv
  · rw [← enc_xy, ← Bool.not_eq_true, commK_iff] at hxy
    exact hxy hcv

@[expose] noncomputable def qGens (c : ℕ) : Bool :=
  !(commK c 90391056 && commK c 70668816 && commK c 39073281 && commK c 22294626) ||
    Nat.beq c 106181136

theorem qGens_walk : walkK 7 qGens 7 0 0 0 = true := by decide +kernel

theorem centralizer_gens_trivial_K :
    ∀ c : Perm (Fin 7), c * S7.x = S7.x * c → c * S7.y = S7.y * c →
      c * S7.u = S7.u * c → c * S7.w = S7.w * c → c = 1 := by
  intro c hx hy hu hw
  have h := walkK_sound qGens_walk c
  have h1 : commK (enc c) 90391056 = true := by rw [← enc_x]; exact commK_iff.2 hx
  have h2 : commK (enc c) 70668816 = true := by rw [← enc_y]; exact commK_iff.2 hy
  have h3 : commK (enc c) 39073281 = true := by rw [← enc_u]; exact commK_iff.2 hu
  have h4 : commK (enc c) 22294626 = true := by rw [← enc_w]; exact commK_iff.2 hw
  rw [qGens.eq_1, h1, h2, h3, h4] at h
  simp only [Bool.and_self, Bool.not_true, Bool.false_or] at h
  rw [← enc_one] at h
  exact (beq_enc_iff h16).1 h

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Sec12a3K
