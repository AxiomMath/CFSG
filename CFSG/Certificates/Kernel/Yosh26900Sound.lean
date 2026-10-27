module

public import Certificates.Data.Kernel.Yosh26900
public import CFSG.Certificates.Kernel.Misc.PermClosSound
import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CFSG.KC.Yosh26900

open CFSG.KC.Ord CFSG.KC.LQT CFSG.KC.LQT.P CFSG.KC.Misc.Clos

theorem letN_eq (y : ℕ) (k : ℕ → ℕ) : letN y k = k y := by
  cases y <;> rfl

theorem imW_G (G : ℕ → ℕ) {l : ℕ} (hl : l < 3) : imW (G 0) (G 1) (G 2) l = G l := by
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl <;> rfl

theorem imW_lt {H : Type*} (enc : H → ℕ) (f : ℕ → H) {s0 ec y : ℕ} (h0 : enc (f 0) = s0)
    (h1 : enc (f 1) = ec) (h2 : enc (f 2) = y) : ∀ l < 3, enc (f l) = imW s0 ec y l := by
  intro l hl
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl
  exacts [h0, h1, h2]

theorem tree_zero {M : ℕ → ℕ → ℕ} {one : ℕ} {G : ℕ → ℕ} {nG : ℕ} {E PA : ℕ → ℕ}
    (h : treeAt M one G nG E PA 0 = true) : E 0 = one := Nat.eq_of_beq_eq_true h

theorem tree_step {M : ℕ → ℕ → ℕ} {one : ℕ} {G : ℕ → ℕ} {nG : ℕ} {E PA : ℕ → ℕ} {k : ℕ}
    (h : treeAt M one G nG E PA (k + 1) = true) :
    Nat.land (PA (k + 1)) 16777215 < k + 1 ∧
      E (k + 1) = M (E (Nat.land (PA (k + 1)) 16777215)) (G (Nat.shiftRight (PA (k + 1)) 24)) := by
  have h' : letB (PA (k + 1)) (fun r => letB (Nat.land r 16777215) fun p =>
      letB (Nat.shiftRight r 24) fun l => andB (Nat.blt p (k + 1))
        (andB (Nat.blt l nG) (Nat.beq (E (k + 1)) (M (E p) (G l))))) = true := h
  rw [P.letB_eq, P.letB_eq, P.letB_eq] at h'
  obtain ⟨hp, h'⟩ := andB_iff.1 h'
  obtain ⟨-, h'⟩ := andB_iff.1 h'
  exact ⟨Nat.blt_eq.mp hp, Nat.eq_of_beq_eq_true h'⟩

section Path

variable {H : Type*} [Group H] {enc : H → ℕ} (henc : ClosEnc enc (mul 14) (one 14))
  {G E PA : ℕ → ℕ} {nG N : ℕ} {x w : ℕ → H} (hx : ∀ k < N, enc (x k) = E k)
  (hw : ∀ l < 3, enc (w l) = G l)
  (ht : ∀ k < N, treeAt (mul 14) (one 14) G nG E PA k = true)
  (hl : ∀ k < N, Nat.shiftRight (PA k) 24 < 3)

include henc hx hw ht hl

theorem x_step {k : ℕ} (hk : k + 1 < N) :
    x (k + 1) = x (Nat.land (PA (k + 1)) 16777215) * w (Nat.shiftRight (PA (k + 1)) 24) := by
  obtain ⟨hp, he⟩ := tree_step (ht (k + 1) hk)
  apply henc.inj
  rw [henc.enc_mul, hx (k + 1) hk, hx _ (by omega), hw _ (hl (k + 1) hk), he]

omit hw hl in
theorem x_zero (hN : 0 < N) : x 0 = 1 :=
  henc.inj (by rw [hx 0 hN, tree_zero (ht 0 hN), henc.enc_one])

theorem path_sound (φ : H →* H) {s0 ec y : ℕ} (himg : ∀ l < 3, enc (φ (w l)) = imW s0 ec y l) :
    ∀ f k, k < f → k < N → pathK PA s0 ec y f k = enc (φ (x k)) := by
  intro f
  induction f with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero _)
  | succ f ih =>
    intro k hkf hkN
    cases k with
    | zero =>
      rw [x_zero henc hx ht hkN, map_one, henc.enc_one]
      rfl
    | succ k =>
      have hp := (tree_step (ht (k + 1) hkN)).1
      have key : mul 14 (pathK PA s0 ec y f (Nat.land (PA (k + 1)) 16777215))
          (imW s0 ec y (Nat.shiftRight (PA (k + 1)) 24)) = enc (φ (x (k + 1))) := by
        rw [ih _ (by omega) (by omega), ← himg _ (hl (k + 1) hkN), ← henc.enc_mul, ← map_mul,
          ← x_step henc hx hw ht hl hkN]
      have hs : pathK PA s0 ec y (f + 1) (k + 1) = letN (PA (k + 1)) fun r =>
          mul 14 (pathK PA s0 ec y f (Nat.land r 16777215)) (imW s0 ec y (Nat.shiftRight r 24)) :=
        rfl
      rw [hs, letN_eq]
      exact key

theorem vals_sound (φ : H →* H) {s0 ec y : ℕ} (himg : ∀ l < 3, enc (φ (w l)) = imW s0 ec y l)
    {V : ℕ → ℕ} (hv : ∀ k < N, vAt PA V s0 ec y k = true) :
    ∀ k < N, V k = enc (φ (x k)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    cases k with
    | zero =>
      have h : Nat.beq (V 0) (one 14) = true := hv 0 hk
      rw [Nat.eq_of_beq_eq_true h, x_zero henc hx ht hk, map_one, henc.enc_one]
    | succ k =>
      have h : letB (PA (k + 1)) (fun r => letB (Nat.land r 16777215) fun p =>
          andB (Nat.blt p (k + 1)) (Nat.beq (V (k + 1))
            (mul 14 (V p) (imW s0 ec y (Nat.shiftRight r 24))))) = true := hv (k + 1) hk
      rw [P.letB_eq, P.letB_eq] at h
      obtain ⟨hp, h⟩ := andB_iff.1 h
      have hp' := Nat.blt_eq.mp hp
      rw [Nat.eq_of_beq_eq_true h, ih _ hp' (by omega), ← himg _ (hl (k + 1) hk),
        ← henc.enc_mul, ← map_mul, ← x_step henc hx hw ht hl hk]

end Path

theorem ord8_iff {H : Type*} [Group H] {enc : H → ℕ} (henc : ClosEnc enc (mul 14) (one 14))
    (z : H) : ord8 (enc z) = true ↔ z ^ 8 = 1 ∧ z ^ 4 ≠ 1 := by
  have h4 : z ^ 4 = z * z * (z * z) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have h8 : z ^ 8 = z * z * (z * z) * (z * z * (z * z)) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have e1 : ∀ a b : H, mul 14 (enc a) (enc b) = enc (a * b) := fun a b => (henc.enc_mul a b).symm
  have hiff : ∀ a : H, Nat.beq (enc a) (one 14) = true ↔ a = 1 := fun a => by
    rw [beq_iff, ← henc.enc_one]
    exact henc.inj.eq_iff
  unfold ord8
  rw [P.letB_eq, P.letB_eq, e1, e1, e1, andB_iff, notB_iff, hiff, hiff, h4, h8]

theorem clsAt_cases {E PA CL SV : ℕ → ℕ} {s0 e ec g j : ℕ}
    (h : clsAt E PA CL SV s0 e ec g j = true) :
    notB (ord8 (E j)) = true ∨ notB (Nat.beq (pathK PA s0 ec (E j) 384 j) g) = true ∨
      homAt E PA s0 e ec g (E j) (fl (CL j) 2 511) (fl (CL j) 11 3) (fl (CL j) 13 511) = true ∨
      SV (fl (CL j) 2 3) = j := by
  unfold clsAt at h
  rw [P.letB_eq, P.letB_eq] at h
  revert h
  cases h0 : Nat.beq (Nat.land (CL j) 3) 0
  · cases h1 : Nat.beq (Nat.land (CL j) 3) 1
    · cases h2 : Nat.beq (Nat.land (CL j) 3) 2
      · intro h
        exact Or.inr (Or.inr (Or.inr (Nat.eq_of_beq_eq_true h)))
      · intro h
        exact Or.inr (Or.inr (Or.inl h))
    · intro h
      exact Or.inr (Or.inl h)
  · intro h
    exact Or.inl h

theorem fl_lt (r a m : ℕ) : fl r a m ≤ m := Nat.and_le_right

theorem cls_sound {H : Type*} [Group H] {enc : H → ℕ} (henc : ClosEnc enc (mul 14) (one 14))
    {G E PA CL SV : ℕ → ℕ} {nG : ℕ} {x w : ℕ → H} (hx : ∀ k < 384, enc (x k) = E k)
    (hw : ∀ l < 3, enc (w l) = G l)
    (ht : ∀ k < 384, treeAt (mul 14) (one 14) G nG E PA k = true)
    (hl : ∀ k < 384, Nat.shiftRight (PA k) 24 < 3) {ec : ℕ}
    (hcl : ∀ j < 384, clsAt E PA CL SV (G 0) (G 1) ec (G 2) j = true)
    (hg8 : w 2 ^ 8 = 1 ∧ w 2 ^ 4 ≠ 1)
    (ψ : MulAut H) (h0 : ψ (w 0) = w 0) (h1 : enc (ψ (w 1)) = ec) (hinv : ∀ y, ψ (ψ y) = y)
    {j : ℕ} (hj : j < 384) (hψg : ψ (w 2) = x j) : ∃ s < 4, SV s = j := by
  have himg : ∀ l < 3, enc ((ψ : H →* H) (w l)) = imW (G 0) ec (E j) l := by
    refine imW_lt enc (fun l => (ψ : H →* H) (w l)) ?_ h1 ?_
    · change enc (ψ (w 0)) = G 0
      rw [h0, hw 0 (by norm_num)]
    · change enc (ψ (w 2)) = E j
      rw [hψg, hx j hj]
  rcases clsAt_cases (hcl j hj) with h | h | h | h
  · exfalso
    rw [← hx j hj, ← hψg] at h
    have h8 := (ord8_iff henc (ψ (w 2))).2 ⟨by rw [← map_pow, hg8.1, map_one], fun h4 =>
      hg8.2 (ψ.injective (by rw [map_pow, h4, map_one]))⟩
    rw [h8] at h
    exact absurd h (by decide)
  · exfalso
    rw [path_sound henc hx hw ht hl (ψ : H →* H) himg 384 j hj hj] at h
    have : ((ψ : H →* H) (x j)) = w 2 := by
      change ψ (x j) = w 2
      rw [← hψg, hinv]
    rw [this, hw 2 (by norm_num), Nat.beq_refl] at h
    exact absurd h (by decide)
  · exfalso
    unfold homAt at h
    obtain ⟨hk, h⟩ := andB_iff.1 h
    obtain ⟨ht3, h⟩ := andB_iff.1 h
    obtain ⟨hm, h⟩ := andB_iff.1 h
    obtain ⟨he, h⟩ := andB_iff.1 h
    have hk' := Nat.blt_eq.mp hk
    have ht3' := Nat.blt_eq.mp ht3
    have hm' := Nat.blt_eq.mp hm
    have hxm : x (fl (CL j) 13 511) = x (fl (CL j) 2 511) * w (fl (CL j) 11 3) := by
      apply henc.inj
      rw [henc.enc_mul, hx _ hm', hx _ hk', hw _ ht3', Nat.eq_of_beq_eq_true he, imW_G G ht3']
    rw [path_sound henc hx hw ht hl (ψ : H →* H) himg 384 _ hm' hm',
      path_sound henc hx hw ht hl (ψ : H →* H) himg 384 _ hk' hk', ← himg _ ht3',
      ← henc.enc_mul, ← map_mul, ← hxm, Nat.beq_refl] at h
    exact absurd h (by decide)
  · exact ⟨_, Nat.lt_succ_of_le (fl_lt _ _ _), h⟩

end CFSG.KC.Yosh26900

end
