module

public import Certificates.Data.Kernel.TwD5ReflK
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Refl

public section

namespace CFSG.KC.TwD5R

open scoped Matrix

@[expose] noncomputable def decV (x : ℕ) : Fin 6 → ZMod 3 := fun j => (dg x j : ZMod 3)

@[expose] def encV (u : Fin 6 → ZMod 3) : ℕ :=
  (u 0).val + 3 * (u 1).val + 9 * (u 2).val + 27 * (u 3).val + 81 * (u 4).val + 243 * (u 5).val

@[expose] noncomputable def reflK (key : ℕ) : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  1 + Matrix.vecMulVec (decV (key / 729)) (decV (key % 729))

theorem dg_lt (x j : ℕ) : dg x j < 3 := Nat.mod_lt _ (by norm_num)

theorem dg_eq (x j : ℕ) : dg x j = x / 3 ^ j % 3 := rfl

theorem dg_sum {c0 c1 c2 c3 c4 c5 : ℕ} (h0 : c0 < 3) (h1 : c1 < 3) (h2 : c2 < 3) (h3 : c3 < 3)
    (h4 : c4 < 3) (h5 : c5 < 3) (j : Fin 6) :
    dg (c0 + 3 * c1 + 9 * c2 + 27 * c3 + 81 * c4 + 243 * c5) j = ![c0, c1, c2, c3, c4, c5] j := by
  rw [dg_eq]
  fin_cases j <;> simp <;> omega

theorem eq_sum_dg {x : ℕ} (hx : x < 729) :
    x = dg x 0 + 3 * dg x 1 + 9 * dg x 2 + 27 * dg x 3 + 81 * dg x 4 + 243 * dg x 5 := by
  simp only [dg_eq, Nat.reducePow, Nat.div_one]
  omega

theorem encV_lt (u : Fin 6 → ZMod 3) : encV u < 729 := by
  have h0 := ZMod.val_lt (u 0)
  have h1 := ZMod.val_lt (u 1)
  have h2 := ZMod.val_lt (u 2)
  have h3 := ZMod.val_lt (u 3)
  have h4 := ZMod.val_lt (u 4)
  have h5 := ZMod.val_lt (u 5)
  unfold encV
  omega

theorem decV_encV (u : Fin 6 → ZMod 3) : decV (encV u) = u := by
  funext j
  have h := dg_sum (ZMod.val_lt (u 0)) (ZMod.val_lt (u 1)) (ZMod.val_lt (u 2))
    (ZMod.val_lt (u 3)) (ZMod.val_lt (u 4)) (ZMod.val_lt (u 5)) j
  unfold decV encV
  rw [h]
  fin_cases j <;> simp

theorem encV_decV {x : ℕ} (hx : x < 729) : encV (decV x) = x := by
  have hv : ∀ j, (decV x j).val = dg x j := fun j => by
    unfold decV
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (dg_lt x j)]
  unfold encV
  rw [hv, hv, hv, hv, hv, hv]
  exact (eq_sum_dg hx).symm

theorem dot_cast (v f : ℕ) : ((dot v f : ℕ) : ZMod 3) = decV v ⬝ᵥ decV f := by
  rw [show dot v f = (dg v 0 * dg f 0 + dg v 1 * dg f 1 + (dg v 2 * dg f 2 + dg v 3 * dg f 3) +
    (dg v 4 * dg f 4 + dg v 5 * dg f 5)) % 3 from rfl, ZMod.natCast_mod]
  push_cast
  simp only [dotProduct, Fin.sum_univ_six, decV]
  simp
  ring

theorem dot_lt (v f : ℕ) : dot v f < 3 := Nat.mod_lt _ (by norm_num)

theorem dot_eq_one {v f : ℕ} : dot v f = 1 ↔ decV f ⬝ᵥ decV v = 1 := by
  rw [dotProduct_comm, ← dot_cast]
  rcases (show dot v f = 0 ∨ dot v f = 1 ∨ dot v f = 2 by have := dot_lt v f; omega)
    with h | h | h <;> rw [h] <;> decide

theorem dot_eq_zero {x f : ℕ} : dot x f = 0 ↔ decV f ⬝ᵥ decV x = 0 := by
  rw [dotProduct_comm, ← dot_cast]
  rcases (show dot x f = 0 ∨ dot x f = 1 ∨ dot x f = 2 by have := dot_lt x f; omega)
    with h | h | h <;> rw [h] <;> decide

theorem negV_eq (x : ℕ) :
    negV x = 2 * dg x 0 % 3 + 3 * (2 * dg x 1 % 3) + 9 * (2 * dg x 2 % 3) +
      27 * (2 * dg x 3 % 3) + 81 * (2 * dg x 4 % 3) + 243 * (2 * dg x 5 % 3) := by
  rw [show negV x = 0 + 2 * dg x 0 % 3 * 3 ^ 0 + 2 * dg x 1 % 3 * 3 ^ 1 + 2 * dg x 2 % 3 * 3 ^ 2 +
    2 * dg x 3 % 3 * 3 ^ 3 + 2 * dg x 4 % 3 * 3 ^ 4 + 2 * dg x 5 % 3 * 3 ^ 5 from rfl]
  ring

theorem two_eq_neg_one : (2 : ZMod 3) = -1 := by decide

theorem decV_negV (x : ℕ) : decV (negV x) = -decV x := by
  funext j
  have h := dg_sum (Nat.mod_lt (2 * dg x 0) (by norm_num : 0 < 3))
    (Nat.mod_lt (2 * dg x 1) (by norm_num : 0 < 3)) (Nat.mod_lt (2 * dg x 2) (by norm_num : 0 < 3))
    (Nat.mod_lt (2 * dg x 3) (by norm_num : 0 < 3)) (Nat.mod_lt (2 * dg x 4) (by norm_num : 0 < 3))
    (Nat.mod_lt (2 * dg x 5) (by norm_num : 0 < 3)) j
  unfold decV
  rw [negV_eq, h]
  fin_cases j <;> simp [ZMod.natCast_mod, two_eq_neg_one]

theorem negV_lt (x : ℕ) : negV x < 729 := by
  rw [negV_eq]
  omega

theorem reflV_eq (key x : ℕ) :
    reflV key x = (dg x 0 + dot x (key % 729) * dg (key / 729) 0) % 3 +
      3 * ((dg x 1 + dot x (key % 729) * dg (key / 729) 1) % 3) +
      9 * ((dg x 2 + dot x (key % 729) * dg (key / 729) 2) % 3) +
      27 * ((dg x 3 + dot x (key % 729) * dg (key / 729) 3) % 3) +
      81 * ((dg x 4 + dot x (key % 729) * dg (key / 729) 4) % 3) +
      243 * ((dg x 5 + dot x (key % 729) * dg (key / 729) 5) % 3) := by
  rw [show reflV key x = 0 + (dg x 0 + dot x (key % 729) * dg (key / 729) 0) % 3 * 3 ^ 0 +
    (dg x 1 + dot x (key % 729) * dg (key / 729) 1) % 3 * 3 ^ 1 +
    (dg x 2 + dot x (key % 729) * dg (key / 729) 2) % 3 * 3 ^ 2 +
    (dg x 3 + dot x (key % 729) * dg (key / 729) 3) % 3 * 3 ^ 3 +
    (dg x 4 + dot x (key % 729) * dg (key / 729) 4) % 3 * 3 ^ 4 +
    (dg x 5 + dot x (key % 729) * dg (key / 729) 5) % 3 * 3 ^ 5 from rfl]
  ring

theorem decV_reflV (key x : ℕ) : decV (reflV key x) = reflK key *ᵥ decV x := by
  funext j
  have hm : ∀ a, a % 3 < 3 := fun a => Nat.mod_lt a (by norm_num)
  have h := dg_sum (hm (dg x 0 + dot x (key % 729) * dg (key / 729) 0))
    (hm (dg x 1 + dot x (key % 729) * dg (key / 729) 1))
    (hm (dg x 2 + dot x (key % 729) * dg (key / 729) 2))
    (hm (dg x 3 + dot x (key % 729) * dg (key / 729) 3))
    (hm (dg x 4 + dot x (key % 729) * dg (key / 729) 4))
    (hm (dg x 5 + dot x (key % 729) * dg (key / 729) 5)) j
  have hd := dot_cast x (key % 729)
  rw [reflV_eq, decV, h]
  unfold reflK
  rw [Matrix.add_mulVec, Matrix.one_mulVec]
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Fin.sum_univ_six] at hd ⊢
  fin_cases j <;> simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Fin.sum_univ_six,
    ZMod.natCast_mod, decV, hd] <;> ring

theorem keyOK_iff {k : ℕ} :
    keyOK k = true ↔ k < 531441 ∧ canon (k / 729) = true ∧ dot (k / 729) (k % 729) = 1 := by
  have e1 : Nat.blt k 531441 = decide (k < 531441) := Bool.eq_iff_iff.mpr (by simp [Nat.blt_eq])
  have e3 : Nat.beq (dot (k / 729) (k % 729)) 1 = decide (dot (k / 729) (k % 729) = 1) :=
    Bool.eq_iff_iff.mpr (by simp [Nat.beq_eq])
  change Bool.rec false (Bool.rec false (Nat.beq (dot (k / 729) (k % 729)) 1) (canon (k / 729)))
    (Nat.blt k 531441) = true ↔ _
  rw [e1, e3]
  cases canon (k / 729) <;> by_cases ha : k < 531441 <;> by_cases hb : dot (k / 729) (k % 729) = 1 <;>
    simp [ha, hb]

theorem canon_or_negV : ∀ x, x < 729 → x ≠ 0 → canon x = true ∨ canon (negV x) = true := by
  decide +kernel

theorem vecMulVec_neg_neg (v f : Fin 6 → ZMod 3) :
    Matrix.vecMulVec (-v) (-f) = Matrix.vecMulVec v f := by
  ext i j
  simp [Matrix.vecMulVec_apply]

theorem key_of_pair {cv cf : ℕ} (hv : cv < 729) (hf : cf < 729) (h0 : cv ≠ 0) :
    ∃ k, k < 531441 ∧ canon (k / 729) = true ∧ (dot (k / 729) (k % 729) = dot cv cf) ∧
      reflK k = 1 + Matrix.vecMulVec (decV cv) (decV cf) := by
  rcases canon_or_negV cv hv h0 with hc | hc
  · refine ⟨cv * 729 + cf, by omega, ?_, ?_, ?_⟩
    · rw [show (cv * 729 + cf) / 729 = cv by omega]
      exact hc
    · rw [show (cv * 729 + cf) / 729 = cv by omega, show (cv * 729 + cf) % 729 = cf by omega]
    · unfold reflK
      rw [show (cv * 729 + cf) / 729 = cv by omega, show (cv * 729 + cf) % 729 = cf by omega]
  · have hn1 := negV_lt cv
    have hn2 := negV_lt cf
    refine ⟨negV cv * 729 + negV cf, by omega, ?_, ?_, ?_⟩
    · rw [show (negV cv * 729 + negV cf) / 729 = negV cv by omega]
      exact hc
    · rw [show (negV cv * 729 + negV cf) / 729 = negV cv by omega,
        show (negV cv * 729 + negV cf) % 729 = negV cf by omega]
      have e1 := dot_cast (negV cv) (negV cf)
      have e2 := dot_cast cv cf
      rw [decV_negV, decV_negV, neg_dotProduct, dotProduct_neg, neg_neg, ← e2] at e1
      have l1 := dot_lt (negV cv) (negV cf)
      have l2 := dot_lt cv cf
      rcases (show dot cv cf = 0 ∨ dot cv cf = 1 ∨ dot cv cf = 2 by omega) with h | h | h <;>
        rcases (show dot (negV cv) (negV cf) = 0 ∨ dot (negV cv) (negV cf) = 1 ∨
          dot (negV cv) (negV cf) = 2 by omega) with h' | h' | h' <;>
        rw [h, h'] at e1 <;> first | exact absurd e1 (by decide) | rw [h, h']
    · unfold reflK
      rw [show (negV cv * 729 + negV cf) / 729 = negV cv by omega,
        show (negV cv * 729 + negV cf) % 729 = negV cf by omega, decV_negV, decV_negV,
        vecMulVec_neg_neg]

theorem exists_key_of_isRefl {s : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (hs : CFSG.StandardType.FrameRoute.FS81.IsRefl s) : ∃ k, keyOK k = true ∧ reflK k = s := by
  obtain ⟨v, f, hfv, rfl⟩ := hs
  have hv0 : encV v ≠ 0 := by
    intro h
    have : v = 0 := by rw [← decV_encV v, h]; funext j; simp [decV, dg_eq]
    rw [this, dotProduct_zero] at hfv
    exact absurd hfv (by decide)
  obtain ⟨k, hk, hc, hd, hr⟩ := key_of_pair (encV_lt v) (encV_lt f) hv0
  refine ⟨k, keyOK_iff.mpr ⟨hk, hc, ?_⟩, ?_⟩
  · rw [hd, dot_eq_one, decV_encV, decV_encV]
    exact hfv
  · rw [hr, decV_encV, decV_encV]

theorem isRefl_reflK {k : ℕ} (hk : keyOK k = true) :
    CFSG.StandardType.FrameRoute.FS81.IsRefl (reflK k) :=
  ⟨decV (k / 729), decV (k % 729), dot_eq_one.mp (keyOK_iff.mp hk).2.2, rfl⟩

end CFSG.KC.TwD5R
