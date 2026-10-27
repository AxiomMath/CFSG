module

public import Certificates.Data.Kernel.LyOmega.Cent
import all CFSG.Certificates.Kernel.LyOmega.SoundB5
import all CFSG.Certificates.Kernel.Spor.OrdSound
public import CFSG.Certificates.Kernel.LyOmega.Defs

public section

namespace CFSG.KS.LyOm

open CFSG.KC.LyOm CFSG.KC.Ord CFSG.KC.LL CFSG.KC.Loop

namespace CentPf

open CFSG.KS.Ord CFSG.KS.LyOm.SB5

private theorem bAnd2 {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> simp_all

private theorem bIf2 {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    (c = true → t = true) ∧ (c = false → e = true) := by
  cases c <;> simp_all

private theorem quad_key {C : SConsts} (hC : sConstsOK C = true) {a b c : ℕ} {x y : ℕ → ℕ}
    (ha : a < 5) (hb : b < 5) (hc : c < 5) (hx : ∀ t < 7 * 7, x t < 5) (hy : ∀ t < 7 * 7, y t < 5) :
    LCanon 11 7 7 (redP 11 C.L7 C.H7 5 7
        (a * pk 11 (7 * 7) y + (b * pk 11 (7 * 7) x + c * C.ONE))) ∧
      smM (redP 11 C.L7 C.H7 5 7 (a * pk 11 (7 * 7) y + (b * pk 11 (7 * 7) x + c * C.ONE))) =
        (a : ZMod 5) • smM (pk 11 (7 * 7) y) + (b : ZMod 5) • smM (pk 11 (7 * 7) x) +
          (c : ZMod 5) • 1 := by
  obtain ⟨-, -, -, -, -, -, hL, hH, -, -, hONE⟩ := consts_facts (sc_consts hC)
  have hx' : ∀ t < 7 * 7, x t < 2 ^ 11 := fun t ht => Nat.lt_of_lt_of_le (hx t ht) (by norm_num)
  have hy' : ∀ t < 7 * 7, y t < 2 ^ 11 := fun t ht => Nat.lt_of_lt_of_le (hy t ht) (by norm_num)
  have hδ : ∀ t < 7 * 7, (if t / 7 = t % 7 then 1 else 0) < 2 ^ 11 := fun t _ => by split <;> norm_num
  have hone : ∀ i j : Fin 7, (1 : Matrix (Fin 7) (Fin 7) (ZMod 5)) i j =
      (((if (7 * i.val + j.val) / 7 = (7 * i.val + j.val) % 7 then 1 else 0 : ℕ)) : ZMod 5) := by
    intro i j
    rw [← (one_fact hC).2, smM_eq, hONE]
    exact ordMat77_pk hδ i j
  set f : ℕ → ℕ := fun t => y t * a + (x t * b + (if t / 7 = t % 7 then 1 else 0) * c) with hfdef
  have e : a * pk 11 (7 * 7) y + (b * pk 11 (7 * 7) x + c * C.ONE) = pk 11 (7 * 7) f := by
    rw [hONE, Nat.mul_comm a, Nat.mul_comm b, Nat.mul_comm c, pk_mul, pk_mul, pk_mul, pk_add, pk_add]
  have hfb : ∀ t < 7 * 7, f t ≤ 36 := by
    intro t ht
    have h1 := hx t ht
    have h2 := hy t ht
    have h3 : y t * a ≤ 4 * 4 := Nat.mul_le_mul (by omega : y t ≤ 4) (by omega : a ≤ 4)
    have h4 : x t * b ≤ 4 * 4 := Nat.mul_le_mul (by omega : x t ≤ 4) (by omega : b ≤ 4)
    have h5 : (if t / 7 = t % 7 then 1 else 0) * c ≤ 4 := by split <;> omega
    simp only [hfdef]
    omega
  have hf : ∀ t < 7 * 7, f t < 2 ^ (11 - 1) := fun t ht => by have := hfb t ht; norm_num; omega
  have hf2 : ∀ t < 7 * 7, f t < 5 * 2 ^ (7 + 1) := fun t ht => by have := hfb t ht; norm_num; omega
  have hr : redP 11 C.L7 C.H7 5 7 (a * pk 11 (7 * 7) y + (b * pk 11 (7 * 7) x + c * C.ONE)) =
      pk 11 (7 * 7) (fun t => f t % 5) := by
    rw [e, hL, hH]
    exact redP_pk (by norm_num) (by norm_num) hf hf2
  have hg : ∀ t < 7 * 7, f t % 5 < 5 := fun t _ => Nat.mod_lt _ (by norm_num)
  rw [hr]
  refine ⟨lcanon_iff.2 (canon_pk hg (by norm_num)), ?_⟩
  funext i j
  simp only [smM_eq]
  rw [ordMat77_pk (fun t ht => Nat.lt_of_lt_of_le (hg t ht) (by norm_num)),
    Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.smul_apply,
    hone, ordMat77_pk hx', ordMat77_pk hy', ZMod.natCast_mod]
  simp only [hfdef, smul_eq_mul]
  push_cast
  ring

private theorem sVld' {C : SConsts} (hC : sConstsOK C = true) {X : ℕ} (h : sVld C X = true) :
    LCanon 11 7 7 X :=
  lcanon_iff.2 (validM_canon (sc_consts hC) (d := 7) (S := 77) h)

private theorem sQuad' {C : SConsts} (hC : sConstsOK C = true) {a b c X : ℕ} (ha : a < 5) (hb : b < 5)
    (hc : c < 5) (hX : LCanon 11 7 7 X) :
    LCanon 11 7 7 (sQuad C a b c X) ∧
      smM (sQuad C a b c X) = (a : ZMod 5) • smM X ^ 2 + (b : ZMod 5) • smM X + (c : ZMod 5) • 1 := by
  have h2 := sMul_fact hC hX hX
  obtain ⟨x, hXx, hx⟩ := canon_decomp (by norm_num : 0 < 11) (lcanon_iff.1 hX)
  obtain ⟨y, hYy, hy⟩ := canon_decomp (by norm_num : 0 < 11) (lcanon_iff.1 h2.1)
  have key := quad_key hC ha hb hc hx hy
  rw [← hXx, ← hYy, h2.2] at key
  rw [sq]
  exact key

private theorem sConjTree' {C : SConsts} (hC : sConstsOK C = true) {G Z P L : ℕ → ℕ} {Y m n : ℕ}
    (hG : ∀ s < m, LCanon 11 7 7 (G s)) (h : sConjTree C G Z P L Y m n = true) :
    Z 0 = Y ∧ (∀ k < n, LCanon 11 7 7 (Z k)) ∧
      (∀ k, 0 < k → k < n → P k < k ∧ L k < m ∧
        smM (G (L k)) * smM (Z (P k)) = smM (Z k) * smM (G (L k))) ∧
      (∀ i < n, ∀ j < n, Z i = Z j → i = j) := by
  unfold sConjTree at h
  obtain ⟨h0, h⟩ := bAnd2 h
  obtain ⟨h1, h2⟩ := bAnd2 h
  have H1 := (allBelow_iff (Nat.le_mul_of_pos_left n (by norm_num))).1 h1
  have hm2 : n * n ≤ 64 * Nat.succ (Nat.shiftRight (n * n) 6) := by
    change n * n ≤ 64 * ((n * n) >>> 6 + 1)
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have H2 := (allBelow_iff hm2).1 h2
  have hZ : ∀ k < n, LCanon 11 7 7 (Z k) := fun k hk => sVld' hC (bAnd2 (H1 k hk)).1
  refine ⟨beq_iff.1 h0, hZ, fun k hk0 hkn => ?_, fun i hi j hj hij => ?_⟩
  · have hk := (bIf2 (bAnd2 (H1 k hkn)).2).2 (by
      cases hb : Nat.beq k 0
      · rfl
      · exact absurd (beq_iff.1 hb) (by omega))
    obtain ⟨hP, hk⟩ := bAnd2 hk
    obtain ⟨hL, hk⟩ := bAnd2 hk
    have hP' := blt_iff.1 hP
    have hL' := blt_iff.1 hL
    have hGL := hG _ hL'
    have hZP := hZ (P k) (by omega)
    have e1 := sMul_fact hC hGL hZP
    have e2 := sMul_fact hC (hZ k hkn) hGL
    refine ⟨hP', hL', ?_⟩
    rw [← e1.2, ← e2.2, beq_iff.1 hk]
  · have key : ∀ i < n, ∀ j < n, i < j → Z i ≠ Z j := by
      intro i hi j hj hlt heq
      have ht : n * i + j < n * n := by nlinarith
      have hb := H2 _ ht
      have hd : (n * i + j) / n = i := by
        rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
      have hmd : (n * i + j) % n = j := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
      simp only [Nat.div_eq, Nat.mod_eq] at hb
      change Bool.rec (motive := fun _ => Bool) true
        (Bool.rec (motive := fun _ => Bool) true false (Nat.beq (Z ((n * i + j) / n)) (Z ((n * i + j) % n))))
        (Nat.blt ((n * i + j) / n) ((n * i + j) % n)) = true at hb
      rw [hd, hmd, blt_iff.2 hlt, beq_iff.2 heq] at hb
      exact Bool.false_ne_true hb
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact absurd hij (key i hi j hj hlt)
    · exact heq
    · exact absurd hij.symm (key j hj i hi hgt)

end CentPf

theorem sVld_sound {C : SConsts} (hC : sConstsOK C = true) {X : ℕ} (h : sVld C X = true) :
    LCanon 11 7 7 X :=
  CentPf.sVld' hC h

theorem sQuad_sound {C : SConsts} (hC : sConstsOK C = true) {a b c X : ℕ} (ha : a < 5) (hb : b < 5)
    (hc : c < 5) (hX : LCanon 11 7 7 X) :
    LCanon 11 7 7 (sQuad C a b c X) ∧
      smM (sQuad C a b c X) = (a : ZMod 5) • smM X ^ 2 + (b : ZMod 5) • smM X + (c : ZMod 5) • 1 :=
  CentPf.sQuad' hC ha hb hc hX

theorem sConjTree_sound {C : SConsts} (hC : sConstsOK C = true) {G Z P L : ℕ → ℕ} {Y m n : ℕ}
    (hG : ∀ s < m, LCanon 11 7 7 (G s)) (h : sConjTree C G Z P L Y m n = true) :
    Z 0 = Y ∧ (∀ k < n, LCanon 11 7 7 (Z k)) ∧
      (∀ k, 0 < k → k < n → P k < k ∧ L k < m ∧
        smM (G (L k)) * smM (Z (P k)) = smM (Z k) * smM (G (L k))) ∧
      (∀ i < n, ∀ j < n, Z i = Z j → i = j) :=
  CentPf.sConjTree' hC hG h

end CFSG.KS.LyOm

end
