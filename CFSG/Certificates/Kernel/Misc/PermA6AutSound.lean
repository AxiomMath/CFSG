module

public import Certificates.Data.Kernel.Misc.PermA6Aut
public import CFSG.Certificates.Kernel.Misc.PermClosSound
import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CFSG.KC.Misc.A6Aut

open CFSG.KC.Ord CFSG.KC.LQT CFSG.KC.Misc.Clos CFSG.KC.Misc.GH23

variable {H : Type*} [Group H] {enc : H → ℕ}

@[expose] def InvCases (f : H →* H) : Prop :=
  (∃ g : H, ¬(f g * g⁻¹) * (f g * g⁻¹) = 1 ∧
      (f g * g⁻¹) * (f g * g⁻¹) * ((f g * g⁻¹) * (f g * g⁻¹)) = 1) ∨
    (∃ a b g : H, a * a * a = 1 ∧ b * b * b = 1 ∧ a ≠ 1 ∧ a * b = b * a ∧ b ≠ 1 ∧ b ≠ a ∧
      b ≠ a * a ∧ ((f a = a * a ∧ f b = b) ∨ (f a = b ∧ f b = a)) ∧ f g * g⁻¹ ≠ 1 ∧
      (f g * g⁻¹) * (f g * g⁻¹) = 1)

theorem pow5_enc (henc : ClosEnc enc mul8 one8) (a : H) :
    pow5 (enc a) = enc (a * (a * (a * (a * a)))) := by
  rw [pow5, henc.enc_mul, henc.enc_mul, henc.enc_mul, henc.enc_mul]

theorem pathK_eq (henc : ClosEnc enc mul8 one8) {gx gy : H} (hx : xC = enc gx) (hy : yC = enc gy)
    {N : ℕ} {E PA : ℕ → ℕ} (ht : ∀ k < N, treeAt mul8 one8 genC 2 E PA k = true)
    (hex : ∀ k < N, ∃ g, enc g = E k) (f : H →* H) :
    ∀ fuel k, k < N → k ≤ fuel → ∀ e, enc e = E k →
      pathK PA (enc (f gx)) (enc (f gy)) fuel k = enc (f e) := by
  have hone : ∀ e, 0 < N → enc e = E 0 → e = 1 := fun e hN he => by
    have h0 : Nat.beq (E 0) one8 = true := ht 0 hN
    exact henc.inj (he.trans ((Nat.eq_of_beq_eq_true h0).trans henc.enc_one.symm))
  intro fuel
  induction fuel with
  | zero =>
    intro k hk hle e he
    obtain rfl : k = 0 := by omega
    rw [hone e hk he, map_one, henc.enc_one] <;> rfl
  | succ fuel ih =>
    intro k hk hle e he
    cases k with
    | zero =>
      rw [hone e hk he, map_one, henc.enc_one] <;> rfl
    | succ k =>
      have h : P.letB (PA (k + 1)) (fun r => P.letB (Nat.land r (nat_lit 16777215)) fun p =>
          P.letB (Nat.shiftRight r (nat_lit 24)) fun l => andB (Nat.blt p (k + 1))
            (andB (Nat.blt l 2) (Nat.beq (E (k + 1)) (mul8 (E p) (genC l))))) = true :=
        ht (k + 1) hk
      rw [P.letB_eq, P.letB_eq, P.letB_eq] at h
      obtain ⟨hp, h⟩ := P.andB_iff.1 h
      obtain ⟨hl, he'⟩ := P.andB_iff.1 h
      replace hp := P.blt_iff.1 hp
      replace hl := P.blt_iff.1 hl
      replace he' := P.beq_iff.1 he'
      have hstep : pathK PA (enc (f gx)) (enc (f gy)) (fuel + 1) (k + 1) =
          mul8 (pathK PA (enc (f gx)) (enc (f gy)) fuel (Nat.land (PA (k + 1)) (nat_lit 16777215)))
            (Bool.rec (motive := fun _ => ℕ) (enc (f gy)) (enc (f gx))
              (Nat.beq (Nat.shiftRight (PA (k + 1)) (nat_lit 24)) 0)) := rfl
      rw [hstep]
      generalize Nat.land (PA (k + 1)) (nat_lit 16777215) = p at hp he' ⊢
      generalize Nat.shiftRight (PA (k + 1)) (nat_lit 24) = l at hl he' ⊢
      obtain ⟨ep, hep⟩ := hex p (by omega)
      obtain ⟨gl, hgl, hgv⟩ : ∃ gl, genC l = enc gl ∧
          Bool.rec (motive := fun _ => ℕ) (enc (f gy)) (enc (f gx)) (Nat.beq l 0) = enc (f gl) := by
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨gx, hx, rfl⟩
        · exact ⟨gy, hy, rfl⟩
      have hee : e = ep * gl := henc.inj (by rw [he, he', henc.enc_mul, hep, hgl])
      rw [ih p (by omega) (by omega) ep hep, hgv, ← henc.enc_mul, ← map_mul, hee]

theorem witOK_sound (henc : ClosEnc enc mul8 one8) {N : ℕ} {E PA : ℕ → ℕ}
    (hex : ∀ k < N, ∃ g, enc g = E k) (f : H →* H) {u v w : ℕ}
    (hP : ∀ k < N, ∀ e, enc e = E k → pathK PA u v N k = enc (f e))
    (h : witOK N E PA u v w = true) : InvCases f := by
  simp only [witOK, P.letB_eq, P.andB_iff, P.blt_iff, P.beq_iff] at h
  obtain ⟨hig, hih, hgi, hord, hsyl⟩ := h
  obtain ⟨g, hg⟩ := hex _ hig
  obtain ⟨gi, hgi'⟩ := hex _ hih
  have hinv : gi = g⁻¹ := by
    rw [← hg, ← hgi', ← henc.enc_mul, ← henc.enc_one] at hgi
    exact eq_inv_of_mul_eq_one_right (henc.inj hgi)
  rw [hP _ hig g hg, ← hgi', hinv, ← henc.enc_mul] at hord
  generalize Nat.beq (Nat.land w 1) 0 = b at hord hsyl
  cases b with
  | true =>
    left
    simp only [ordOK, P.letB_eq, P.andB_iff, P.notB_iff, P.beq_iff, ← henc.enc_mul,
      ← henc.enc_one, henc.inj.eq_iff] at hord
    exact ⟨g, hord⟩
  | false =>
    right
    simp only [ordOK, P.andB_iff, P.notB_iff, P.beq_iff, ← henc.enc_mul, ← henc.enc_one,
      henc.inj.eq_iff] at hord
    simp only [P.letB_eq, P.andB_iff, P.blt_iff] at hsyl
    obtain ⟨hia, hib, hs⟩ := hsyl
    obtain ⟨a, ha⟩ := hex _ hia
    obtain ⟨b, hb⟩ := hex _ hib
    rw [hP _ hia a ha, hP _ hib b hb, ← ha, ← hb] at hs
    simp only [sylOK, P.andB_iff, P.orB_iff, P.notB_iff, P.beq_iff, ← henc.enc_mul,
      ← henc.enc_one, henc.inj.eq_iff] at hs
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hs
    exact ⟨a, b, g, h1, h2, h3, h4, h5, h6, h7, h8, hord⟩

theorem pairOK_sound (henc : ClosEnc enc mul8 one8) {gx gy : H} (hx : xC = enc gx)
    (hy : yC = enc gy) {N : ℕ} {E PA : ℕ → ℕ} (ht : ∀ k < N, treeAt mul8 one8 genC 2 E PA k = true)
    (hex : ∀ k < N, ∃ g, enc g = E k) (f : H →* H)
    (h5 : gx * gy * (gx * gy * (gx * gy * (gx * gy * (gx * gy)))) = 1)
    (h5' : gx * (gy * gy) * (gx * (gy * gy) * (gx * (gy * gy) * (gx * (gy * gy) *
      (gx * (gy * gy))))) = 1)
    (hffx : f (f gx) = gx) (hffy : f (f gy) = gy) (hne : ¬(f gx = gx ∧ f gy = gy))
    {iu iv w : ℕ} (hiu : iu < N) (hiv : iv < N) (heu : E iu = enc (f gx))
    (hev : E iv = enc (f gy)) (h : pairOK N E PA iu iv w = true) : InvCases f := by
  have hP := pathK_eq henc hx hy ht hex f N
  simp only [pairOK, P.letB_eq, P.impB_iff, P.andB_iff, P.orB_iff, P.beq_iff, heu, hev] at h
  have e5 := congrArg f h5
  have e5' := congrArg f h5'
  simp only [map_mul, map_one] at e5 e5'
  have hr1 : pow5 (mul8 (enc (f gx)) (enc (f gy))) = one8 := by
    rw [← henc.enc_mul, pow5_enc henc, e5, henc.enc_one]
  have hr2 : pow5 (mul8 (enc (f gx)) (mul8 (enc (f gy)) (enc (f gy)))) = one8 := by
    rw [← henc.enc_mul, ← henc.enc_mul, pow5_enc henc, e5', henc.enc_one]
  have hpu : pathK PA (enc (f gx)) (enc (f gy)) N iu = xC := by
    rw [hP iu hiu hiu.le (f gx) heu.symm, hffx, hx]
  have hpv : pathK PA (enc (f gx)) (enc (f gy)) N iv = yC := by
    rw [hP iv hiv hiv.le (f gy) hev.symm, hffy, hy]
  rcases h ⟨hr1, hr2⟩ ⟨hpu, hpv⟩ with ⟨h1, h2⟩ | hw
  · exact absurd ⟨henc.inj (h1.trans hx), henc.inj (h2.trans hy)⟩ hne
  · exact witOK_sound henc hex f (fun k hk e he => hP k hk hk.le e he) hw

end CFSG.KC.Misc.A6Aut

end
