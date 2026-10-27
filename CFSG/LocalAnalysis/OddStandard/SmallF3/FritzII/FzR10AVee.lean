module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10ASet

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzR10A

variable {G : Type} [Group G] {t tau lam rho : G} {Z E W Q R T P : Subgroup G} {a b : G}

@[expose] def fzrAV (t tau lam : G) (v : ℕ) : G :=
  t ^ (v % 2) * tau ^ (v / 2 % 2) * lam ^ (v / 4 % 2)

theorem fzr_a_V_zero : fzrAV t tau lam 0 = 1 := by
  simp [fzrAV]

theorem fzr_a_V_one : fzrAV t tau lam 1 = t := by
  simp [fzrAV]

theorem fzr_a_V_two : fzrAV t tau lam 2 = tau := by
  simp [fzrAV]

private lemma fzrAux_three {a b c : G} (hab : a * b = b * a) (hac : a * c = c * a)
    (hbc : b * c = c * b) (p q r p' q' r' : ℕ) :
    a ^ p * b ^ q * c ^ r * (a ^ p' * b ^ q' * c ^ r') =
      a ^ (p + p') * b ^ (q + q') * c ^ (r + r') := by
  have hab' : Commute a b := hab
  have hac' : Commute a c := hac
  have hbc' : Commute b c := hbc
  have hca : c ^ r * a ^ p' = a ^ p' * c ^ r := ((hac'.symm.pow_left r).pow_right p').eq
  have hcb : c ^ r * b ^ q' = b ^ q' * c ^ r := ((hbc'.symm.pow_left r).pow_right q').eq
  have hba : b ^ q * a ^ p' = a ^ p' * b ^ q := ((hab'.symm.pow_left q).pow_right p').eq
  calc
    a ^ p * b ^ q * c ^ r * (a ^ p' * b ^ q' * c ^ r')
        = a ^ p * b ^ q * (c ^ r * a ^ p') * b ^ q' * c ^ r' := by group
    _ = a ^ p * b ^ q * (a ^ p' * c ^ r) * b ^ q' * c ^ r' := by rw [hca]
    _ = a ^ p * b ^ q * a ^ p' * c ^ r * b ^ q' * c ^ r' := by group
    _ = a ^ p * b ^ q * a ^ p' * (c ^ r * b ^ q') * c ^ r' := by group
    _ = a ^ p * b ^ q * a ^ p' * (b ^ q' * c ^ r) * c ^ r' := by rw [hcb]
    _ = a ^ p * (b ^ q * a ^ p') * b ^ q' * c ^ r * c ^ r' := by group
    _ = a ^ p * (a ^ p' * b ^ q) * b ^ q' * c ^ r * c ^ r' := by rw [hba]
    _ = a ^ p * a ^ p' * (b ^ q * b ^ q') * (c ^ r * c ^ r') := by group
    _ = a ^ (p + p') * b ^ (q + q') * c ^ (r + r') := by
      rw [← pow_add a p p', ← pow_add b q q', ← pow_add c r r']

private lemma fzrAux_xor_bits (v w : ℕ) (hv : v < 8) (hw : w < 8) :
    (v % 2 + w % 2) % 2 = (v ^^^ w) % 2 ∧
      (v / 2 % 2 + w / 2 % 2) % 2 = (v ^^^ w) / 2 % 2 ∧
      (v / 4 % 2 + w / 4 % 2) % 2 = (v ^^^ w) / 4 % 2 := by
  interval_cases v <;> interval_cases w <;> decide

private lemma fzrAux_ap_lt (m : Mat) (n : ℕ) : m.ap n < 64 := by
  have h1 := Nat.mod_lt (m.a * (n % 8) + m.b * (n / 8 % 8)) (by norm_num : 0 < 8)
  have h2 := Nat.mod_lt (m.c * (n % 8) + m.d * (n / 8 % 8)) (by norm_num : 0 < 8)
  unfold Mat.ap
  omega

private lemma fzrAux_pow_mod_two (s : G) (hs : s ^ 2 = 1) (n : ℕ) : s ^ n = s ^ (n % 2) :=
  pow_eq_pow_mod (a := s) (n := 2) (m := n) hs

theorem fzr_a_V_mul (ht : t * t = 1) (htau : tau * tau = 1) (hlam : lam * lam = 1)
    (httau : t * tau = tau * t) (htlam : t * lam = lam * t) (htaulam : tau * lam = lam * tau)
    {v w : ℕ} (hv : v < 8) (hw : w < 8) :
    fzrAV t tau lam v * fzrAV t tau lam w = fzrAV t tau lam (v ^^^ w) := by
  have ht2 : t ^ 2 = 1 := by simpa [pow_two] using ht
  have hs2 : tau ^ 2 = 1 := by simpa [pow_two] using htau
  have hl2 : lam ^ 2 = 1 := by simpa [pow_two] using hlam
  obtain ⟨hb0, hb1, hb2⟩ := fzrAux_xor_bits v w hv hw
  unfold fzrAV
  rw [fzrAux_three (a := t) (b := tau) (c := lam) httau htlam htaulam
    (v % 2) (v / 2 % 2) (v / 4 % 2) (w % 2) (w / 2 % 2) (w / 4 % 2)]
  rw [fzrAux_pow_mod_two t ht2 (v % 2 + w % 2),
    fzrAux_pow_mod_two tau hs2 (v / 2 % 2 + w / 2 % 2),
    fzrAux_pow_mod_two lam hl2 (v / 4 % 2 + w / 4 % 2)]
  rw [hb0, hb1, hb2]

private lemma fzrAux_step {a b s : G} {M : Mat} (hact : FzR10AAct a b s M) {e n : ℕ}
    (he : e = 0 ∨ e = 1) (hn : n < 64) :
    s ^ e * fzrAElt a b n * (s ^ e)⁻¹ =
      fzrAElt a b (if e == 1 then M.ap n else n) := by
  rcases he with rfl | rfl
  · simp
  · simpa using hact n hn

private lemma fzrAux_conj_split (A B C X : G) :
    (A * B * C) * X * (A * B * C)⁻¹ = A * (B * (C * X * C⁻¹) * B⁻¹) * A⁻¹ := by
  group

private lemma fzrAux_vAct_eq (Mt Ms Ml : Mat) (v q : ℕ) :
    vAct Mt Ms Ml v q =
      if v % 2 == 1 then
        Mt.ap (if v / 2 % 2 == 1 then
          Ms.ap (if v / 4 % 2 == 1 then Ml.ap q else q)
          else (if v / 4 % 2 == 1 then Ml.ap q else q))
      else
        (if v / 2 % 2 == 1 then
          Ms.ap (if v / 4 % 2 == 1 then Ml.ap q else q)
          else (if v / 4 % 2 == 1 then Ml.ap q else q)) := by
  unfold vAct
  rfl

theorem fzr_a_V_conj {Mt Ms Ml : Mat} (hM : FzR10AMats t tau lam a b Mt Ms Ml) {v q : ℕ}
    (hq : q < 64) :
    fzrAV t tau lam v * fzrAElt a b q * (fzrAV t tau lam v)⁻¹ =
      fzrAElt a b (vAct Mt Ms Ml v q) := by
  have hq1 : (if (v / 4 % 2 == 1) = true then Ml.ap q else q) < 64 := by
    by_cases h : (v / 4 % 2 == 1) = true
    · rw [if_pos h]; exact fzrAux_ap_lt Ml q
    · rw [if_neg h]; exact hq
  have hq2 : (if (v / 2 % 2 == 1) = true then
        Ms.ap (if (v / 4 % 2 == 1) = true then Ml.ap q else q)
        else (if (v / 4 % 2 == 1) = true then Ml.ap q else q)) < 64 := by
    by_cases h : (v / 2 % 2 == 1) = true
    · rw [if_pos h]; exact fzrAux_ap_lt Ms _
    · rw [if_neg h]; exact hq1
  have hstep_l : lam ^ (v / 4 % 2) * fzrAElt a b q * (lam ^ (v / 4 % 2))⁻¹ =
      fzrAElt a b (if v / 4 % 2 == 1 then Ml.ap q else q) :=
    fzrAux_step hM.act_l (e := v / 4 % 2) (n := q) (Nat.mod_two_eq_zero_or_one _) hq
  have hstep_s : tau ^ (v / 2 % 2)
        * fzrAElt a b (if v / 4 % 2 == 1 then Ml.ap q else q)
        * (tau ^ (v / 2 % 2))⁻¹ =
      fzrAElt a b (if v / 2 % 2 == 1 then
        Ms.ap (if v / 4 % 2 == 1 then Ml.ap q else q)
        else (if v / 4 % 2 == 1 then Ml.ap q else q)) :=
    fzrAux_step hM.act_s (e := v / 2 % 2) (n := if v / 4 % 2 == 1 then Ml.ap q else q)
      (Nat.mod_two_eq_zero_or_one _) hq1
  have hstep_t : t ^ (v % 2)
        * fzrAElt a b (if v / 2 % 2 == 1 then
          Ms.ap (if v / 4 % 2 == 1 then Ml.ap q else q)
          else (if v / 4 % 2 == 1 then Ml.ap q else q))
        * (t ^ (v % 2))⁻¹ =
      fzrAElt a b (if v % 2 == 1 then
        Mt.ap (if v / 2 % 2 == 1 then
          Ms.ap (if v / 4 % 2 == 1 then Ml.ap q else q)
          else (if v / 4 % 2 == 1 then Ml.ap q else q))
        else (if v / 2 % 2 == 1 then
          Ms.ap (if v / 4 % 2 == 1 then Ml.ap q else q)
          else (if v / 4 % 2 == 1 then Ml.ap q else q))) :=
    fzrAux_step hM.act_t (e := v % 2) (n := if v / 2 % 2 == 1 then
        Ms.ap (if v / 4 % 2 == 1 then Ml.ap q else q)
        else (if v / 4 % 2 == 1 then Ml.ap q else q))
      (Nat.mod_two_eq_zero_or_one _) hq2
  have hsplit : fzrAV t tau lam v * fzrAElt a b q * (fzrAV t tau lam v)⁻¹ =
      t ^ (v % 2) * (tau ^ (v / 2 % 2) * (lam ^ (v / 4 % 2) * fzrAElt a b q
        * (lam ^ (v / 4 % 2))⁻¹) * (tau ^ (v / 2 % 2))⁻¹) * (t ^ (v % 2))⁻¹ :=
    fzrAux_conj_split (t ^ (v % 2)) (tau ^ (v / 2 % 2)) (lam ^ (v / 4 % 2))
      (fzrAElt a b q)
  rw [hsplit, hstep_l, hstep_s, hstep_t, fzrAux_vAct_eq]

private lemma fzrAux_lam_notin_R (S : FzR10ASet t tau lam rho Z E W Q R T P a b) :
    lam ∉ R := by
  intro hlamR
  obtain ⟨z, hzZ, hz⟩ := S.str.lam_Z
  exact hz (S.str.R_Z lam hlamR z hzZ)

private lemma fzrAux_mul_mem_cancel {H : Subgroup G} {x y : G} (hx : x ∈ H)
    (hxy : x * y ∈ H) : y ∈ H := by
  have h := H.mul_mem (H.inv_mem hx) hxy
  rwa [show x⁻¹ * (x * y) = y by group] at h

theorem fzr_a_V_mem_P (S : FzR10ASet t tau lam rho Z E W Q R T P a b) (htP : t ∉ P) {u : ℕ}
    (hu : u < 8) (h : fzrAV t tau lam u ∈ P) : u = 0 := by
  interval_cases u
  · rfl
  · exfalso
    exact htP (by simpa [fzrAV] using h)
  · exfalso
    exact S.str.tau_notin_Q (S.pf.PQ (by simpa [fzrAV] using h))
  · exfalso
    have htQ : t ∈ Q := S.str.WQ S.str.t_mem
    have hmem : t * tau ∈ Q := S.pf.PQ (by simpa [fzrAV] using h)
    exact S.str.tau_notin_Q (fzrAux_mul_mem_cancel htQ hmem)
  · exfalso
    exact fzrAux_lam_notin_R S (S.str.QR (S.pf.PQ (by simpa [fzrAV] using h)))
  · exfalso
    have htR : t ∈ R := S.str.QR (S.str.WQ S.str.t_mem)
    have hmem : t * lam ∈ R := S.str.QR (S.pf.PQ (by simpa [fzrAV] using h))
    exact fzrAux_lam_notin_R S (fzrAux_mul_mem_cancel htR hmem)
  · exfalso
    have hmem : tau * lam ∈ R := S.str.QR (S.pf.PQ (by simpa [fzrAV] using h))
    exact fzrAux_lam_notin_R S (fzrAux_mul_mem_cancel S.str.tau_R hmem)
  · exfalso
    have htR : t ∈ R := S.str.QR (S.str.WQ S.str.t_mem)
    have httauR : t * tau ∈ R := R.mul_mem htR S.str.tau_R
    have hmem : t * tau * lam ∈ R := S.str.QR (S.pf.PQ (by simpa [fzrAV] using h))
    exact fzrAux_lam_notin_R S (fzrAux_mul_mem_cancel httauR hmem)

end CFSG.OddStandard.SmallF3.FritzII
