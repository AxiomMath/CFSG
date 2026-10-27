module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10AVee
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10AElt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10AMat

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzR10A

variable {G : Type} [Group G] {t tau lam rho : G} {Z E W Q R T P : Subgroup G} {a b : G}
  {Mt Ms Ml : Mat}

@[expose] def fzrAMu (a b t tau lam : G) (n : ℕ) : G :=
  fzrAElt a b (n % 64) * fzrAV t tau lam (n / 64 % 8)

private theorem fzrAux_V_hyps (S : FzR10ASet t tau lam rho Z E W Q R T P a b) :
    t * t = 1 ∧ tau * tau = 1 ∧ lam * lam = 1 ∧
      t * tau = tau * t ∧ t * lam = lam * t ∧ tau * lam = lam * tau := by
  have htt : t * t = 1 := by simpa [pow_two] using S.str.t_sq
  have hss : tau * tau = 1 := by simpa [pow_two] using S.pf.tau_sq1
  have hll : lam * lam = 1 := by simpa [pow_two] using S.str.lam_sq
  have hts : t * tau = tau * t := by
    have h : tau * t * tau⁻¹ = t := S.str.tau_t
    calc t * tau = (tau * t * tau⁻¹) * tau := by rw [h]
      _ = tau * t := by group
  have htl : t * lam = lam * t := by
    have h : lam * t * lam⁻¹ = t := S.str.lam_t
    calc t * lam = (lam * t * lam⁻¹) * lam := by rw [h]
      _ = lam * t := by group
  exact ⟨htt, hss, hll, hts, htl, S.str.tau_lam⟩

private theorem fzrAux_V_mem (S : FzR10ASet t tau lam rho Z E W Q R T P a b) (v : ℕ) :
    fzrAV t tau lam v ∈ T := by
  have htT : t ∈ T := S.str.RT (S.str.QR (S.str.WQ S.str.t_mem))
  have htauT : tau ∈ T := S.str.RT S.str.tau_R
  have hlamT : lam ∈ T := S.str.lam_T
  unfold fzrAV
  exact T.mul_mem (T.mul_mem (T.pow_mem htT _) (T.pow_mem htauT _)) (T.pow_mem hlamT _)

private theorem fzrAux_vAct_lt (Mt Ms Ml : Mat) {v q : ℕ} (hq : q < 64) :
    vAct Mt Ms Ml v q < 64 := by
  unfold vAct
  split_ifs <;> first | exact fzr_a_ap_lt _ _ | exact hq

private theorem fzrAux_xor_lt_eight {v w : ℕ} (hv : v < 8) (hw : w < 8) : v ^^^ w < 8 := by
  simpa using Nat.xor_lt_two_pow (n := 3) hv hw

theorem fzr_a_emA_lt (Mt Ms Ml : Mat) {x y : ℕ} (hx : x < 512) (hy : y < 512) :
    emA Mt Ms Ml x y < 512 := by
  have h1 : addP (x % 64) (vAct Mt Ms Ml (x / 64 % 8) (y % 64)) < 64 := fzr_a_addP_lt _ _
  have h2 : x / 64 % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have h3 : y / 64 % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have h4 : (x / 64 % 8) ^^^ (y / 64 % 8) < 8 := fzrAux_xor_lt_eight h2 h3
  rw [show emA Mt Ms Ml x y = addP (x % 64) (vAct Mt Ms Ml (x / 64 % 8) (y % 64))
      + 64 * ((x / 64 % 8) ^^^ (y / 64 % 8)) from rfl]
  omega

theorem fzrAMu_zero : fzrAMu a b t tau lam 0 = 1 := by
  simp [fzrAMu, fzr_a_elt_zero, fzr_a_V_zero]

theorem fzrAMu_tI : fzrAMu a b t tau lam 64 = t := by
  simp [fzrAMu, fzr_a_elt_zero, fzr_a_V_one]

theorem fzrAMu_sI : fzrAMu a b t tau lam 128 = tau := by
  simp [fzrAMu, fzr_a_elt_zero, fzr_a_V_two]

theorem fzrAMu_mem (S : FzR10ASet t tau lam rho Z E W Q R T P a b) (n : ℕ) :
    fzrAMu a b t tau lam n ∈ T := by
  have hPT : P ≤ T := S.pf.PQ.trans (S.str.QR.trans S.str.RT)
  unfold fzrAMu
  exact T.mul_mem (hPT (fzr_a_elt_mem S.basis (n % 64))) (fzrAux_V_mem S (n / 64 % 8))

private theorem fzrAux_mu_mul (S : FzR10ASet t tau lam rho Z E W Q R T P a b)
    (hM : FzR10AMats t tau lam a b Mt Ms Ml) {p v q w : ℕ}
    (hp : p < 64) (hv : v < 8) (hq : q < 64) (hw : w < 8) :
    fzrAMu a b t tau lam (addP p (vAct Mt Ms Ml v q) + 64 * (v ^^^ w)) =
      (fzrAElt a b p * fzrAV t tau lam v) * (fzrAElt a b q * fzrAV t tau lam w) := by
  obtain ⟨htt, hss, hll, hts, htl, hsl⟩ := fzrAux_V_hyps S
  set c : ℕ := vAct Mt Ms Ml v q with hc
  set A : ℕ := addP p c with hA
  set B : ℕ := v ^^^ w with hB
  have hc_lt : c < 64 := by rw [hc]; exact fzrAux_vAct_lt Mt Ms Ml hq
  have hA_lt : A < 64 := by rw [hA]; exact fzr_a_addP_lt p c
  have hB_lt : B < 8 := by rw [hB]; exact fzrAux_xor_lt_eight hv hw
  have hmod : (A + 64 * B) % 64 = A := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hA_lt]
  have hdiv : (A + 64 * B) / 64 % 8 = B := by
    rw [Nat.add_mul_div_left A B (by norm_num : (0 : ℕ) < 64), Nat.div_eq_of_lt hA_lt,
      Nat.zero_add, Nat.mod_eq_of_lt hB_lt]
  have hEA : fzrAElt a b A = fzrAElt a b p * fzrAElt a b c :=
    (fzr_a_elt_mul S.basis hp hc_lt).symm
  have hconj : fzrAV t tau lam v * fzrAElt a b q * (fzrAV t tau lam v)⁻¹ = fzrAElt a b c :=
    fzr_a_V_conj hM hq
  have hVw : fzrAV t tau lam v * fzrAV t tau lam w = fzrAV t tau lam B :=
    fzr_a_V_mul htt hss hll hts htl hsl hv hw
  have hgroup : fzrAV t tau lam v * fzrAElt a b q * fzrAV t tau lam w
      = fzrAElt a b c * fzrAV t tau lam B := by
    have h1 : fzrAV t tau lam v * fzrAElt a b q * fzrAV t tau lam w
        = (fzrAV t tau lam v * fzrAElt a b q * (fzrAV t tau lam v)⁻¹)
          * (fzrAV t tau lam v * fzrAV t tau lam w) := by group
    rw [h1, hconj, hVw]
  unfold fzrAMu
  rw [hmod, hdiv, hEA]
  calc fzrAElt a b p * fzrAElt a b c * fzrAV t tau lam B
      = fzrAElt a b p * (fzrAElt a b c * fzrAV t tau lam B) := by group
    _ = fzrAElt a b p * (fzrAV t tau lam v * fzrAElt a b q * fzrAV t tau lam w) := by
          rw [← hgroup]
    _ = (fzrAElt a b p * fzrAV t tau lam v) * (fzrAElt a b q * fzrAV t tau lam w) := by group

theorem fzrAMu_mul (S : FzR10ASet t tau lam rho Z E W Q R T P a b)
    (hM : FzR10AMats t tau lam a b Mt Ms Ml) {n m : ℕ} (hn : n < 512) (hm : m < 512) :
    fzrAMu a b t tau lam (emA Mt Ms Ml n m) = fzrAMu a b t tau lam n * fzrAMu a b t tau lam m := by
  have hemA : emA Mt Ms Ml n m = addP (n % 64) (vAct Mt Ms Ml (n / 64 % 8) (m % 64))
      + 64 * ((n / 64 % 8) ^^^ (m / 64 % 8)) := rfl
  rw [hemA]
  exact fzrAux_mu_mul S hM (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))

theorem fzrAMu_inj (S : FzR10ASet t tau lam rho Z E W Q R T P a b) (htP : t ∉ P)
    {n m : ℕ} (hn : n < 512) (hm : m < 512)
    (h : fzrAMu a b t tau lam n = fzrAMu a b t tau lam m) : n = m := by
  obtain ⟨htt, hss, hll, hts, htl, hsl⟩ := fzrAux_V_hyps S
  have hp : n % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hq : m % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hv : n / 64 % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hw : m / 64 % 8 < 8 := Nat.mod_lt _ (by norm_num)
  unfold fzrAMu at h
  have hmem : fzrAV t tau lam (n / 64 % 8) * (fzrAV t tau lam (m / 64 % 8))⁻¹
      = (fzrAElt a b (n % 64))⁻¹ * fzrAElt a b (m % 64) := by
    calc fzrAV t tau lam (n / 64 % 8) * (fzrAV t tau lam (m / 64 % 8))⁻¹
        = (fzrAElt a b (n % 64))⁻¹ * (fzrAElt a b (n % 64) * fzrAV t tau lam (n / 64 % 8))
            * (fzrAV t tau lam (m / 64 % 8))⁻¹ := by group
      _ = (fzrAElt a b (n % 64))⁻¹ * (fzrAElt a b (m % 64) * fzrAV t tau lam (m / 64 % 8))
            * (fzrAV t tau lam (m / 64 % 8))⁻¹ := by rw [h]
      _ = (fzrAElt a b (n % 64))⁻¹ * fzrAElt a b (m % 64) := by group
  have hVP : fzrAV t tau lam (n / 64 % 8) * (fzrAV t tau lam (m / 64 % 8))⁻¹ ∈ P := by
    rw [hmem]
    exact P.mul_mem (P.inv_mem (fzr_a_elt_mem S.basis _)) (fzr_a_elt_mem S.basis _)
  have hw2 : fzrAV t tau lam (m / 64 % 8) * fzrAV t tau lam (m / 64 % 8) = 1 := by
    rw [fzr_a_V_mul htt hss hll hts htl hsl hw hw, Nat.xor_self, fzr_a_V_zero]
  have hwinv : (fzrAV t tau lam (m / 64 % 8))⁻¹ = fzrAV t tau lam (m / 64 % 8) :=
    inv_eq_of_mul_eq_one_right hw2
  have hVmm : fzrAV t tau lam (n / 64 % 8) * fzrAV t tau lam (m / 64 % 8)
      = fzrAV t tau lam ((n / 64 % 8) ^^^ (m / 64 % 8)) :=
    fzr_a_V_mul htt hss hll hts htl hsl hv hw
  have hxorP : fzrAV t tau lam ((n / 64 % 8) ^^^ (m / 64 % 8)) ∈ P := by
    rw [← hVmm, ← hwinv]
    exact hVP
  have hxor0 : (n / 64 % 8) ^^^ (m / 64 % 8) = 0 :=
    fzr_a_V_mem_P S htP (fzrAux_xor_lt_eight hv hw) hxorP
  have hvw : n / 64 % 8 = m / 64 % 8 := xor_eq_zero_iff.mp hxor0
  have hE : fzrAElt a b (n % 64) = fzrAElt a b (m % 64) := by
    have h' : fzrAElt a b (n % 64) * fzrAV t tau lam (m / 64 % 8)
        = fzrAElt a b (m % 64) * fzrAV t tau lam (m / 64 % 8) := by
      simpa [hvw] using h
    exact mul_right_cancel h'
  have hpq : n % 64 = m % 64 := (fzr_a_elt_eq_iff S.basis hp hq).mp hE
  have hnv : n / 64 % 8 = n / 64 := Nat.mod_eq_of_lt (by omega)
  have hmw : m / 64 % 8 = m / 64 := Nat.mod_eq_of_lt (by omega)
  have hn1 : n % 64 + 64 * (n / 64) = n := Nat.mod_add_div n 64
  have hm1 : m % 64 + 64 * (m / 64) = m := Nat.mod_add_div m 64
  omega

theorem fzrAMu_surj [Finite G] (S : FzR10ASet t tau lam rho Z E W Q R T P a b) (htP : t ∉ P)
    {g : G} (hg : g ∈ T) : ∃ n, n < 512 ∧ fzrAMu a b t tau lam n = g := by
  let f : Fin 512 → ↥T := fun k => ⟨fzrAMu a b t tau lam k.1, fzrAMu_mem S k.1⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hxy' : fzrAMu a b t tau lam x.1 = fzrAMu a b t tau lam y.1 := by
      simpa [f] using congrArg Subtype.val hxy
    exact Fin.ext (fzrAMu_inj S htP x.2 y.2 hxy')
  have hcard : Nat.card ↥T ≤ Nat.card (Fin 512) := by
    rw [S.str.card_T, Nat.card_fin]
  have hbij : Function.Bijective f := hf.bijective_of_nat_card_le hcard
  obtain ⟨k, hk⟩ := hbij.2 ⟨g, hg⟩
  exact ⟨k.1, k.2, by simpa [f] using congrArg Subtype.val hk⟩

end CFSG.OddStandard.SmallF3.FritzII
