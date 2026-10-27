module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10ANum
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10AFix

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzR10A Certificates.FzR10

variable {G : Type} [Group G] {t tau lam rho : G} {Z E W Q R T P : Subgroup G} {a b : G}
  {Mt Ms Ml : Mat}

theorem fzrAMu_rho (S : FzR10ASet t tau lam rho Z E W Q R T P a b) {x : ℕ} (hx : x < 256) :
    fzrAMu a b t tau lam (rho0.ap (x % 64) + 64 * (x / 64)) =
      rho * fzrAMu a b t tau lam x * rho⁻¹ := by
  have hp : x % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hv8 : x / 64 % 8 = x / 64 := Nat.mod_eq_of_lt (by omega)
  have hmod : (rho0.ap (x % 64) + 64 * (x / 64)) % 64 = rho0.ap (x % 64) := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (fzr_a_ap_lt rho0 (x % 64))]
  have hdiv : (rho0.ap (x % 64) + 64 * (x / 64)) / 64 % 8 = x / 64 := by
    rw [Nat.add_mul_div_left _ _ (by norm_num),
      Nat.div_eq_of_lt (fzr_a_ap_lt rho0 (x % 64)), Nat.zero_add]
    omega
  rw [fzrAMu, fzrAMu, hmod, hdiv, hv8]
  have hract : rho * fzrAElt a b (x % 64) * rho⁻¹ =
      fzrAElt a b (rho0.ap (x % 64)) := S.rho_act (x % 64) hp
  have hB : rho * fzrAV t tau lam (x / 64) * rho⁻¹ = fzrAV t tau lam (x / 64) := by
    have h4 : x / 64 / 4 % 2 = 0 := by omega
    have htauc : rho * tau * rho⁻¹ = tau := by
      rw [← S.str.tau_rho]; group
    rw [fzrAV, h4, pow_zero, mul_one]
    calc rho * (t ^ (x / 64 % 2) * tau ^ (x / 64 / 2 % 2)) * rho⁻¹
        = (rho * t ^ (x / 64 % 2) * rho⁻¹) *
            (rho * tau ^ (x / 64 / 2 % 2) * rho⁻¹) := by group
      _ = t ^ (x / 64 % 2) * tau ^ (x / 64 / 2 % 2) := by
          rw [← conj_pow, S.str.rho_t, ← conj_pow, htauc]
  calc fzrAElt a b (rho0.ap (x % 64)) * fzrAV t tau lam (x / 64)
      = (rho * fzrAElt a b (x % 64) * rho⁻¹) *
          (rho * fzrAV t tau lam (x / 64) * rho⁻¹) := by rw [hract, hB]
    _ = rho * (fzrAElt a b (x % 64) * fzrAV t tau lam (x / 64)) * rho⁻¹ := by
        group

theorem fzrAMu_inW (S : FzR10ASet t tau lam rho Z E W Q R T P a b)
    (hM : FzR10AMats t tau lam a b Mt Ms Ml) {x : ℕ} (h : (parOfA Mt Ms Ml).inW x = true) :
    fzrAMu a b t tau lam x ∈ W := by
  simp only [parOfA, Bool.and_eq_true, beq_iff_eq, decide_eq_true_iff] at h
  obtain ⟨hfix, hv2⟩ := h
  have hp : x % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hv8 : x / 64 % 8 = x / 64 := Nat.mod_eq_of_lt (by omega)
  have helt : fzrAElt a b (x % 64) ∈ E :=
    (fzr_a_fix_iff_E S hM.act_t hp).mp hfix
  have hV : fzrAV t tau lam (x / 64) = t ^ (x / 64) := by
    have h2 : x / 64 / 2 % 2 = 0 := by omega
    have h4 : x / 64 / 4 % 2 = 0 := by omega
    have hmod : x / 64 % 2 = x / 64 := Nat.mod_eq_of_lt (by omega)
    rw [fzrAV, h2, h4, pow_zero, pow_zero, mul_one, mul_one, hmod]
  rw [fzrAMu, hv8, hV]
  exact W.mul_mem (S.str.EW helt) (W.pow_mem S.str.t_mem (x / 64))

theorem fzrAMu_inTL (S : FzR10ASet t tau lam rho Z E W Q R T P a b)
    (hM : FzR10AMats t tau lam a b Mt Ms Ml) {x : ℕ} (hx : x < 512)
    (h : (parOfA Mt Ms Ml).inTL x = true) {L₀ : Subgroup G} (hE : E ≤ L₀) (hlam : lam ∈ L₀) :
    fzrAMu a b t tau lam x ∈ L₀ := by
  simp only [parOfA, Bool.and_eq_true, beq_iff_eq, decide_eq_true_iff] at h
  obtain ⟨hfix, hv4⟩ := h
  have hp : x % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hv : x / 64 < 8 := by omega
  have hv8 : x / 64 % 8 = x / 64 := Nat.mod_eq_of_lt (by omega)
  have helt : fzrAElt a b (x % 64) ∈ E :=
    (fzr_a_fix_iff_E S hM.act_t hp).mp hfix
  have hv_cases : x / 64 = 0 ∨ x / 64 = 4 := by omega
  have hV : fzrAV t tau lam (x / 64) = lam ^ (x / 64 / 4) := by
    rcases hv_cases with h0 | h4
    · rw [h0]; simp [fzrAV]
    · rw [h4]; norm_num [fzrAV]
  rw [fzrAMu, hv8, hV]
  exact L₀.mul_mem (hE helt) (L₀.pow_mem hlam (x / 64 / 4))

theorem fzrAMu_inTZ (S : FzR10ASet t tau lam rho Z E W Q R T P a b) (htP : t ∉ P)
    {z : G} (hz : z ∈ Z) {x : ℕ} (hx : x < 512) (h : fzrAMu a b t tau lam x = t * z) :
    (parOfA Mt Ms Ml).inTZ x = true := by
  simp only [parOfA, Bool.and_eq_true, beq_iff_eq, decide_eq_true_iff]
  have hp : x % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hv : x / 64 < 8 := by omega
  have hv8 : x / 64 % 8 = x / 64 := Nat.mod_eq_of_lt (by omega)
  have hgP : fzrAElt a b (x % 64) ∈ P := fzr_a_elt_mem S.basis (x % 64)
  have htT : t ∈ T := S.str.RT (S.str.QR (S.str.WQ S.str.t_mem))
  have ht2 : t * t = 1 := by rw [← pow_two, S.str.t_sq]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hgV : fzrAElt a b (x % 64) * fzrAV t tau lam (x / 64) = t * z := by
    have h' := h
    rwa [fzrAMu, hv8] at h'
  have hV : fzrAV t tau lam (x / 64) = (fzrAElt a b (x % 64))⁻¹ * t * z := by
    calc fzrAV t tau lam (x / 64) =
        (fzrAElt a b (x % 64))⁻¹ *
          (fzrAElt a b (x % 64) * fzrAV t tau lam (x / 64)) := by group
      _ = (fzrAElt a b (x % 64))⁻¹ * (t * z) := by rw [hgV]
      _ = (fzrAElt a b (x % 64))⁻¹ * t * z := by group
  have htVP : t * fzrAV t tau lam (x / 64) ∈ P := by
    have hconj : t * (fzrAElt a b (x % 64))⁻¹ * t⁻¹ ∈ P :=
      S.pf.nrm_P t htT _ (P.inv_mem hgP)
    have hzP : z ∈ P := S.pf.EP (S.str.ZE hz)
    have heq : t * fzrAV t tau lam (x / 64) =
        (t * (fzrAElt a b (x % 64))⁻¹ * t⁻¹) * z := by
      rw [hV, htinv]; group
    rw [heq]
    exact P.mul_mem hconj hzP
  have hlam2 : lam * lam = 1 := by rw [← pow_two, S.str.lam_sq]
  have htau2 : tau * tau = 1 := by rw [← pow_two, S.pf.tau_sq1]
  have httau : t * tau = tau * t := by
    have h1 : tau * t = t * tau := by
      calc tau * t = (tau * t * tau⁻¹) * tau := by group
        _ = t * tau := by rw [S.str.tau_t]
    exact h1.symm
  have htlam : t * lam = lam * t := by
    have h1 : lam * t = t * lam := by
      calc lam * t = (lam * t * lam⁻¹) * lam := by group
        _ = t * lam := by rw [S.str.lam_t]
    exact h1.symm
  have hV1 : t * fzrAV t tau lam (x / 64) = fzrAV t tau lam (1 ^^^ (x / 64)) := by
    calc t * fzrAV t tau lam (x / 64)
        = fzrAV t tau lam 1 * fzrAV t tau lam (x / 64) := by
          rw [fzr_a_V_one (t := t) (tau := tau) (lam := lam)]
      _ = fzrAV t tau lam (1 ^^^ (x / 64)) :=
          fzr_a_V_mul ht2 htau2 hlam2 httau htlam S.str.tau_lam
            (v := 1) (w := x / 64) (by norm_num) hv
  have hxor_lt : 1 ^^^ (x / 64) < 8 := by
    have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [h8]
    exact Nat.xor_lt_two_pow (by norm_num) (by omega)
  have hmem : fzrAV t tau lam (1 ^^^ (x / 64)) ∈ P := by
    simpa [← hV1] using htVP
  have hzero : 1 ^^^ (x / 64) = 0 := fzr_a_V_mem_P S htP hxor_lt hmem
  have hv1 : x / 64 = 1 := (Nat.xor_eq_zero_iff.mp hzero).symm
  have hx64 : x / 64 % 8 = 1 := by rw [hv1]
  have hg : fzrAElt a b (x % 64) * t = t * z := by
    have h' := h
    rw [fzrAMu, hx64, fzr_a_V_one] at h'
    exact h'
  have htcommz : t * z = z * t := S.str.W_comm t S.str.t_mem z (S.str.EW (S.str.ZE hz))
  have hgt : fzrAElt a b (x % 64) = t * z * t := by
    calc fzrAElt a b (x % 64) = (fzrAElt a b (x % 64) * t) * t := by
          rw [mul_assoc, ht2, mul_one]
      _ = (t * z) * t := by rw [hg]
  have hgz : fzrAElt a b (x % 64) = z := by
    rw [hgt, htcommz, mul_assoc, ht2, mul_one]
  have hgsq : fzrAElt a b (x % 64) ^ 2 = 1 := by
    rw [hgz, S.str.Z_sq z hz]
  exact ⟨hv1, (fzr_a_elt_sq_eq_one_iff S.basis hp).mp hgsq⟩

end CFSG.OddStandard.SmallF3.FritzII
