module

public import CFSG.ClassicalInvolution.Asc77.AscC25V42
public import CFSG.ClassicalInvolution.Asc77.AscC25V47

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

section Main

variable {p f : ℕ} [Fact p.Prime]


theorem gcs25z_of_g1 (h11 : C25_11 p f) (h9 : p ^ f ≠ 9) (hG1 : G1_25 p f) : GCS25Z p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ t' h hg hnf hat hp hq e n hnS
    hn hn' hδ hδ'
  classical
  let _ : CommGroup (GaloisField p f ≃+* GaloisField p f) := ringAutCommGroup _
  have hC := h11 G Ω K K' W S R R' z t u₁ u₂ hyp
  have hfix := fix_of_isFAut h haS hFa'
  have haK : a ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_iff_conjSub_eq.mpr hfix.2.2.1
  have hσ : fieldChar hp hq e ⟨a, haK⟩ ≠ 1 :=
    fieldChar_ne_one_of_isFAut hp hq e h.hRsyl.1 h.hqR h.hzR hFa ha2 haK
  have haz : a * z = z * a := hyp.hzS a haS
  have hnz : n * z = z * n := hyp.hzS n hnS
  obtain ⟨d, hdN, hdN', hdz, hda, hχd, hχd'⟩ :=
    exists_comm_rep h hC hp hq e ha2 haz hat hFa haK hσ hn hnz hn' hδ hδ'
  have hodd := hG1 G Ω K K' W S R R' z t u₁ u₂ t' h h9 a haS ha2 hFa' hat hZ hp hq e d hdN hdz hda
    hdN'
  rw [hχd, hχd'] at hodd
  obtain ⟨i, hi⟩ := IsPGroup.iff_orderOf.mp S.isPGroup' (⟨n, hnS⟩ : (S : Subgroup G))
  have hi' : n ^ 2 ^ i = 1 := by
    have := pow_orderOf_eq_one (⟨n, hnS⟩ : (S : Subgroup G))
    rw [hi] at this
    exact congrArg Subtype.val this
  have h1 : fieldChar hp hq e ⟨n, hn⟩ ^ 2 ^ i = 1 := by
    rw [← map_pow]
    have : (⟨n, hn⟩ : Subgroup.normalizer (K : Set G)) ^ 2 ^ i = 1 := Subtype.ext hi'
    rw [this, map_one]
  have h2 : fieldChar hp hq e ⟨t' * n * t', hn'⟩ ^ 2 ^ i = 1 := by
    rw [← map_pow]
    have : (⟨t' * n * t', hn'⟩ : Subgroup.normalizer (K : Set G)) ^ 2 ^ i = 1 := by
      apply Subtype.ext
      change (t' * n * t') ^ 2 ^ i = 1
      have e3 : t' * n * t' = t' * n * t'⁻¹ := by rw [h.ht'inv]
      rw [e3, ← MulAut.conj_apply, ← map_pow]
      simp [hi']
    rw [this, map_one]
  exact (eq_of_odd_orderOf_of_pow_eq_one h1 h2 hodd).symm

theorem res25_of_g1_diag25 (h11 : C25_11 p f) (h9 : p ^ f ≠ 9) (hG1 : G1_25 p f)
    (hD : DIAG25 p f) : RES25 p f :=
  res25_of_parts (gcs25z_of_g1 h11 h9 hG1) hD

theorem ne_nine_of_four_dvd (hf0 : f % 4 = 0) : p ^ f ≠ 9 := by
  intro h9
  rcases Nat.eq_zero_or_pos f with h0 | h0
  · rw [h0, pow_zero] at h9
    omega
  · have hf4 : 4 ≤ f := by omega
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have h1 : 2 ^ 4 ≤ p ^ f := calc
      2 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left hp2 4
      _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf4
    omega

theorem res25_of_residuals' (h11 : C25_11 p f) (hf : Even f) (hG6 : 4 ∣ f → G1Omega6 p f)
    (hD : DIAG25 p f) : RES25 p f := by
  have hf2 : f % 2 = 0 := Nat.even_iff.mp hf
  by_cases hf4 : f % 4 = 2
  · exact res25_of_pm h11 hf4 hD
  · have hf0 : f % 4 = 0 := by omega
    exact res25_of_g1_diag25 h11 (ne_nine_of_four_dvd hf0)
      (g1_25_of_omega6 (hG6 (Nat.dvd_of_mod_eq_zero hf0))) hD

theorem c25_16invEven_of_diag25 (h11 : C25_11 p f) (hG6 : 4 ∣ f → G1Omega6 p f)
    (hD : Even f → DIAG25 p f) : Even f → T7U.C25_16inv p f :=
  fun hf => c25_16inv_of_res h11 mix25_all (res25_of_residuals' h11 hf hG6 (hD hf))

end Main

end CFSG.ClassicalInvolution.Asc77.C25V
