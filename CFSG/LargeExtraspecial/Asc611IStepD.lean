module

public import CFSG.LargeExtraspecial.Asc611IStepB

public section

namespace CFSG.LargeExtraspecial.Asc611I

open Subgroup CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary CFSG.LargeExtraspecial.AS35L
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ} {e : SUid frob m} {U : Subgroup (PG m)}

section Steps

variable (S : Setup e U) {k : SUid frob m} (hk : (QuotientGroup.mk k : PG m) ∈ U)
  (hke : k * e = e * k) (hkN : ∀ x, invN e (k • x) = invN e x)
include S hk hke hkN

theorem smul_eq_of_ker_iso {q y : Fin m → K} (F : Frame2 e q y) {v : Fin m → K}
    (hv : invN e v = 0) (hvv : herm frob v v = 0) : k • v = v := by
  have he := S.invol
  set d := k • v + v with hd
  have hdperp : ∀ b, invN e b = 0 → herm frob d b = 0 := fun b hb =>
    smul_add_perp S hk hke hkN F hv hb
  by_contra hne
  have hd0 : d ≠ 0 := fun h0 => hne (eq_of_add_eq_zero_vec h0)
  have hvnot : ¬ ∀ b, invN e b = 0 → herm frob v b = 0 := fun h => hne (smul_eq_of_perp hkN h)
  push Not at hvnot
  obtain ⟨b₀, hb₀, hvb₀⟩ := hvnot
  have hkv : herm frob (k • v) (k • v) = 0 := by rw [herm_smul_smul, hvv]
  have hkvv : herm frob (k • v) v = 0 := by
    have : k • v = d + v := by rw [hd, add_assoc, vec_add_self, add_zero]
    rw [this, herm_add_left, hdperp v hv, hvv, add_zero]
  have hNkv : invN e (k • v) = 0 := by rw [hkN, hv]
  have hU1 := mk_comm_mem S.normal hk (tvU_comm_of_ker hvv hv)
  rw [conj_tvU k hvv, tvU_inv hvv] at hU1
  have hce1 : Commute (tvU (k • v)) e := tvU_comm_of_ker hkv hNkv
  have hce2 : Commute (tvU v) e := tvU_comm_of_ker hvv hv
  have hk'e : tvU (k • v) * tvU v * e = e * (tvU (k • v) * tvU v) := hce1.mul_left hce2
  have hk'smul : ∀ x, (tvU (k • v) * tvU v) • x =
      x + herm frob v x • v + herm frob (k • v) x • (k • v) := by
    intro x
    rw [mul_smul, tvU_smul hvv, tvU_smul hkv, herm_add_right, herm_smul_right, hkvv,
      mul_zero, add_zero]
  have hk'N : ∀ x, invN e ((tvU (k • v) * tvU v) • x) = invN e x := by
    intro x
    rw [hk'smul, invN_add, invN_add, invN_smul, invN_smul, hv, hNkv, smul_zero, smul_zero,
      add_zero, add_zero]
  have key : ∀ a, herm frob a a = 0 → herm frob a (invN e a) = 0 → invN e a ≠ 0 →
      herm frob d a = 0 := by
    intro a ha haN hNa
    have hs := herm_shift_perp he S.normal S.noTransv hU1 hk'e ha haN (hk'N a) hNa hb₀
    have hcomp : (tvU (k • v) * tvU v) • a + a =
        herm frob d a • v + herm frob (k • v) a • d := by
      rw [hk'smul, hd, herm_add_left]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring_nf
      simp [two_eq_zero]
    rw [hcomp, herm_add_left, herm_smul_left, herm_smul_left, hdperp b₀ hb₀, mul_zero,
      add_zero] at hs
    rcases mul_eq_zero.mp hs with h | h
    · exact (map_eq_zero_iff frob frob.injective).mp h
    · exact absurd h hvb₀
  have hall : ∀ x, herm frob d x = 0 := by
    refine linear_eq_zero_of_isotropic (isSesq_H e) (fun x z => herm_invN_swap he x z)
      (f := herm frob d) (fun x z => herm_add_right frob d x z)
      (fun c x => herm_smul_right frob c d x) (fun a ha => ?_) F.hq F.hy F.hqy
    by_cases hNa : invN e a = 0
    · exact hdperp a hNa
    · obtain ⟨z, c, hiso⟩ := exists_isotropic_shift he hNa
      have hw0 : invN e (c • invN e z) = 0 := by rw [invN_smul, invN_invN he, smul_zero]
      have h1 := key _ hiso (isoN_add_ker he ha hw0) (by rw [invN_add, hw0, add_zero]; exact hNa)
      rwa [herm_add_right, hdperp _ hw0, add_zero] at h1
  exact hd0 (eq_zero_of_herm frob hall)

theorem smul_eq_of_ker_aniso {q y : Fin m → K} (F : Frame2 e q y) {v : Fin m → K}
    (hv : invN e v = 0) (hvv : herm frob v v = 1) : k • v = v := by
  have he := S.invol
  by_cases hex : ∃ v', invN e v' = 0 ∧ herm frob v' v' = 0 ∧ herm frob v v' ≠ 0
  · obtain ⟨v', hv', hv'v', hvv'⟩ := hex
    set l := ω * (herm frob v v')⁻¹ with hl
    have hl' : l * herm frob v v' = ω := by rw [hl, mul_assoc, inv_mul_cancel₀ hvv', mul_one]
    have hlv : invN e (l • v') = 0 := by rw [invN_smul, hv', smul_zero]
    have hlvv : herm frob (l • v') (l • v') = 0 := by
      rw [herm_smul_left, herm_smul_right, hv'v', mul_zero, mul_zero]
    have hsum : invN e (v + l • v') = 0 := by rw [invN_add, hv, hlv, add_zero]
    have hiso : herm frob (v + l • v') (v + l • v') = 0 := by
      have hv'v : herm frob v' v = frob (herm frob v v') := herm_conj frob frob_frob v v'
      rw [herm_add_left, herm_add_right, herm_add_right, hlvv, hvv, herm_smul_right,
        herm_smul_left, hv'v, hl', ← map_mul, hl', frob_omega]
      linear_combination (1 + ω) * two_eq_zero
    have h1 := smul_eq_of_ker_iso S hk hke hkN F hsum hiso
    have h2 := smul_eq_of_ker_iso S hk hke hkN F hlv hlvv
    rw [smul_add, h2] at h1
    exact add_right_cancel h1
  · push Not at hex
    set d := k • v + v with hd
    have hdperp : ∀ b, invN e b = 0 → herm frob d b = 0 := fun b hb =>
      smul_add_perp S hk hke hkN F hv hb
    have hNd : invN e d = 0 := by rw [hd, invN_add, hkN, hv, add_zero]
    have hdd : herm frob d d = 0 := hdperp d hNd
    have hL : ∀ u, invN e u = 0 → herm frob v u = 0 → herm frob u u = 0 := by
      intro u hu hvu
      rcases herm_self_eq_zero_or_one' u with h | h
      · exact h
      · exfalso
        have huv : herm frob u v = 0 := herm_eq_zero_comm frob frob_frob hvu
        have h1 := hex (v + u) (by rw [invN_add, hv, hu, add_zero]) (by
          rw [herm_add_left, herm_add_right, herm_add_right, hvv, hvu, huv, h]
          simp [add_self_K])
        rw [herm_add_right, hvv, hvu, add_zero] at h1
        exact one_ne_zero h1
    have hLperp : ∀ r, invN e r = 0 → herm frob v r = 0 → ∀ b, invN e b = 0 →
        herm frob r b = 0 := by
      intro r hr hvr b hb
      set b' := b + herm frob v b • v with hb'
      have hb'0 : invN e b' = 0 := by rw [hb', invN_add, invN_smul, hv, hb, smul_zero, add_zero]
      have hvb' : herm frob v b' = 0 := by
        rw [hb', herm_add_right, herm_smul_right, hvv, mul_one, add_self_K]
      have hrv : herm frob r v = 0 := herm_eq_zero_comm frob frob_frob hvr
      have key : ∀ l : K, l ≠ 0 → 0 + l * herm frob r b' + frob l * herm frob b' r = 0 := by
        intro l hl
        have h0 := hL (r + l • b') (by rw [invN_add, invN_smul, hr, hb'0, smul_zero, add_zero])
          (by rw [herm_add_right, herm_smul_right, hvr, hvb', mul_zero, add_zero])
        rw [herm_add_left, herm_add_right, herm_add_right, herm_smul_left, herm_smul_right,
          herm_smul_left, herm_smul_right, hL r hr hvr, hL b' hb'0 hvb'] at h0
        linear_combination h0
      have h1 := (three_lambda key).1
      rw [hb', herm_add_right, herm_smul_right, hrv, mul_zero, add_zero] at h1
      exact h1
    have hkv : k • v = v + d := by
      rw [hd, add_comm (k • v) v, ← add_assoc, vec_add_self, zero_add]
    have hsq : k ^ 2 = tvU d := by
      refine ext_smul _ fun x => ?_
      set sx := k • x + x with hsx
      have hkx : k • x = x + sx := by
        rw [hsx, add_comm (k • x) x, ← add_assoc, vec_add_self, zero_add]
      have hsx0 : invN e sx = 0 := by rw [hsx, invN_add, hkN, vec_add_self]
      clear_value sx
      set r := sx + herm frob v sx • v with hr
      have hr0 : invN e r = 0 := by rw [hr, invN_add, invN_smul, hv, hsx0, smul_zero, add_zero]
      have hvr : herm frob v r = 0 := by
        rw [hr, herm_add_right, herm_smul_right, hvv, mul_one, add_self_K]
      have hkr : k • r = r := smul_eq_of_perp hkN (hLperp r hr0 hvr)
      clear_value r
      have hunit : herm frob v sx = herm frob d x := by
        have h1 : herm frob (k • v) (k • x) = herm frob v x := herm_smul_smul frob k v x
        rw [hkv, hkx, herm_add_left, herm_add_right, herm_add_right, hdperp sx hsx0,
          add_zero] at h1
        linear_combination h1 - herm frob d x * two_eq_zero
      have hsxr : sx = r + herm frob v sx • v := by
        rw [hr, add_assoc, ← add_smul, add_self_K, zero_smul, add_zero]
      have hksx : k • sx = sx + herm frob v sx • d := by
        have h2 : k • sx = r + herm frob v sx • v + herm frob v sx • d := by
          conv_lhs => rw [hsxr]
          rw [smul_add, hkr, smul_comm, hkv, smul_add, add_assoc]
        rw [h2, ← hsxr]
      rw [sq, mul_smul, tvU_smul hdd, ← hunit, hkx, smul_add, hkx, hksx]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring_nf
      simp [two_eq_zero]
    by_contra hne
    have hd0 : d ≠ 0 := fun h0 => hne (eq_of_add_eq_zero_vec h0)
    apply S.noTransv _ (U.pow_mem hk 2)
    rw [← QuotientGroup.mk_pow, hsq]
    exact tq_mem_DG hd0 hdd

theorem smul_eq_of_ker {q y : Fin m → K} (F : Frame2 e q y) {v : Fin m → K}
    (hv : invN e v = 0) : k • v = v := by
  rcases herm_self_eq_zero_or_one' v with h | h
  · exact smul_eq_of_ker_iso S hk hke hkN F hv h
  · exact smul_eq_of_ker_aniso S hk hke hkN F hv h

end Steps

end CFSG.LargeExtraspecial.Asc611I
