module

public import CFSG.LargeExtraspecial.Asc611IBasic
public import CFSG.LargeExtraspecial.Asc611ILift

public section

namespace CFSG.LargeExtraspecial.Asc611I

open Subgroup CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary CFSG.LargeExtraspecial.AS35L
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ} {e : SUid frob m}

section Formula

variable (he : e * e = 1) {g : SUid frob m} (hge : g * e = e * g) {a : Fin m → K}
  (ha : herm frob a a = 0) (haN : herm frob a (invN e a) = 0)
  (hgN : invN e (g • a) = invN e a)
include he hge ha haN hgN

omit he hgN in
theorem comm_cv_eq : g * cv e a * g⁻¹ * (cv e a)⁻¹ = cv e (g • a) * cv e a := by
  rw [cv_inv ha haN, conj_cv hge ha (by rw [herm_smul_smul, ha])]

theorem comm_cv_smul (x : Fin m → K) :
    (g * cv e a * g⁻¹ * (cv e a)⁻¹) • x = x + herm frob (g • a + a) x • invN e a +
      herm frob (invN e a) x • (g • a + a) +
      (herm frob (g • a) a * herm frob (invN e a) x) • invN e a := by
  rw [comm_cv_eq hge ha haN]
  have hga : herm frob (g • a) (g • a) = 0 := by rw [herm_smul_smul, ha]
  have hgaN : herm frob (g • a) (invN e (g • a)) = 0 := by
    rw [herm_invN_smul_smul hge, haN]
  have hnn : herm frob (invN e a) (invN e a) = 0 := herm_invN_invN he a a
  have hna : herm frob (invN e a) a = 0 := by rw [herm_invN_left he, haN]
  have hgan : herm frob (g • a) (invN e a) = 0 := by rw [← hgN, hgaN]
  rw [mul_smul, cv_smul ha haN x, cv_smul hga hgaN, hgN]
  simp only [herm_add_right, herm_smul_right, hnn, hna, hgan, mul_zero, add_zero]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, herm_add_left]
  ring_nf
  simp [two_eq_zero]

end Formula

theorem herm_self_eq_zero_or_one' (x : Fin m → K) : herm frob x x = 0 ∨ herm frob x x = 1 :=
  (frob_eq_self_iff _).mp (herm_self_fixed frob frob_frob x)

section Normal

variable (hm : 3 ≤ m) (he : e * e = 1) {U : Subgroup (PG m)}
  (hUN : ∀ c ∈ centralizer ({(QuotientGroup.mk e : PG m)} : Set (PG m)), ∀ u ∈ U,
    c * u * c⁻¹ ∈ U)
  (hUD : ∀ u ∈ U, u ∉ DG m)
include he hUN hUD

theorem trace_shift {g : SUid frob m} (hg : (QuotientGroup.mk g : PG m) ∈ U)
    (hge : g * e = e * g) {a : Fin m → K} (ha : herm frob a a = 0)
    (haN : herm frob a (invN e a) = 0) (hgN : invN e (g • a) = invN e a)
    (hNa : invN e a ≠ 0) {v : Fin m → K} (hv : invN e v = 0)
    (hav : herm frob (a + v) (a + v) = 0) :
    herm frob (g • a + a) (a + v) + frob (herm frob (g • a + a) (a + v)) = 0 := by
  set g' := g * cv e a * g⁻¹ * (cv e a)⁻¹ with hg'def
  have hg' : (QuotientGroup.mk g' : PG m) ∈ U := mk_comm_mem hUN hg (cv_comm he ha haN)
  have hcv : Commute (cv e a) e := cv_comm he ha haN
  have hgc : Commute g e := hge
  have hg'e : g' * e = e * g' :=
    (((Commute.mul_left hgc hcv).mul_left hgc.inv_left).mul_left hcv.inv_left)
  set b := a + v with hb
  set τ := herm frob (g • a + a) b with hτ
  have hNb : invN e b = invN e a := by rw [hb, invN_add, hv, add_zero]
  have hna : herm frob (invN e a) a = 0 := by rw [herm_invN_left he, haN]
  have hnv : herm frob (invN e a) v = 0 := by rw [herm_invN_left he, hv, herm_zero_right]
  have hnb : herm frob (invN e a) b = 0 := by rw [hb, herm_add_right, hna, hnv, add_zero]
  have hbN : herm frob b (invN e b) = 0 := by
    rw [hNb, herm_conj frob frob_frob, hnb, map_zero]
  have hg'b : g' • b = b + τ • invN e a := by
    rw [hg'def, comm_cv_smul he hge ha haN hgN, hnb, zero_smul, mul_zero, zero_smul,
      add_zero, add_zero]
  have hs' : g' • b + b = τ • invN e a := by
    rw [hg'b, add_comm b, add_assoc, vec_add_self, add_zero]
  have hg'N : invN e (g' • b) = invN e b := by
    rw [hg'b, invN_add, invN_smul, invN_invN he, smul_zero, add_zero]
  have hγ : herm frob (g' • b) b = 0 := by
    rw [hg'b, herm_add_left, hav, herm_smul_left, hnb, mul_zero, add_zero]
  have hg'' := mk_comm_mem hUN hg' (cv_comm he hav hbN)
  have hnn : herm frob (invN e a) (invN e a) = 0 := herm_invN_invN he a a
  by_contra htr
  have h1 := (add_frob_eq_zero_or_one τ).resolve_left htr
  have heq : g' * cv e b * g'⁻¹ * (cv e b)⁻¹ = tvU (invN e a) := by
    refine ext_smul _ fun x => ?_
    rw [comm_cv_smul he hg'e hav hbN hg'N, hs', hγ, zero_mul, zero_smul, add_zero, hNb,
      herm_smul_left, tvU_smul hnn, add_assoc, smul_smul, ← add_smul]
    congr 2
    linear_combination herm frob (invN e a) x * h1
  apply hUD _ hg''
  rw [heq]
  exact tq_mem_DG hNa hnn

theorem herm_shift_perp {g : SUid frob m} (hg : (QuotientGroup.mk g : PG m) ∈ U)
    (hge : g * e = e * g) {a : Fin m → K} (ha : herm frob a a = 0)
    (haN : herm frob a (invN e a) = 0) (hgN : invN e (g • a) = invN e a)
    (hNa : invN e a ≠ 0) {v : Fin m → K} (hv : invN e v = 0) :
    herm frob (g • a + a) v = 0 := by
  set s := g • a + a with hs
  have hNs : invN e s = 0 := by rw [hs, invN_add, hgN, vec_add_self]
  have h0 := trace_shift he hUN hUD hg hge ha haN hgN hNa (v := 0) (invN_zero e)
    (by rw [add_zero, ha])
  rw [add_zero] at h0
  have tr : ∀ v, invN e v = 0 → herm frob s v + frob (herm frob s v) = 0 := by
    intro v hv
    rcases herm_self_eq_zero_or_one' (a + v) with h | h
    · have h1 := trace_shift he hUN hUD hg hge ha haN hgN hNa hv h
      rw [herm_add_right, map_add] at h1
      linear_combination h1 - h0
    · obtain ⟨z, hz⟩ := exists_herm_eq_one frob hNa
      set w := ω • invN e z with hw
      have hw0 : invN e w = 0 := by rw [hw, invN_smul, invN_invN he, smul_zero]
      have haw : herm frob a w = ω := by
        rw [hw, herm_smul_right, ← herm_invN_left he, hz, mul_one]
      have hwa : herm frob w a = ω + 1 := by
        rw [herm_conj frob frob_frob, haw, frob_omega]
      have hvw : herm frob v w = 0 := by
        rw [hw, herm_smul_right, ← herm_invN_left he, hv, herm_zero_left, mul_zero]
      have hwv : herm frob w v = 0 := by rw [herm_conj frob frob_frob, hvw, map_zero]
      have hsw : herm frob s w = 0 := by
        rw [hw, herm_smul_right, ← herm_invN_left he, hNs, herm_zero_left, mul_zero]
      have hww : herm frob w w = 0 := by
        rw [hw, herm_smul_left, herm_smul_right, herm_invN_invN he, mul_zero, mul_zero]
      have huw : herm frob (a + v) w = ω := by rw [herm_add_left, haw, hvw, add_zero]
      have hwu : herm frob w (a + v) = ω + 1 := by rw [herm_add_right, hwa, hwv, add_zero]
      have h2 : herm frob (a + (v + w)) (a + (v + w)) = 0 := by
        rw [← add_assoc]
        set u := a + v with hu
        clear_value u
        rw [ herm_add_left, herm_add_right, herm_add_right, h, huw, hwu,
          hww]
        linear_combination (1 + ω) * two_eq_zero
      have hvw0 : invN e (v + w) = 0 := by rw [invN_add, hv, hw0, add_zero]
      have h3 := trace_shift he hUN hUD hg hge ha haN hgN hNa hvw0 h2
      rw [herm_add_right, herm_add_right, hsw, add_zero, map_add] at h3
      linear_combination h3 - h0
  have t1 := tr v hv
  have t2 := tr (ω • v) (by rw [invN_smul, hv, smul_zero])
  rw [herm_smul_right] at t2
  rcases (add_frob_eq_zero_iff _).1 t1 with h | h
  · exact h
  · exfalso
    rw [h, mul_one, omega_add_frob] at t2
    exact one_ne_zero t2

end Normal

end CFSG.LargeExtraspecial.Asc611I
