module

public import CFSG.LargeExtraspecial.Asc611IG2
public import CFSG.LargeExtraspecial.Asc611IStepA

public section

namespace CFSG.LargeExtraspecial.Asc611I

open Subgroup CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary CFSG.LargeExtraspecial.AS35L
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

structure Setup (e : SUid frob m) (U : Subgroup (PG m)) : Prop where
  three_le : 3 ≤ m
  invol : e * e = 1
  isPGroup : IsPGroup 2 U
  normal : ∀ c ∈ centralizer ({(QuotientGroup.mk e : PG m)} : Set (PG m)), ∀ u ∈ U,
    c * u * c⁻¹ ∈ U
  noTransv : ∀ u ∈ U, u ∉ DG m

structure Frame2 (e : SUid frob m) (q y : Fin m → K) : Prop where
  hq : herm frob q (invN e q) = 1
  hy : herm frob y (invN e y) = 1
  hqy : herm frob q (invN e y) = 0
  iq : herm frob q q = 0
  iy : herm frob y y = 0
  iqy : herm frob q y = 0

variable {e : SUid frob m} {U : Subgroup (PG m)}

namespace Frame2

variable {q y : Fin m → K} (F : Frame2 e q y)
include F

theorem iso : herm frob (q + y) (q + y) = 0 := by
  rw [herm_add_left, herm_add_right, herm_add_right, F.iq, F.iy, F.iqy,
    herm_eq_zero_comm frob frob_frob F.iqy]
  simp

theorem isoN (he : e * e = 1) : herm frob (q + y) (invN e (q + y)) = 0 := by
  have hyq : herm frob y (invN e q) = 0 := by
    rw [herm_invN_swap he, F.hqy, map_zero]
  rw [invN_add, herm_add_left, herm_add_right, herm_add_right, F.hq, F.hy, F.hqy, hyq]
  simp [add_self_K]

theorem invN_ne_zero : invN e (q + y) ≠ 0 := by
  intro h0
  have : herm frob q (invN e (q + y)) = 1 := by
    rw [invN_add, herm_add_right, F.hq, F.hqy, add_zero]
  rw [h0, herm_zero_right] at this
  exact zero_ne_one this

end Frame2

theorem isoN_add_ker (he : e * e = 1) {a v : Fin m → K} (haN : herm frob a (invN e a) = 0)
    (hv : invN e v = 0) : herm frob (a + v) (invN e (a + v)) = 0 := by
  rw [invN_add, hv, add_zero, herm_add_left, haN, ← herm_invN_left he, hv, herm_zero_left,
    add_zero]

theorem smul_invN {k : SUid frob m} (hke : k * e = e * k)
    (hkN : ∀ x, invN e (k • x) = invN e x) (z : Fin m → K) : k • invN e z = invN e z := by
  rw [← invN_smul_of_comm hke, hkN]

theorem eq_of_add_eq_zero_vec {x z : Fin m → K} (h : x + z = 0) : x = z := by
  have := congrArg (· + z) h
  simpa [add_assoc, vec_add_self] using this

theorem smul_eq_of_perp {k : SUid frob m} (hkN : ∀ x, invN e (k • x) = invN e x)
    {z : Fin m → K} (hz : ∀ b, invN e b = 0 → herm frob z b = 0) : k • z = z := by
  refine eq_of_add_eq_zero_vec (eq_zero_of_herm frob fun b => ?_)
  have h1 : herm frob (k • z) b = herm frob z (k⁻¹ • b) := by
    conv_lhs => rw [← smul_inv_smul k b]
    rw [herm_smul_smul]
  have h2 : invN e (k⁻¹ • b + b) = 0 := by
    have := hkN (k⁻¹ • b)
    rw [smul_inv_smul] at this
    rw [invN_add, ← this, vec_add_self]
  rw [herm_add_left, h1, ← herm_add_right, hz _ h2]

section Steps

variable (S : Setup e U) {k : SUid frob m} (hk : (QuotientGroup.mk k : PG m) ∈ U)
  (hke : k * e = e * k) (hkN : ∀ x, invN e (k • x) = invN e x)
include S hk hke hkN

theorem smul_add_perp {q y : Fin m → K} (F : Frame2 e q y) {v : Fin m → K} (hv : invN e v = 0)
    {b : Fin m → K} (hb : invN e b = 0) : herm frob (k • v + v) b = 0 := by
  have he := S.invol
  set a := q + y with ha
  have haN : herm frob a (invN e a) = 0 := F.isoN he
  have hNa : invN e a ≠ 0 := F.invN_ne_zero
  have hperp : ∀ a' : Fin m → K, herm frob a' a' = 0 → herm frob a' (invN e a') = 0 →
      invN e a' ≠ 0 → herm frob (k • a' + a') b = 0 := fun a' h1 h2 h3 =>
    herm_shift_perp he S.normal S.noTransv hk hke h1 h2 (hkN a') h3 hb
  have h0 := hperp a F.iso haN hNa
  have hNav : invN e (a + v) = invN e a := by rw [invN_add, hv, add_zero]
  rcases herm_self_eq_zero_or_one' (a + v) with h | h
  · have h1 := hperp (a + v) h (isoN_add_ker he haN hv) (by rwa [hNav])
    have : k • v + v = (k • (a + v) + (a + v)) + (k • a + a) := by
      rw [smul_add]
      funext i
      simp only [Pi.add_apply]
      ring_nf
      simp [two_eq_zero]
    rw [this, herm_add_left, h1, h0, add_zero]
  · obtain ⟨z, c, hiso⟩ := exists_isotropic_shift he (show invN e (a + v) ≠ 0 by rwa [hNav])
    set w := c • invN e z with hw
    have hw0 : invN e w = 0 := by rw [hw, invN_smul, invN_invN he, smul_zero]
    have hkw : k • w = w := by rw [hw, smul_comm, smul_invN hke hkN]
    have hvw : invN e (v + w) = 0 := by rw [invN_add, hv, hw0, add_zero]
    have h1 := hperp (a + (v + w)) (by rwa [← add_assoc]) (isoN_add_ker he haN hvw)
      (by rw [invN_add, hvw, add_zero]; exact hNa)
    have : k • v + v = (k • (a + (v + w)) + (a + (v + w))) + (k • a + a) := by
      rw [smul_add k a (v + w), smul_add k v w, hkw]
      funext i
      simp only [Pi.add_apply]
      ring_nf
      simp [two_eq_zero]
    rw [this, herm_add_left, h1, h0, add_zero]

theorem smul_add_perp_all {q y : Fin m → K} (F : Frame2 e q y) (x : Fin m → K)
    {b : Fin m → K} (hb : invN e b = 0) : herm frob (k • x + x) b = 0 := by
  have he := S.invol
  rw [herm_conj frob frob_frob]
  suffices h : herm frob b (k • x + x) = 0 by rw [h, map_zero]
  refine linear_eq_zero_of_isotropic (isSesq_H e) (fun x z => herm_invN_swap he x z)
    (f := fun x => herm frob b (k • x + x)) (fun x z => ?_) (fun c x => ?_) (fun a ha => ?_)
    F.hq F.hy F.hqy x
  · simp only [smul_add, herm_add_right]; ring
  · simp only [smul_comm k c x, ← smul_add, herm_smul_right]
  · by_cases hNa : invN e a = 0
    · rw [herm_conj frob frob_frob, smul_add_perp S hk hke hkN F hNa hb, map_zero]
    · obtain ⟨z, c, hiso⟩ := exists_isotropic_shift he hNa
      set w := c • invN e z with hw
      have hw0 : invN e w = 0 := by rw [hw, invN_smul, invN_invN he, smul_zero]
      have hkw : k • w = w := by rw [hw, smul_comm, smul_invN hke hkN]
      have h1 := herm_shift_perp he S.normal S.noTransv hk hke hiso
        (isoN_add_ker he ha hw0) (hkN _) (by rw [invN_add, hw0, add_zero]; exact hNa) hb
      have : k • a + a = k • (a + w) + (a + w) := by
        rw [smul_add k a w, hkw]
        funext i
        simp only [Pi.add_apply]
        ring_nf
        simp [two_eq_zero]
      rw [this, herm_conj frob frob_frob, h1, map_zero]

end Steps

end CFSG.LargeExtraspecial.Asc611I
