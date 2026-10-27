module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutUnitaryCoordAut
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvField

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Bender

namespace UnitaryCoordAut

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.ShultStronglyClosedTI

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem comm_fst (J : HermitianForm 3 K) (z w : hermitianUnipotentCoord J) :
    ((w * z)⁻¹ * (z * w)).1.1 = 0 := by
  change -(w.1.1 + z.1.1) + (z.1.1 + w.1.1) = 0
  ring

omit [Finite K] [CharP K 2] in
theorem comm_snd (J : HermitianForm 3 K) (z w : hermitianUnipotentCoord J) :
    ((w * z)⁻¹ * (z * w)).1.2 = w.1.1 * J.conj z.1.1 - z.1.1 * J.conj w.1.1 := by
  change J.conj (w.1.2 + z.1.2 - w.1.1 * J.conj z.1.1) + (z.1.2 + w.1.2 - z.1.1 * J.conj w.1.1) -
    -(w.1.1 + z.1.1) * J.conj (z.1.1 + w.1.1) = _
  rw [map_sub, map_add, map_mul, J.conj_involutive, map_add]
  linear_combination z.2 + w.2

theorem center_fixed (J : HermitianForm 3 K) (q : ℕ) (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q) (hq : 4 ≤ q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (ψ : hermitianUnipotentCoord J →* hermitianUnipotentCoord J) (hψψ : ∀ z, ψ (ψ z) = z)
    (htor : ∀ k : Kˣ, ∃ k' : Kˣ,
      ∀ z, ψ (hermitianTorusAction J k z) = hermitianTorusAction J k' (ψ z)) :
    ∀ z : hermitianUnipotentCoord J, z.1.1 = 0 → ψ z = z := by
  classical
  have hσσ := J.conj_involutive
  have hsurj := unitaryCoverFirstCoord_surjective J q hcard hfixed hJ
  choose sec hsec using fun a : K => hsurj (Multiplicative.ofAdd a)
  have hsec1 : ∀ a, (sec a).1.1 = a := fun a => congrArg Multiplicative.toAdd (hsec a)
  obtain ⟨u₀, hu₀⟩ : ∃ u : K, J.conj u ≠ u := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card {x : K // J.conj x = x} = Nat.card K :=
      Nat.card_congr (Equiv.subtypeUnivEquiv hcon)
    rw [hfixed, hcard] at h1
    have : q * 1 < q * q := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    rw [sq] at h1
    omega
  have hcentral : ∀ z : hermitianUnipotentCoord J, (∀ w, w * z = z * w) → z.1.1 = 0 := by
    intro z hz
    by_contra hz0
    have hcz : J.conj z.1.1 ≠ 0 := (map_ne_zero J.conj).mpr hz0
    have h := (UnitaryCoord.mul_comm_iff J z (sec (u₀ / J.conj z.1.1))).mp (hz _)
    rw [hsec1, map_div₀, hσσ] at h
    apply hu₀
    have e1 : u₀ / J.conj z.1.1 * J.conj z.1.1 = u₀ := div_mul_cancel₀ u₀ hcz
    have e2 : z.1.1 * (J.conj u₀ / z.1.1) = J.conj u₀ := by field_simp
    rw [e1, e2] at h
    exact h.symm
  have hcentral' : ∀ z : hermitianUnipotentCoord J, z.1.1 = 0 → ∀ w, w * z = z * w := by
    intro z hz w
    rw [UnitaryCoord.mul_comm_iff, hz, map_zero, mul_zero, zero_mul]
  have hψcen : ∀ z : hermitianUnipotentCoord J, z.1.1 = 0 → (ψ z).1.1 = 0 := by
    intro z hz
    apply hcentral
    intro w
    rw [← hψψ w, ← map_mul, ← map_mul, hcentral' z hz (ψ w)]
  have hfib : ∀ z z' : hermitianUnipotentCoord J, z.1.1 = z'.1.1 → (ψ z').1.1 = (ψ z).1.1 := by
    intro z z' h
    have hc1 : (z⁻¹ * z').1.1 = 0 := by
      change -z.1.1 + z'.1.1 = 0
      rw [h]
      ring
    have hz' : ψ z' = ψ z * ψ (z⁻¹ * z') := by rw [← map_mul, mul_inv_cancel_left]
    rw [hz']
    change (ψ z).1.1 + (ψ (z⁻¹ * z')).1.1 = _
    rw [hψcen _ hc1, add_zero]
  set L : K → K := fun a => (ψ (sec a)).1.1 with hLdef
  have hL : ∀ z, (ψ z).1.1 = L z.1.1 := fun z => hfib (sec z.1.1) z (hsec1 _)
  have hLadd : ∀ a a', L (a + a') = L a + L a' := by
    intro a a'
    have h := congrArg (fun v : hermitianUnipotentCoord J => v.1.1) (map_mul ψ (sec a) (sec a'))
    change (ψ (sec a * sec a')).1.1 = (ψ (sec a)).1.1 + (ψ (sec a')).1.1 at h
    have e1 : (sec a * sec a').1.1 = a + a' := by
      change (sec a).1.1 + (sec a').1.1 = _
      rw [hsec1, hsec1]
    rw [hL (sec a * sec a'), e1] at h
    exact h
  have hLL : ∀ a, L (L a) = a := by
    intro a
    have h := congrArg (fun v : hermitianUnipotentCoord J => v.1.1) (hψψ (sec a))
    change (ψ (ψ (sec a))).1.1 = (sec a).1.1 at h
    rw [hL (ψ (sec a)), hsec1] at h
    exact h
  have hL0 : L 0 = 0 := by
    have h := hLadd 0 0
    rw [add_zero] at h
    linear_combination -h
  choose kk hkk using htor
  set sc : Kˣ → K := fun k => (k : K) * (J.conj (k : K))⁻¹ ^ 2 with hscdef
  have hLs : ∀ k a, L (a * sc k) = L a * sc (kk k) := by
    intro k a
    have h := congrArg (fun v : hermitianUnipotentCoord J => v.1.1) (hkk k (sec a))
    simp only [hL, torusAction_fst, hsec1] at h
    exact h
  obtain ⟨lam, hlamdef⟩ : ∃ lam, L 1 = lam := ⟨_, rfl⟩
  have hLzero : ∀ a, L a = 0 → a = 0 := by
    intro a ha
    rw [← hLL a, ha, hL0]
  have hlam0 : lam ≠ 0 := fun h => one_ne_zero (hLzero 1 (hlamdef.trans h))
  set θ : K → K := fun a => L a * lam⁻¹ with hθdef
  have hθ1 : θ 1 = 1 := by simp only [hθdef, hlamdef]; exact mul_inv_cancel₀ hlam0
  have hθadd : ∀ a a', θ (a + a') = θ a + θ a' := by
    intro a a'
    simp only [hθdef, hLadd a a']
    ring
  have hθs : ∀ k a, θ (a * sc k) = θ a * θ (sc k) := by
    intro k a
    have h1 := hLs k a
    have h2 := hLs k 1
    rw [one_mul, hlamdef] at h2
    simp only [hθdef, h1, h2]
    field_simp
  have hθr : ∀ r : K, J.conj r = r → ∀ a, θ (a * r) = θ a * θ r := by
    intro r hr a
    by_cases hr0 : r = 0
    · simp only [hθdef, hr0, mul_zero, hL0, zero_mul]
    · have hk : sc (Units.mk0 r hr0)⁻¹ = r := scalar_of_fix J hr hr0
      rw [← hk]
      exact hθs _ a
  obtain ⟨k₀, hk₀⟩ := exists_scalar_not_fix J q hcard hfixed hq hJ
  have hdec := UnitaryField.exists_decomp J.conj q hcard hfixed (μ := 1) (ν := sc k₀)
    one_ne_zero (fun r hr h => by
      apply hk₀
      change J.conj (sc k₀) = sc k₀
      rw [h, one_mul, hr])
  have hθmul : ∀ x a, θ (x * a) = θ x * θ a := by
    intro x a
    obtain ⟨r₁, r₂, hr₁, hr₂, rfl⟩ := hdec x
    have e1 : (1 * r₁ + sc k₀ * r₂) * a = a * r₁ + (a * r₂) * sc k₀ := by ring
    have e2 : 1 * r₁ + sc k₀ * r₂ = 1 * r₁ + r₂ * sc k₀ := by ring
    rw [e1, e2, hθadd, hθadd, hθr r₁ hr₁, hθs, hθr r₂ hr₂, hθr r₁ hr₁, hθs, hθ1]
    ring
  let θr : K →+* K :=
    { toFun := θ
      map_one' := hθ1
      map_mul' := hθmul
      map_zero' := by simp only [hθdef, hL0, zero_mul]
      map_add' := hθadd }
  have hLθ : ∀ a, L a = lam * θ a := by
    intro a
    simp only [hθdef]
    field_simp
  have hθinj : Function.Injective θ := by
    intro a b h
    have h1 : L a = L b := by rw [hLθ, hLθ, h]
    rw [← hLL a, h1, hLL]
  have hlamθ : lam * θ lam = 1 := by
    have h := hLL 1
    rw [hlamdef, hLθ] at h
    exact h
  have hθθ : ∀ a, θr (θr a) = a := by
    intro a
    have h := hLL a
    rw [hLθ a, hLθ, hθmul] at h
    change θ (θ a) = a
    calc θ (θ a) = (lam * θ lam) * θ (θ a) := by rw [hlamθ, one_mul]
      _ = a := by linear_combination h
  have hθK₀ : ∀ t, J.conj t = t → θ t = t := fun t ht =>
    InvField.apply_eq_self_of_involutive J.conj θr q (by omega) hcard hfixed hθθ ht
  have hcommL : ∀ a a', a' * J.conj a = a * J.conj a' →
      L a' * J.conj (L a) = L a * J.conj (L a') := by
    intro a a' h
    have h1 : sec a' * sec a = sec a * sec a' := by
      rw [UnitaryCoord.mul_comm_iff, hsec1, hsec1]
      exact h
    have h2 : ψ (sec a') * ψ (sec a) = ψ (sec a) * ψ (sec a') := by
      rw [← map_mul, ← map_mul, h1]
    have h3 := (UnitaryCoord.mul_comm_iff J (ψ (sec a)) (ψ (sec a'))).mp h2
    rw [hL (sec a), hL (sec a'), hsec1, hsec1] at h3
    exact h3
  have hN0 : lam * J.conj lam ≠ 0 := mul_ne_zero hlam0 ((map_ne_zero J.conj).mpr hlam0)
  have hθfix_maps : ∀ t, J.conj t = t → J.conj (θ t) = θ t := by
    intro t ht
    have h := hcommL 1 t (by rw [map_one, mul_one, one_mul, ht])
    simp only [hLθ, hθ1, mul_one, map_mul] at h
    have h2 : (lam * J.conj lam) * (θ t - J.conj (θ t)) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hN0
    · exact (sub_eq_zero.mp h3).symm
  have hθconj : ∀ x, J.conj (θ x) = θ (J.conj x) := by
    intro x
    have hTr : J.conj (x + J.conj x) = x + J.conj x := by rw [map_add, hσσ x, add_comm]
    have hNm : J.conj (x * J.conj x) = x * J.conj x := by rw [map_mul, hσσ x, mul_comm]
    have hroot : (J.conj (θ x)) ^ 2 - θ (x + J.conj x) * J.conj (θ x) + θ (x * J.conj x) = 0 := by
      have h0 : θ x ^ 2 - θ (x + J.conj x) * θ x + θ (x * J.conj x) = 0 := by
        have h1 : θr (x ^ 2 - (x + J.conj x) * x + x * J.conj x) = 0 := by
          have : x ^ 2 - (x + J.conj x) * x + x * J.conj x = 0 := by ring
          rw [this, map_zero]
        have e : θr (x ^ 2 - (x + J.conj x) * x + x * J.conj x) =
            θr x ^ 2 - θr (x + J.conj x) * θr x + θr (x * J.conj x) := by
          rw [map_add, map_sub, map_mul θr (x + J.conj x) x, map_pow]
        rw [e] at h1
        exact h1
      have h2 := congrArg J.conj h0
      rw [map_add, map_sub, map_mul, map_pow, hθfix_maps _ hTr, hθfix_maps _ hNm, map_zero] at h2
      exact h2
    have hfact : (J.conj (θ x) - θ x) * (J.conj (θ x) - θ (J.conj x)) = 0 := by
      have e : θ (x + J.conj x) = θ x + θ (J.conj x) := hθadd _ _
      have e' : θ (x * J.conj x) = θ x * θ (J.conj x) := hθmul _ _
      rw [e, e'] at hroot
      linear_combination hroot
    rcases mul_eq_zero.mp hfact with h1 | h1
    ·
      have hfixθ : J.conj (θ x) = θ x := sub_eq_zero.mp h1
      let F := {t : K // J.conj t = t}
      let θF : F → F := fun t => ⟨θ t, hθfix_maps t t.2⟩
      have hθFinj : Function.Injective θF := fun a b h =>
        Subtype.ext (hθinj (congrArg Subtype.val h))
      obtain ⟨t, ht⟩ := (Finite.injective_iff_surjective.mp hθFinj) ⟨θ x, hfixθ⟩
      have htx : (t : K) = x := hθinj (congrArg Subtype.val ht)
      have hx : J.conj x = x := by rw [← htx]; exact t.2
      rw [hx]
      exact hfixθ
    · exact sub_eq_zero.mp h1
  have hcenter : ∀ y : hermitianUnipotentCoord J, y.1.1 = 0 →
      (ψ y).1.1 = 0 ∧ (ψ y).1.2 = (lam * J.conj lam) * y.1.2 := by
    intro y hy
    refine ⟨hψcen y hy, ?_⟩
    have hyt : J.conj y.1.2 = y.1.2 := by
      have h := y.2
      rw [hy, map_zero, mul_zero, add_zero] at h
      exact (CharTwo.add_eq_zero.mp h).symm
    obtain ⟨u, hu⟩ := UnitaryCoord.exists_add_conj_eq J q hcard hfixed hyt
    have hsub : u - J.conj u = y.1.2 := by rw [CharTwo.sub_eq_add, hu]
    have hc : (sec u * sec 1)⁻¹ * (sec 1 * sec u) = y := by
      apply Subtype.ext
      apply Prod.ext
      · change ((sec u * sec 1)⁻¹ * (sec 1 * sec u)).1.1 = y.1.1
        rw [comm_fst, hy]
      · change ((sec u * sec 1)⁻¹ * (sec 1 * sec u)).1.2 = y.1.2
        rw [comm_snd, hsec1, hsec1, map_one, mul_one, one_mul, hsub]
    have e1 : ψ ((sec u * sec 1)⁻¹ * (sec 1 * sec u)) =
        (ψ (sec u) * ψ (sec 1))⁻¹ * (ψ (sec 1) * ψ (sec u)) := by
      simp only [map_mul, map_inv]
    have hψc : (ψ ((sec u * sec 1)⁻¹ * (sec 1 * sec u))).1.2 =
        (lam * J.conj lam) * (θ u - θ (J.conj u)) := by
      rw [e1, comm_snd, hL (sec u), hL (sec 1), hsec1, hsec1, hLθ u, hLθ 1, hθ1, mul_one, map_mul,
        hθconj]
      ring
    have hθsub : θ (u - J.conj u) = θ u - θ (J.conj u) := map_sub θr u (J.conj u)
    rw [hc] at hψc
    rw [hψc, ← hθsub, hsub, hθK₀ _ hyt]
  have hν : lam * J.conj lam = 1 := by
    have h1 := hcenter (zeroOne J) rfl
    have h2 := (hcenter (ψ (zeroOne J)) h1.1).2
    rw [hψψ, h1.2] at h2
    have h4 : (zeroOne J).1.2 = 1 := rfl
    rw [h4] at h2
    exact CharTwo.sq_injective (show (lam * J.conj lam) ^ 2 = 1 ^ 2 by linear_combination -h2)
  intro z hz
  obtain ⟨h1, h2⟩ := hcenter z hz
  apply Subtype.ext
  apply Prod.ext
  · change (ψ z).1.1 = z.1.1
    rw [h1, hz]
  · change (ψ z).1.2 = z.1.2
    rw [h2, hν, one_mul]

end UnitaryCoordAut

end Bender

end CFSG.ComponentClassification.AschbacherToolkit
