module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutUnitaryField

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Bender

namespace UnitaryCoordAut

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.ShultStronglyClosedTI

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

@[expose] def zeroOne (J : HermitianForm 3 K) : hermitianUnipotentCoord J :=
  ⟨(0, 1), by rw [map_one, CharTwo.add_self_eq_zero, map_zero, mul_zero, add_zero]⟩

omit [Finite K] [CharP K 2] in
theorem torusAction_fst (J : HermitianForm 3 K) (k : Kˣ) (z : hermitianUnipotentCoord J) :
    (hermitianTorusAction J k z).1.1 = z.1.1 * ((k : K) * (J.conj (k : K))⁻¹ ^ 2) := by
  rw [hermitianTorusAction_fst]
  ring

omit [Finite K] [CharP K 2] in
theorem torusAction_snd (J : HermitianForm 3 K) (k : Kˣ) (z : hermitianUnipotentCoord J) :
    (hermitianTorusAction J k z).1.2 = z.1.2 * ((J.conj (k : K))⁻¹ * (k : K)⁻¹) := by
  rw [hermitianTorusAction_snd]
  ring

omit [Finite K] [CharP K 2] in
theorem scalar_norm (J : HermitianForm 3 K) (k : Kˣ) :
    ((k : K) * (J.conj (k : K))⁻¹ ^ 2) * J.conj ((k : K) * (J.conj (k : K))⁻¹ ^ 2) =
      (J.conj (k : K))⁻¹ * (k : K)⁻¹ := by
  have h := unitaryCoverScalar_norm J k
  rw [unitaryCoverScalar_val] at h
  exact h

omit [Finite K] [CharP K 2] in
theorem scalar_of_fix (J : HermitianForm 3 K) {r : K} (hr : J.conj r = r) (hr0 : r ≠ 0) :
    ((Units.mk0 r hr0)⁻¹ : Kˣ) * (J.conj (((Units.mk0 r hr0)⁻¹ : Kˣ) : K))⁻¹ ^ 2 = r := by
  rw [Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, hr, inv_inv]
  field_simp

omit [CharP K 2] in
theorem exists_scalar_not_fix (J : HermitianForm 3 K) (q : ℕ) (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q) (hq : 4 ≤ q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    ∃ k : Kˣ, J.conj ((k : K) * (J.conj (k : K))⁻¹ ^ 2) ≠ (k : K) * (J.conj (k : K))⁻¹ ^ 2 := by
  classical
  by_contra hcon
  push Not at hcon
  have hScard := unitaryCoverScalarImage_card J q hcard hfixed hJ
  let g : unitaryCoverScalarImage J → {x : K // J.conj x = x ∧ x ≠ 0} := fun u =>
    ⟨((u : Kˣ) : K), by
      obtain ⟨k, hk⟩ := u.2
      rw [← hk, unitaryCoverScalar_val]
      exact ⟨hcon k, mul_ne_zero (Units.ne_zero k) (pow_ne_zero 2 (inv_ne_zero
        ((map_ne_zero J.conj).mpr (Units.ne_zero k))))⟩⟩
  have hg : Function.Injective g := by
    intro u v h
    apply Subtype.ext
    apply Units.ext
    exact congrArg Subtype.val h
  have hle := Nat.card_le_card_of_injective g hg
  have hF : Nat.card {x : K // J.conj x = x ∧ x ≠ 0} = q - 1 := by
    have h1 : Nat.card {x : K // J.conj x = x ∧ x ≠ 0} =
        ({x : K | J.conj x = x} \ {0} : Set K).ncard := by
      rw [← Nat.card_coe_set_eq]
      rfl
    rw [h1, Set.ncard_sdiff (by simp), Set.ncard_singleton, ← Nat.card_coe_set_eq]
    change Nat.card {x : K // J.conj x = x} - 1 = q - 1
    rw [hfixed]
  rw [hScard, hF] at hle
  set d := Nat.gcd 3 (q + 1) with hd
  have hdvd : d ∣ q ^ 2 - 1 := by
    rw [show q ^ 2 - 1 = (q + 1) * (q - 1) by simpa using Nat.sq_sub_sq q 1]
    exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right 3 (q + 1)) _
  have hdm : d * ((q ^ 2 - 1) / d) = q ^ 2 - 1 := Nat.mul_div_cancel' hdvd
  have hd3 : d ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 (q + 1))
  have h3 : q ^ 2 - 1 ≤ 3 * ((q ^ 2 - 1) / d) := by
    calc q ^ 2 - 1 = d * ((q ^ 2 - 1) / d) := hdm.symm
      _ ≤ 3 * ((q ^ 2 - 1) / d) := Nat.mul_le_mul_right _ hd3
  have hqq : q ^ 2 = q * q := sq q
  have h4 : 4 * q ≤ q * q := Nat.mul_le_mul_right q hq
  omega

theorem coordAut_form (J : HermitianForm 3 K) (q : ℕ) (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q) (hq : 4 ≤ q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (ψ : hermitianUnipotentCoord J →* hermitianUnipotentCoord J) (hψ : Function.Injective ψ)
    (hcen : ∀ z : hermitianUnipotentCoord J, z.1.1 = 0 → ψ z = z)
    (htor : ∀ k : Kˣ, ∃ k' : Kˣ,
      ∀ z, ψ (hermitianTorusAction J k z) = hermitianTorusAction J k' (ψ z)) :
    ∃ lam : K, lam * J.conj lam = 1 ∧
      ((∀ z, (ψ z).1.1 = lam * z.1.1 ∧ (ψ z).1.2 = z.1.2) ∨
        (∀ z, (ψ z).1.1 = lam * J.conj z.1.1 ∧ (ψ z).1.2 = z.1.2 + z.1.1 * J.conj z.1.1)) := by
  classical
  have hσσ := J.conj_involutive
  have hsurj := unitaryCoverFirstCoord_surjective J q hcard hfixed hJ
  choose sec hsec using fun a : K => hsurj (Multiplicative.ofAdd a)
  have hsec1 : ∀ a, (sec a).1.1 = a := fun a => congrArg Multiplicative.toAdd (hsec a)
  have hfib : ∀ z z' : hermitianUnipotentCoord J, z.1.1 = z'.1.1 →
      (ψ z').1.1 = (ψ z).1.1 ∧ (ψ z').1.2 = (ψ z).1.2 + (z'.1.2 - z.1.2) := by
    intro z z' h
    set c := z⁻¹ * z' with hcdef
    have hc1 : c.1.1 = 0 := by
      change -z.1.1 + z'.1.1 = 0
      rw [h]
      ring
    have hc2 : c.1.2 = z'.1.2 - z.1.2 := by
      change J.conj z.1.2 + z'.1.2 - -z.1.1 * J.conj z'.1.1 = _
      rw [← h]
      linear_combination z.2
    have hz' : ψ z' = ψ z * c := by
      rw [← hcen c hc1, ← map_mul, hcdef, mul_inv_cancel_left]
    rw [hz']
    constructor
    · change (ψ z).1.1 + c.1.1 = _
      rw [hc1, add_zero]
    · change (ψ z).1.2 + c.1.2 - (ψ z).1.1 * J.conj c.1.1 = _
      rw [hc1, hc2, map_zero, mul_zero, sub_zero]
  set L : K → K := fun a => (ψ (sec a)).1.1 with hLdef
  set γ : K → K := fun a => (ψ (sec a)).1.2 - (sec a).1.2 with hγdef
  have hL : ∀ z, (ψ z).1.1 = L z.1.1 := fun z =>
    (hfib (sec z.1.1) z (hsec1 _)).1
  have hγ : ∀ z, (ψ z).1.2 = z.1.2 + γ z.1.1 := by
    intro z
    rw [(hfib (sec z.1.1) z (hsec1 _)).2]
    simp only [hγdef]
    ring
  have hLzero : ∀ a, L a = 0 → a = 0 := by
    intro a ha
    have h1 : ψ (ψ (sec a)) = ψ (sec a) := hcen _ ha
    have h2 := hψ h1
    have h3 : (ψ (sec a)).1.1 = a := by rw [h2, hsec1]
    rw [← h3]
    exact ha
  have hprod : ∀ a a', L (a + a') = L a + L a' ∧
      γ (a + a') - a * J.conj a' = γ a + γ a' - L a * J.conj (L a') := by
    intro a a'
    have h := map_mul ψ (sec a) (sec a')
    have e1 : (sec a * sec a').1.1 = a + a' := by
      change (sec a).1.1 + (sec a').1.1 = _
      rw [hsec1, hsec1]
    have e2 : (sec a * sec a').1.2 = (sec a).1.2 + (sec a').1.2 - a * J.conj a' := by
      change (sec a).1.2 + (sec a').1.2 - (sec a).1.1 * J.conj (sec a').1.1 = _
      rw [hsec1, hsec1]
    have f1 := congrArg (fun v : hermitianUnipotentCoord J => v.1.1) h
    have f2 := congrArg (fun v : hermitianUnipotentCoord J => v.1.2) h
    change (ψ (sec a * sec a')).1.1 = (ψ (sec a)).1.1 + (ψ (sec a')).1.1 at f1
    change (ψ (sec a * sec a')).1.2 = (ψ (sec a)).1.2 + (ψ (sec a')).1.2 -
      (ψ (sec a)).1.1 * J.conj (ψ (sec a')).1.1 at f2
    rw [hL, hL, hL, e1, hsec1, hsec1] at f1
    rw [hγ, hγ, hγ, hL, hL, e1, e2, hsec1, hsec1] at f2
    exact ⟨f1, by linear_combination f2⟩
  have hL0 : L 0 = 0 := by
    have h := (hprod 0 0).1
    rw [add_zero] at h
    linear_combination -h
  have hLneg : ∀ a, L (-a) = -L a := by
    intro a
    have h := (hprod a (-a)).1
    rw [add_neg_cancel, hL0] at h
    linear_combination -h
  have hLinj : Function.Injective L := by
    intro a b h
    have h1 : L (a + -b) = 0 := by rw [(hprod a (-b)).1, hLneg, h, add_neg_cancel]
    have := hLzero _ h1
    linear_combination this
  choose kk hkk using htor
  set sc : Kˣ → K := fun k => (k : K) * (J.conj (k : K))⁻¹ ^ 2 with hscdef
  set nc : Kˣ → K := fun k => (J.conj (k : K))⁻¹ * (k : K)⁻¹ with hncdef
  have hnc : ∀ k, nc (kk k) = nc k := by
    intro k
    have h := hkk k (zeroOne J)
    rw [hcen (zeroOne J) rfl, hcen (hermitianTorusAction J k (zeroOne J)) (by
      rw [torusAction_fst]
      change (0 : K) * _ = 0
      rw [zero_mul])] at h
    have h2 := congrArg (fun v : hermitianUnipotentCoord J => v.1.2) h
    simp only [torusAction_snd] at h2
    change (1 : K) * nc k = 1 * nc (kk k) at h2
    rw [one_mul, one_mul] at h2
    exact h2.symm
  have hLs : ∀ k a, L (a * sc k) = L a * sc (kk k) := by
    intro k a
    have h := congrArg (fun v : hermitianUnipotentCoord J => v.1.1) (hkk k (sec a))
    simp only [hL, torusAction_fst, hsec1] at h
    exact h
  have hγs : ∀ k a, γ (a * sc k) = nc k * γ a := by
    intro k a
    have h := congrArg (fun v : hermitianUnipotentCoord J => v.1.2) (hkk k (sec a))
    simp only [hγ, torusAction_snd, torusAction_fst, hsec1] at h
    change (sec a).1.2 * nc k + γ (a * sc k) = ((sec a).1.2 + γ a) * nc (kk k) at h
    rw [hnc] at h
    linear_combination h
  obtain ⟨lam, hlamdef⟩ : ∃ lam, L 1 = lam := ⟨_, rfl⟩
  have hlam0 : lam ≠ 0 := fun h => one_ne_zero (hLzero 1 (hlamdef.trans h))
  set θ : K → K := fun a => L a * lam⁻¹ with hθdef
  have hθ1 : θ 1 = 1 := by simp only [hθdef, hlamdef]; exact mul_inv_cancel₀ hlam0
  have hθadd : ∀ a a', θ (a + a') = θ a + θ a' := by
    intro a a'
    simp only [hθdef, (hprod a a').1]
    ring
  have hθs : ∀ k a, θ (a * sc k) = θ a * θ (sc k) := by
    intro k a
    have h1 := hLs k a
    have h2 := hLs k 1
    rw [one_mul, hlamdef] at h2
    simp only [hθdef, h1, h2]
    field_simp
  have hfixsc : ∀ r : K, J.conj r = r → r ≠ 0 → ∃ k : Kˣ, sc k = r ∧ nc k = r * J.conj r := by
    intro r hr hr0
    refine ⟨(Units.mk0 r hr0)⁻¹, scalar_of_fix J hr hr0, ?_⟩
    simp only [hncdef, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, hr, inv_inv]
  have hθr : ∀ r : K, J.conj r = r → ∀ a, θ (a * r) = θ a * θ r := by
    intro r hr a
    by_cases hr0 : r = 0
    · simp only [hθdef, hr0, mul_zero, hL0, zero_mul]
    · obtain ⟨k, hk, -⟩ := hfixsc r hr hr0
      rw [← hk]
      exact hθs k a
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
  have hθinj : Function.Injective θ := by
    intro a b h
    apply hLinj
    simp only [hθdef] at h
    exact mul_right_cancel₀ (inv_ne_zero hlam0) h
  have hLθ : ∀ a, L a = lam * θ a := by
    intro a
    simp only [hθdef]
    field_simp

  have hcomm : ∀ a a', L a' * J.conj (L a) - L a * J.conj (L a') =
      a' * J.conj a - a * J.conj a' := by
    intro a a'
    have h1 := (hprod a a').2
    have h2 := (hprod a' a).2
    rw [add_comm a' a] at h2
    linear_combination h2 - h1
  have hN0 : lam * J.conj lam ≠ 0 := mul_ne_zero hlam0 ((map_ne_zero J.conj).mpr hlam0)
  have hθfix_maps : ∀ t, J.conj t = t → J.conj (θ t) = θ t := by
    intro t ht
    have h := hcomm 1 t
    simp only [hLθ, hθ1, ht, map_one, mul_one, one_mul, map_mul] at h
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
  have hNθ : ∀ t, J.conj t = t → (lam * J.conj lam) * θ t = t := by
    intro t ht
    obtain ⟨u, hu⟩ := UnitaryCoord.exists_add_conj_eq J q hcard hfixed ht
    have h := hcomm 1 u
    have e1 : L u = lam * θ u := hLθ u
    have e2 : L 1 = lam := hlamdef
    have e3 : J.conj (lam * θ u) = J.conj lam * θ (J.conj u) := by rw [map_mul, hθconj]
    simp only [e1, e2, e3, map_one, mul_one, one_mul] at h
    have hsub : u - J.conj u = t := by rw [CharTwo.sub_eq_add, hu]
    have hθsub : θ t = θ u - θ (J.conj u) := by rw [← hsub]; exact map_sub θr u (J.conj u)
    linear_combination h + (lam * J.conj lam) * hθsub + hsub
  have hNlam : lam * J.conj lam = 1 := by
    have := hNθ 1 (map_one _)
    rwa [hθ1, mul_one] at this
  have hθfix : ∀ t, J.conj t = t → θ t = t := by
    intro t ht
    have := hNθ t ht
    rwa [hNlam, one_mul] at this
  have hγfix : ∀ a, J.conj (γ a) = γ a := by
    intro a
    have h1 := (ψ (sec a)).2
    have h2 := (sec a).2
    rw [hγ, hL, hsec1] at h1
    rw [hsec1] at h2
    have hLL : L a * J.conj (L a) = a * J.conj a := by
      have hNa : J.conj (a * J.conj a) = a * J.conj a := by rw [map_mul, hσσ a, mul_comm]
      rw [hLθ, map_mul, hθconj]
      have : lam * θ a * (J.conj lam * θ (J.conj a)) =
          (lam * J.conj lam) * θ (a * J.conj a) := by
        rw [hθmul]
        ring
      rw [this, hNlam, one_mul]
      exact hθfix _ hNa
    rw [map_add] at h1
    have h3 : γ a + J.conj (γ a) = 0 := by linear_combination h1 - h2 - hLL
    exact (CharTwo.add_eq_zero.mp h3).symm
  have hγ0 : γ 0 = 0 := by
    have h := hcen (sec 0) (hsec1 0)
    simp only [hγdef, h, sub_self]
  have hSfix : ∀ r : K, J.conj r = r → r ≠ 0 → r ∈ Set.range sc := by
    intro r hr hr0
    obtain ⟨k, hk, -⟩ := hfixsc r hr hr0
    exact ⟨k, hk⟩
  have hncsc : ∀ k, nc k = sc k * J.conj (sc k) := fun k => (scalar_norm J k).symm
  rcases UnitaryField.eq_id_or_eq_conj_of_fix J.conj hσσ θr hθfix with hid | hconj
  ·
    have hγadd : ∀ a a', γ (a + a') = γ a + γ a' := by
      intro a a'
      have h := (hprod a a').2
      rw [hLθ, hLθ, show θ a = a from hid a, show θ a' = a' from hid a', map_mul] at h
      linear_combination h - a * J.conj a' * hNlam
    let κ : K →+ K :=
      { toFun := γ
        map_zero' := hγ0
        map_add' := hγadd }
    have hκ0 := UnitaryField.additive_eq_zero J.conj q hcard hfixed (Set.range sc) hSfix
      ⟨k₀, rfl⟩ hk₀ κ hγfix (by
        rintro _ ⟨k, rfl⟩ x
        change γ (x * sc k) = sc k * J.conj (sc k) * γ x
        rw [hγs, hncsc])
    refine ⟨lam, hNlam, Or.inl fun z => ⟨?_, ?_⟩⟩
    · rw [hL, hLθ, show θ z.1.1 = z.1.1 from hid _]
    · rw [hγ, show γ z.1.1 = 0 from hκ0 _, add_zero]
  ·
    have hκadd : ∀ a a', γ (a + a') - (a + a') * J.conj (a + a') =
        (γ a - a * J.conj a) + (γ a' - a' * J.conj a') := by
      intro a a'
      have h := (hprod a a').2
      rw [hLθ, hLθ, show θ a = J.conj a from hconj a, show θ a' = J.conj a' from hconj a',
        map_mul, hσσ a'] at h
      have h2 := CharTwo.add_self_eq_zero (J.conj a * a')
      rw [map_add]
      linear_combination h - J.conj a * a' * hNlam - h2
    let κ : K →+ K :=
      { toFun := fun x => γ x - x * J.conj x
        map_zero' := by simp only [hγ0, zero_mul, sub_zero]
        map_add' := hκadd }
    have hκfix : ∀ x, J.conj (κ x) = κ x := by
      intro x
      change J.conj (γ x - x * J.conj x) = γ x - x * J.conj x
      rw [map_sub, hγfix, map_mul, hσσ x, mul_comm (J.conj x)]
    have hκ0 := UnitaryField.additive_eq_zero J.conj q hcard hfixed (Set.range sc) hSfix
      ⟨k₀, rfl⟩ hk₀ κ hκfix (by
        rintro _ ⟨k, rfl⟩ x
        change γ (x * sc k) - x * sc k * J.conj (x * sc k) =
          sc k * J.conj (sc k) * (γ x - x * J.conj x)
        rw [hγs, hncsc, map_mul J.conj x (sc k)]
        ring)
    refine ⟨lam, hNlam, Or.inr fun z => ⟨?_, ?_⟩⟩
    · rw [hL, hLθ, show θ z.1.1 = J.conj z.1.1 from hconj _]
    · have h := hκ0 z.1.1
      change γ z.1.1 - z.1.1 * J.conj z.1.1 = 0 at h
      rw [hγ, sub_eq_zero.mp h]

end UnitaryCoordAut

end Bender

end CFSG.ComponentClassification.AschbacherToolkit
