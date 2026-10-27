module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big22
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big23

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W CFSG.GorensteinWalter
open CFSG.Blueprint

section Order

variable {F : Type} [Field F] [Finite F]

theorem autU_pow_eq {ψ : F ≃+* F} {s : ℕ} (hs : ∀ x : F, ψ x = x ^ s) (x : Fˣ) (j : ℕ) :
    autU (ψ ^ j) x = x ^ s ^ j := by
  induction j with
  | zero => rw [pow_zero, autU_one_aut, pow_zero, pow_one]
  | succ j ih =>
      rw [pow_succ', autU_comp, ih, autU_eq_pow hs, ← pow_mul, mul_comm, pow_succ']

theorem nrm_pow_eq {ψ : F ≃+* F} {s : ℕ} (hs : ∀ x : F, ψ x = x ^ s) (ξ : Fˣ) (k n : ℕ) :
    nrm (ψ ^ k) ξ n = ξ ^ ∑ i ∈ Finset.range n, (s ^ k) ^ i := by
  unfold nrm
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl ?_
  intro i _
  rw [← pow_mul, autU_pow_eq hs, pow_mul]

theorem isSquare_autU_iff (σ : F ≃+* F) (v : Fˣ) : IsSquare (autU σ v) ↔ IsSquare v := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨autU σ⁻¹ z, ?_⟩
    rw [← autU_mul, ← hz, autU_inv_aut]
  · rintro ⟨z, rfl⟩
    exact ⟨autU σ z, autU_mul σ z z⟩

theorem gD_pow_ne_one {ξ : Fˣ} {r : ℕ} (hξ : orderOf ξ = 2 ^ r) {ψ : F ≃+* F} {e s : ℕ}
    (he : 1 ≤ e) (hψ : ψ ^ 2 ^ e = 1) (hs : ∀ x : F, ψ x = x ^ s) (hodd : Odd s)
    (harith : s ^ 2 ^ e % 2 ^ (r + 1) = 2 ^ r + 1) (k : ℕ) :
    (gD ξ (ψ ^ k)) ^ 2 ^ e ≠ 1 := by
  intro h
  rw [gD_pow] at h
  have hψk : (ψ ^ k) ^ 2 ^ e = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hψ, one_pow]
  rw [hψk, ← gD_one_one] at h
  have h1 : nrm (ψ ^ k) ξ (2 ^ e) = 1 := (gD_eq_iff.mp h).1
  rw [nrm_pow_eq hs] at h1
  have hdvd : 2 ^ r ∣ ∑ i ∈ Finset.range (2 ^ e), (s ^ k) ^ i := by
    rw [← hξ]
    exact orderOf_dvd_of_pow_eq_one h1
  exact not_two_pow_dvd_geom_sum hodd he harith k hdvd

theorem not_isSquare_of_orderOf (h2 : (2 : F) ≠ 0) {ξ : Fˣ} {r : ℕ} (hξ : orderOf ξ = 2 ^ r)
    (hc2 : ¬ 2 ^ (r + 1) ∣ Nat.card Fˣ) : ¬ IsSquare ξ := by
  intro hsq
  have hpow : ξ ^ (Nat.card Fˣ / 2) = 1 := (isSquare_iff_pow_eq_one h2 ξ).mp hsq
  have hdvd : 2 ^ r ∣ Nat.card Fˣ / 2 := by
    rw [← hξ]
    exact orderOf_dvd_of_pow_eq_one hpow
  have h2dvd : 2 ∣ Nat.card Fˣ := by
    have h := orderOf_dvd_natCard (-1 : Fˣ)
    rwa [orderOf_units_neg_one h2] at h
  obtain ⟨m, hm⟩ := h2dvd
  have hdiv : Nat.card Fˣ / 2 = m := by
    rw [hm, Nat.mul_div_cancel_left m (by norm_num : (0 : ℕ) < 2)]
  rw [hdiv] at hdvd
  apply hc2
  rw [hm, show 2 ^ (r + 1) = 2 * 2 ^ r by rw [pow_succ]; ring]
  exact Nat.mul_dvd_mul_left 2 hdvd

theorem isSquare_mul_square_iff {G : Type*} [CommGroup G] (u t : G) :
    IsSquare (u * (t * t)) ↔ IsSquare u := by
  constructor
  · intro h
    have := IsSquare.mul h (IsSquare.inv (show IsSquare (t * t) from ⟨t, rfl⟩))
    rwa [show u * (t * t) * (t * t)⁻¹ = u by group] at this
  · intro h
    exact IsSquare.mul h ⟨t, rfl⟩

theorem isSquare_pow_iff_even {G : Type*} [CommGroup G] {ξ : G} (hξ : ¬ IsSquare ξ) (n : ℕ) :
    IsSquare (ξ ^ n) ↔ Even n := by
  constructor
  · intro h
    rcases Nat.even_or_odd n with hn | hn
    · exact hn
    · exfalso
      obtain ⟨m, rfl⟩ := hn
      have heq : ξ = ξ ^ (2 * m + 1) * ((ξ ^ m)⁻¹ * (ξ ^ m)⁻¹) := by group
      have hs : IsSquare (ξ ^ (2 * m + 1) * ((ξ ^ m)⁻¹ * (ξ ^ m)⁻¹)) :=
        (isSquare_mul_square_iff (ξ ^ (2 * m + 1)) ((ξ ^ m)⁻¹)).mpr h
      rw [← heq] at hs
      exact hξ hs
  · intro hn
    exact Even.isSquare_pow hn ξ

theorem isSquare_inv_pow_mul_self_iff {G : Type*} [CommGroup G] {ξ : G} (hξ : ¬ IsSquare ξ)
    (a : ℕ) : IsSquare ((ξ ^ a)⁻¹ * ξ) ↔ Odd a := by
  have hiff : IsSquare (ξ ^ (a + 1)) ↔ IsSquare ((ξ ^ a)⁻¹ * ξ) := by
    rw [show ξ ^ (a + 1) = (ξ ^ a)⁻¹ * ξ * (ξ ^ a * ξ ^ a) by group]
    exact isSquare_mul_square_iff _ _
  rw [← hiff, isSquare_pow_iff_even hξ (a + 1), Nat.even_add_one, Nat.not_even_iff_odd]

theorem not_isSquare_inv_pow_mul_self_of_even {G : Type*} [CommGroup G] {ξ : G}
    (hξ : ¬ IsSquare ξ) {a : ℕ} (ha : Even a) : ¬ IsSquare ((ξ ^ a)⁻¹ * ξ) := by
  rw [isSquare_inv_pow_mul_self_iff hξ a]
  exact Nat.not_odd_iff_even.mpr ha

theorem isSquare_inv_pow_mul_self_of_odd {G : Type*} [CommGroup G] {ξ : G}
    (hξ : ¬ IsSquare ξ) {a : ℕ} (ha : Odd a) : IsSquare ((ξ ^ a)⁻¹ * ξ) :=
  (isSquare_inv_pow_mul_self_iff hξ a).mpr ha

theorem exists_nat_pow_eq_of_mem_zpowers (ξ w : Fˣ) (hw : w ∈ Subgroup.zpowers ξ) :
    ∃ a : ℕ, w = ξ ^ a := by
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff w ξ).mp
    ((IsOfFinOrder.mem_powers_iff_mem_zpowers (isOfFinOrder_of_finite ξ)).mpr hw)
  exact ⟨n, hn.symm⟩

theorem exists_nat_pow_eq_of_mem_zpowers_of_orderOf (ψ σ : F ≃+* F) {e : ℕ}
    (hψo : orderOf ψ = 2 ^ e) (hσ : σ ∈ Subgroup.zpowers ψ) : ∃ b : ℕ, σ = ψ ^ b := by
  have hfin : IsOfFinOrder ψ := by
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨2 ^ e, pow_pos (by norm_num) e, by rw [← hψo]; exact pow_orderOf_eq_one ψ⟩
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff σ ψ).mp
    ((IsOfFinOrder.mem_powers_iff_mem_zpowers hfin).mpr hσ)
  exact ⟨n, hn.symm⟩

theorem gD_inv_mul_gD (w x : Fˣ) (σ τ : F ≃+* F) :
    (gD w σ)⁻¹ * gD x τ = gD (autU σ⁻¹ (w⁻¹ * x)) (σ⁻¹ * τ) := by
  rw [gD_inv, gD_mul_gD, autU_mul, autU_inv]

theorem gA_inv_mul_gD (w x : Fˣ) (σ τ : F ≃+* F) :
    (gA w σ)⁻¹ * gD x τ = gA (autU σ⁻¹ (w * x⁻¹)) (σ⁻¹ * τ) := by
  rw [gA_inv, gA_mul_gD, autU_mul, autU_inv]

theorem gA_inv_mem_of_gD_mem (v : Fˣ) (τ : F ≃+* F) (N : Subgroup (PGammaL2 F))
    (hN3 : gA (1 : Fˣ) 1 ∈ N) (h : gD v τ ∈ N) : gA v⁻¹ τ ∈ N := by
  have hmem : gA (1 : Fˣ) 1 * gA v⁻¹ τ ∈ N := by
    rw [gA_mul_gA, autU_one_aut, one_mul, inv_inv]
    exact h
  rw [show gA v⁻¹ τ = (gA (1 : Fˣ) 1)⁻¹ * (gA (1 : Fˣ) 1 * gA v⁻¹ τ) by group]
  exact N.mul_mem (N.inv_mem hN3) hmem

theorem exists_good_k {ξ : Fˣ} {ψ σ₀ : F ≃+* F} {e : ℕ} (he : 1 ≤ e) (hψo : orderOf ψ = 2 ^ e)
    (hσ₀ : ψ ^ 2 ^ (e - 1) = σ₀) (hξ : ¬ IsSquare ξ) (N : Subgroup (PGammaL2 F))
    (hN1 : ∀ v : Fˣ, IsSquare v → gD v 1 ∈ N) (hN2 : ∀ v : Fˣ, ¬ IsSquare v → gD v σ₀ ∈ N)
    (hN3 : gA (1 : Fˣ) 1 ∈ N) {y : PGammaL2 F} (hy : y ∈ stdSylow ξ ψ) :
    ∃ k : ℕ, y⁻¹ * gD ξ (ψ ^ k) ∈ N := by
  obtain ⟨σ, hσ, w, hw, hyD | hyA⟩ := mem_stdSylow_iff.mp hy
  · rw [hyD]
    obtain ⟨b, hb⟩ := exists_nat_pow_eq_of_mem_zpowers_of_orderOf ψ σ hψo hσ
    subst hb
    obtain ⟨a, ha⟩ := exists_nat_pow_eq_of_mem_zpowers ξ w hw
    subst ha
    by_cases heven : Even a
    · refine ⟨b + 2 ^ (e - 1), ?_⟩
      rw [gD_inv_mul_gD]
      have hbc : (ψ ^ b)⁻¹ * ψ ^ (b + 2 ^ (e - 1)) = σ₀ := by
        rw [pow_add, ← mul_assoc, inv_mul_cancel, one_mul, hσ₀]
      rw [hbc]
      refine hN2 _ ?_
      rw [isSquare_autU_iff]
      exact not_isSquare_inv_pow_mul_self_of_even hξ heven
    · have hodd_a : Odd a := Nat.not_even_iff_odd.mp heven
      refine ⟨b, ?_⟩
      rw [gD_inv_mul_gD]
      have hbc : (ψ ^ b)⁻¹ * ψ ^ b = 1 := inv_mul_cancel _
      rw [hbc]
      refine hN1 _ ?_
      rw [isSquare_autU_iff]
      exact isSquare_inv_pow_mul_self_of_odd hξ hodd_a
  · rw [hyA]
    obtain ⟨b, hb⟩ := exists_nat_pow_eq_of_mem_zpowers_of_orderOf ψ σ hψo hσ
    subst hb
    obtain ⟨a, ha⟩ := exists_nat_pow_eq_of_mem_zpowers ξ w hw
    subst ha
    have hv : autU (ψ ^ b)⁻¹ ((ξ ^ a) * ξ⁻¹) =
        (autU (ψ ^ b)⁻¹ ((ξ ^ a)⁻¹ * ξ))⁻¹ := by
      rw [← autU_inv]
      congr 1
      group
    by_cases heven : Even a
    · refine ⟨b + 2 ^ (e - 1), ?_⟩
      rw [gA_inv_mul_gD]
      have hbc : (ψ ^ b)⁻¹ * ψ ^ (b + 2 ^ (e - 1)) = σ₀ := by
        rw [pow_add, ← mul_assoc, inv_mul_cancel, one_mul, hσ₀]
      rw [hbc, hv]
      exact gA_inv_mem_of_gD_mem _ σ₀ N hN3 (hN2 _ (by
        rw [isSquare_autU_iff]
        exact not_isSquare_inv_pow_mul_self_of_even hξ heven))
    · have hodd_a : Odd a := Nat.not_even_iff_odd.mp heven
      refine ⟨b, ?_⟩
      rw [gA_inv_mul_gD]
      have hbc : (ψ ^ b)⁻¹ * ψ ^ b = 1 := inv_mul_cancel _
      rw [hbc, hv]
      exact gA_inv_mem_of_gD_mem _ 1 N hN3 (hN1 _ (by
        rw [isSquare_autU_iff]
        exact isSquare_inv_pow_mul_self_of_odd hξ hodd_a))

theorem exists_large_order_in_coset (h2 : (2 : F) ≠ 0) {ξ : Fˣ} {r : ℕ}
    (hξ : orderOf ξ = 2 ^ r) (hc2 : ¬ 2 ^ (r + 1) ∣ Nat.card Fˣ) {ψ σ₀ : F ≃+* F} {e s : ℕ}
    (he : 1 ≤ e) (hψo : orderOf ψ = 2 ^ e) (hs : ∀ x : F, ψ x = x ^ s) (hodd : Odd s)
    (harith : s ^ 2 ^ e % 2 ^ (r + 1) = 2 ^ r + 1) (hσ₀ : ψ ^ 2 ^ (e - 1) = σ₀)
    (N : Subgroup (PGammaL2 F)) (hN1 : ∀ v : Fˣ, IsSquare v → gD v 1 ∈ N)
    (hN2 : ∀ v : Fˣ, ¬ IsSquare v → gD v σ₀ ∈ N) (hN3 : gA (1 : Fˣ) 1 ∈ N) {y : PGammaL2 F}
    (hy : y ∈ stdSylow ξ ψ) :
    ∃ ζ ∈ stdSylow ξ ψ, y⁻¹ * ζ ∈ N ∧ 2 ^ e < orderOf ζ := by
  have hξns : ¬ IsSquare ξ := not_isSquare_of_orderOf h2 hξ hc2
  obtain ⟨k, hk⟩ := exists_good_k he hψo hσ₀ hξns N hN1 hN2 hN3 hy
  have hξpow : ξ ^ 2 ^ r = 1 := by rw [← hξ]; exact pow_orderOf_eq_one ξ
  have hψpow : ψ ^ 2 ^ e = 1 := by rw [← hψo]; exact pow_orderOf_eq_one ψ
  have hzmem : gD ξ (ψ ^ k) ∈ stdSylow ξ ψ :=
    gD_mem_stdSylow (Subgroup.pow_mem _ (Subgroup.mem_zpowers ψ) k) (Subgroup.mem_zpowers ξ)
  refine ⟨gD ξ (ψ ^ k), hzmem, hk, ?_⟩
  have hP : IsPGroup 2 ↥(stdSylow ξ ψ) := isPGroup_stdSylow hξpow hψpow
  obtain ⟨m, hm⟩ := hP ⟨gD ξ (ψ ^ k), hzmem⟩
  have hm' : (gD ξ (ψ ^ k)) ^ 2 ^ m = 1 := by simpa using hm
  have hdvd : orderOf (gD ξ (ψ ^ k)) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm'
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hje : e < j := by
    by_contra hcon
    have hle : j ≤ e := by omega
    have hdvd2 : 2 ^ j ∣ 2 ^ e := Nat.pow_dvd_pow 2 hle
    have hdvd3 : orderOf (gD ξ (ψ ^ k)) ∣ 2 ^ e := hjeq ▸ hdvd2
    have hone : (gD ξ (ψ ^ k)) ^ 2 ^ e = 1 := (orderOf_dvd_iff_pow_eq_one).mp hdvd3
    exact gD_pow_ne_one hξ he hψpow hs hodd harith k hone
  calc 2 ^ e < 2 ^ j := Nat.pow_lt_pow_right (by norm_num) hje
    _ = orderOf (gD ξ (ψ ^ k)) := hjeq.symm

end Order

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
