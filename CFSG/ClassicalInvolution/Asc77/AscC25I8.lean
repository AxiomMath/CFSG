module

public import CFSG.ClassicalInvolution.Asc77.AscC25V37
public import CFSG.ClassicalInvolution.Asc77.AscFusionR9
public import CFSG.ClassicalInvolution.Asc77.ModOApi
public import CFSG.ClassicalInvolution.Asc77.AscFusionR7

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25I

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.C25V CFSG.ClassicalInvolution.Asc77

section Abstract

variable {X : Type} [Group X] [Finite X] (O : Subgroup X) [O.Normal]

theorem isPGroup_zpowers_of_sq {u : X} (hu : u * u = 1) : IsPGroup 2 (Subgroup.zpowers u) := by
  have h1 : orderOf u ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two]; exact hu)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers]; exact hk)

theorem isPGroup_zpowers_of_orderOf_four {u : X} (hu : orderOf u = 4) :
    IsPGroup 2 (Subgroup.zpowers u) :=
  IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hu]; norm_num)

theorem exists_involution_lift (hO : Odd (Nat.card O)) {ζ : X} (hζ : ζ * ζ = 1)
    {s : X ⧸ O} (hs2 : s * s = 1) (hsζ : s * QuotientGroup.mk ζ = QuotientGroup.mk ζ * s) :
    ∃ t₀ : X, (QuotientGroup.mk t₀ : X ⧸ O) = s ∧ t₀ * t₀ = 1 ∧ t₀ * ζ = ζ * t₀ := by
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective s
  have hx : (QuotientGroup.mk (ζ * x₀ * ζ⁻¹) : X ⧸ O) = QuotientGroup.mk x₀ := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [mul_inv_eq_iff_eq_mul]
    exact hsζ.symm
  obtain ⟨t, ht, htζ⟩ := exists_fixed_lift O hO hζ hx
  set n := Nat.card O with hn
  have htζ' : t * ζ = ζ * t := by
    have : ζ * t = t * ζ := by
      rw [mul_inv_eq_iff_eq_mul] at htζ
      exact htζ
    exact this.symm
  have htt : t * t ∈ O := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ht]
    exact hs2
  have hpow : (t * t) ^ n = 1 := by
    have := pow_card_eq_one' (G := O) (x := ⟨t * t, htt⟩)
    exact congrArg Subtype.val this
  refine ⟨t ^ n, ?_, ?_, (Commute.pow_left (show Commute t ζ from htζ') n).eq⟩
  · rw [QuotientGroup.mk_pow, ht]
    obtain ⟨j, hj⟩ := hO
    rw [hj, pow_succ, pow_mul, sq, hs2, one_pow, one_mul]
  · rw [← (Commute.refl t).mul_pow]
    exact hpow

theorem mem_normalizer_of_normal (u : X) : u ∈ Subgroup.normalizer (O : Set X) := by
  rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
  exact Subgroup.mem_top _

theorem exists_conj_lift (hO : Odd (Nat.card O)) {ζ t₀ : X} (hζ : ζ * ζ = 1) (ht₀ : t₀ * t₀ = 1)
    {x : X ⧸ O} (hx : (QuotientGroup.mk t₀ : X ⧸ O) = x * QuotientGroup.mk ζ * x⁻¹) :
    ∃ c : X, c * ζ * c⁻¹ = t₀ := by
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective x
  set u : X := x₀ * ζ * x₀⁻¹ with hu
  have hu2 : u * u = 1 := by
    calc u * u = x₀ * (ζ * ζ) * x₀⁻¹ := by rw [hu]; group
      _ = 1 := by rw [hζ]; group
  have hxy : u⁻¹ * t₀ ∈ O := by
    rw [← QuotientGroup.eq, hx, hu, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv]
  obtain ⟨h, -, hh⟩ := AscFusion.exists_conj_of_odd_coset hO (isPGroup_zpowers_of_sq hu2)
    (isPGroup_zpowers_of_sq ht₀) (mem_normalizer_of_normal O u) hxy
  exact ⟨h * x₀, by rw [← hh, hu]; group⟩

theorem order_four_pow (hO : Odd (Nat.card O)) {yb : X ⧸ O} (hyb4 : orderOf yb = 4) {g : X}
    (hg : (QuotientGroup.mk g : X ⧸ O) = yb) :
    (QuotientGroup.mk (g ^ (Nat.card O * Nat.card O)) : X ⧸ O) = yb ∧
      orderOf (g ^ (Nat.card O * Nat.card O)) = 4 := by
  set n := Nat.card O with hn
  have hodd : n % 2 = 1 := Nat.odd_iff.mp hO
  have he : (n * n) % 4 = 1 := by
    have : n % 4 = 1 ∨ n % 4 = 3 := by omega
    rcases this with h | h <;> simp [Nat.mul_mod, h]
  have h4 : yb ^ 4 = 1 := by rw [← hyb4]; exact pow_orderOf_eq_one yb
  obtain ⟨q, hq⟩ : ∃ q, n * n = 4 * q + 1 := ⟨(n * n) / 4, by omega⟩
  have hmk : (QuotientGroup.mk (g ^ (n * n)) : X ⧸ O) = yb := by
    rw [QuotientGroup.mk_pow, hg, hq, pow_succ, pow_mul, h4, one_pow, one_mul]
  refine ⟨hmk, ?_⟩
  have hg4 : g ^ 4 ∈ O := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hg]
    exact h4
  have hg4n : (g ^ 4) ^ n = 1 := by
    have := pow_card_eq_one' (G := O) (x := ⟨g ^ 4, hg4⟩)
    exact congrArg Subtype.val this
  have hpow4 : (g ^ (n * n)) ^ 4 = 1 := by
    calc (g ^ (n * n)) ^ 4 = ((g ^ 4) ^ n) ^ n := by
          rw [← pow_mul, ← pow_mul, ← pow_mul]
          congr 1
          ring
      _ = 1 := by rw [hg4n, one_pow]
  have hd1 : orderOf (g ^ (n * n)) ∣ 4 := orderOf_dvd_of_pow_eq_one hpow4
  have hd2 : orderOf (QuotientGroup.mk' O (g ^ (n * n))) ∣ orderOf (g ^ (n * n)) :=
    orderOf_map_dvd _ _
  have hd3 : orderOf (QuotientGroup.mk' O (g ^ (n * n))) = 4 := by
    change orderOf (QuotientGroup.mk (g ^ (n * n)) : X ⧸ O) = 4
    rw [hmk, hyb4]
  rw [hd3] at hd2
  exact Nat.dvd_antisymm hd1 hd2

theorem exists_order_four_lift (hO : Odd (Nat.card O)) {x₂ : X} (hx₂ : x₂ * x₂ = 1)
    (M : Subgroup X) {yb : X ⧸ O} (hyb4 : orderOf yb = 4)
    (hc : yb * QuotientGroup.mk x₂ = QuotientGroup.mk x₂ * yb)
    (hM : ∃ m ∈ M, (QuotientGroup.mk m : X ⧸ O) = yb) :
    ∃ h y : X, (∃ m ∈ M, y = h * m * h⁻¹) ∧ orderOf y = 4 ∧ y * x₂ = x₂ * y := by
  obtain ⟨m, hmM, hmyb⟩ := hM
  obtain ⟨hl2mk, hl2ord⟩ := order_four_pow O hO hyb4 hmyb
  have hx : (QuotientGroup.mk (x₂ * m ^ (Nat.card O * Nat.card O) * x₂⁻¹) : X ⧸ O) =
      QuotientGroup.mk (m ^ (Nat.card O * Nat.card O)) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hl2mk,
      mul_inv_eq_iff_eq_mul]
    exact hc.symm
  obtain ⟨t, ht, htx⟩ := exists_fixed_lift O hO hx₂ hx
  have htc : t * x₂ = x₂ * t := (mul_inv_eq_iff_eq_mul.mp htx).symm
  obtain ⟨hymk, hyord⟩ := order_four_pow O hO hyb4 (ht.trans hl2mk)
  have hxy : (m ^ (Nat.card O * Nat.card O))⁻¹ * t ^ (Nat.card O * Nat.card O) ∈ O :=
    QuotientGroup.eq.mp (hl2mk.trans hymk.symm)
  obtain ⟨h, -, hh⟩ := AscFusion.exists_conj_of_odd_coset hO
    (isPGroup_zpowers_of_orderOf_four hl2ord) (isPGroup_zpowers_of_orderOf_four hyord)
    (mem_normalizer_of_normal O _) hxy
  exact ⟨h, t ^ (Nat.card O * Nat.card O), ⟨m ^ (Nat.card O * Nat.card O),
    M.pow_mem hmM _, hh.symm⟩, hyord, (Commute.pow_left (show Commute t x₂ from htc) _).eq⟩

theorem eq_one_of_central (hO : Odd (Nat.card O))
    (hcen : ∀ w : X ⧸ O, (∀ v : X ⧸ O, v * w = w * v) → w = 1) {x : X}
    (hx : ∀ v : X, v * x = x * v) (hx2 : x * x = 1) : x = 1 := by
  have h1 : (QuotientGroup.mk x : X ⧸ O) = 1 := hcen _ (fun v => by
    obtain ⟨v₀, rfl⟩ := QuotientGroup.mk_surjective v
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hx v₀])
  have hxO : x ∈ O := (QuotientGroup.eq_one_iff x).mp h1
  exact eq_one_of_isPGroup_of_mem_odd hO hxO (isPGroup_zpowers_of_sq hx2)

end Abstract

end CFSG.ClassicalInvolution.Asc77.C25I
