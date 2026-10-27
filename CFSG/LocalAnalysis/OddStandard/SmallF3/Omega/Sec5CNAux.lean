module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B513Prod
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CNAbs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CNCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CNHeart

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

theorem sec5cn_core_of_eq (h36 : Asc82Lemma36) (h52a : Asc82Lemma52a) (hO : Asc82Outside)
    (hAut : Asc82FactAutOm6) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {m s : G}
    (hms : m⁻¹ * t * m = s) (hmz : m ∈ centralizer ({z} : Set G)) (hs2 : s * s = 1)
    (hs1 : s ≠ 1) (hsz : s ≠ z) (hst : s * t = t * s) (hst1 : s ≠ t) (hst3 : s ≠ t * z)
    (hK : ∀ k ∈ K₁ ⊔ K₂, s * k = k * s) : m ∈ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
  subst hms
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact sec5cn_core h36 h52a hO hAut c hmz (orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1)
    hsz hst hst1 hst3 hK

theorem sec5cn_heart_facts (hdict : Asc82HeartDict) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    (∀ x ∈ A, x * x = 1) ∧ (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧ z ∈ A ∧
      (∃ a b : G, a ∈ A ⊓ (K₁ ⊔ K₂) ∧ b ∈ A ⊓ (K₁ ⊔ K₂) ∧ a ≠ 1 ∧ a ≠ z ∧ b ≠ 1 ∧ b ≠ z ∧
        b ≠ a ∧ b ≠ a * z) ∧
      ∃ a₁ ∈ A ⊓ (CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h),
        a₁ ≠ 1 ∧ a₁ ≠ z ∧ a₁ ≠ t ∧ a₁ ≠ t * z := by
  obtain ⟨Alt, φ, -, hpm, hz, hK, hP⟩ := hdict G t L S z r B A K₁ K₂ h c
  have hH := sec5cn_heart_of hpm
  have hzE : IsEvenVec heartZVec := by
    unfold IsEvenVec heartZVec
    decide
  refine ⟨fun x hx => hH.sq_mem hx, fun x hx y hy => hH.comm hx hy, ?_,
    sec5cn_exists_ab hH hz hK, sec5cn_exists_a1 hH hz hP c.t_mul_self c.t_comm_z⟩
  rw [hz]
  exact hH.mem _ hzE

theorem sec5cn_gen_cent (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {ρ : G}
    (hρ : ∀ κ ∈ K₁ ⊔ K₂, Odd (orderOf κ) → κ * ρ = ρ * κ) :
    ∀ k ∈ K₁ ⊔ K₂, k * ρ = ρ * k := by
  have hle : K₁ ⊔ K₂ ≤ centralizer ({ρ} : Set G) := by
    rw [c.prod]
    unfold twoRes
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨hg, hodd⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hρ g (c.K_odd_mem hg hodd) hodd)
  intro k hk
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hk)

theorem sec5cn_QN (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h52a : Asc82Lemma52a)
    (hO : Asc82Outside) (hdict : Asc82HeartDict) (hMA : Asc82Fact513AModel)
    (hAut : Asc82FactAutOm6) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {π : SL23 × SL23 →* G}
    (hπ : Sec5CNPi π (CFSG.conjugate K₁ h) (CFSG.conjugate K₂ h) z) :
    (∀ q ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h, q ^ 4 = 1 →
        q ∈ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G)) ∧
      ∃ u v : SL23, π (u, v) ∈ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) ∧ u ^ 4 ≠ 1 ∧
        v ^ 4 ≠ 1 := by
  obtain ⟨hA2, hAc, -, -, a₁, ha₁, ha₁1, ha₁z, ha₁t, ha₁tz⟩ := sec5cn_heart_facts hdict c
  have ha₁A : a₁ ∈ A := (Subgroup.mem_inf.mp ha₁).1
  have ha₁P : a₁ ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h := (Subgroup.mem_inf.mp ha₁).2
  have ha₁2 : a₁ * a₁ = 1 := hA2 a₁ ha₁A
  have hta₁ : a₁ * t = t * a₁ := hAc a₁ ha₁A t c.t_mem_A
  have ha₁K : ∀ k ∈ K₁ ⊔ K₂, a₁ * k = k * a₁ := fun k hk =>
    (Subgroup.mem_centralizer_iff.mp (hMA G t L S z r B A K₁ K₂ h c ha₁) k hk).symm
  have hzK : ∀ k ∈ K₁ ⊔ K₂, z * k = k * z := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (c.K_le hk)).2).symm
  have hz2 : z * z = 1 := c.z_mul_self
  obtain ⟨ρ, hρP, hρt⟩ := sec5b513_trans (Classical.choice c.iso₃) (Classical.choice c.iso₄)
    c.comm₃₄ c.z_mem_K₃ c.z_mem_K₄ c.z_mul_self c.z_ne_one c.t_mem_sup₃₄ c.t_mul_self c.t_ne_one
    (c.t_ne_z h37) ha₁P ha₁2 ha₁1 ha₁z
  have hρN : ρ ∈ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) :=
    sec5cn_core_of_eq h36 h52a hO hAut c hρt (c.P_le_cent hρP) ha₁2 ha₁1 ha₁z hta₁ ha₁t ha₁tz
      ha₁K
  obtain ⟨c₀, hc₀P, -, hc₀t⟩ :=
    hπ.exists_swap c.t_mem_sup₃₄ c.t_mul_self c.t_ne_one (c.t_ne_z h37)
  have hρz : ρ⁻¹ * z * ρ = z := by
    have h1 : z * ρ = ρ * z := hπ.z_comm hρP
    calc ρ⁻¹ * z * ρ = ρ⁻¹ * (z * ρ) := by group
      _ = ρ⁻¹ * (ρ * z) := by rw [h1]
      _ = z := by group
  have hza₁ : z * a₁ = a₁ * z := hπ.z_comm ha₁P
  have hc₀ρN : c₀ * ρ ∈ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
    refine sec5cn_core_of_eq h36 h52a hO hAut c (s := a₁ * z) ?_
      (c.P_le_cent (mul_mem hc₀P hρP)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · calc (c₀ * ρ)⁻¹ * t * (c₀ * ρ) = ρ⁻¹ * (c₀⁻¹ * t * c₀) * ρ := by group
        _ = ρ⁻¹ * (t * z) * ρ := by rw [hc₀t]
        _ = (ρ⁻¹ * t * ρ) * (ρ⁻¹ * z * ρ) := by group
        _ = a₁ * z := by rw [hρt, hρz]
    · calc (a₁ * z) * (a₁ * z) = a₁ * (z * a₁) * z := by group
        _ = a₁ * (a₁ * z) * z := by rw [hza₁]
        _ = (a₁ * a₁) * (z * z) := by group
        _ = 1 := by rw [ha₁2, hz2, mul_one]
    · intro h1
      apply ha₁z
      calc a₁ = (a₁ * z) * z := by rw [mul_assoc, hz2, mul_one]
        _ = z := by rw [h1, one_mul]
    · intro h1
      apply ha₁1
      calc a₁ = (a₁ * z) * z := by rw [mul_assoc, hz2, mul_one]
        _ = z * z := by rw [h1]
        _ = 1 := hz2
    · calc (a₁ * z) * t = a₁ * (z * t) := by group
        _ = a₁ * (t * z) := by rw [← c.t_comm_z]
        _ = (a₁ * t) * z := by group
        _ = (t * a₁) * z := by rw [hta₁]
        _ = t * (a₁ * z) := by group
    · intro h1
      apply ha₁tz
      calc a₁ = (a₁ * z) * z := by rw [mul_assoc, hz2, mul_one]
        _ = t * z := by rw [h1]
    · intro h1
      exact ha₁t (mul_right_cancel h1)
    · intro k hk
      calc (a₁ * z) * k = a₁ * (z * k) := by group
        _ = a₁ * (k * z) := by rw [hzK k hk]
        _ = (a₁ * k) * z := by group
        _ = (k * a₁) * z := by rw [ha₁K k hk]
        _ = k * (a₁ * z) := by group
  have hc₀N : c₀ ∈ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
    simpa using mul_mem hc₀ρN (inv_mem hρN)
  have ht4 : t ^ 4 = 1 := sec5cn_pow4_of_mul_self c.t_mul_self
  refine ⟨fun q hq hq4 => sec5cn_swap_N hπ (fun g hgt hgz => c.mem_normalizer_of_cent h36
      (Subgroup.mem_centralizer_singleton_iff.mpr hgt)
      (Subgroup.mem_centralizer_singleton_iff.mpr hgz)) hc₀N hc₀P hc₀t hq
      (hπ.conj_q hq c.t_mem_sup₃₄ hq4 ht4), ?_⟩
  obtain ⟨u, v, huv, hu, hv⟩ := hπ.rho_split c.t_mem_sup₃₄ ha₁P hρP c.t_mul_self ha₁2
    c.t_ne_one ha₁1 (c.t_ne_z h37) ha₁z ha₁t ha₁tz hta₁.symm hρt
  exact ⟨u, v, huv ▸ hρN, hu, hv⟩

end CFSG.OddStandard.SmallF3.Omega
