module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.TypeBound
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4ModTwist

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

section Twist


variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {m : ℕ}

theorem phiPow_surj_U (e : ℕ) {u' : adjointGroup Tag.F4 K} (hu' : u' ∈ (DF4 K).U) :
    ∃ u ∈ (DF4 K).U, (phiF4 K ^ e) u = u' := by
  induction e generalizing u' with
  | zero => exact ⟨u', hu', by simp⟩
  | succ e ih =>
    have h1 : u' ∈ (DF4 K).U.map (phiF4 K).toMonoidHom := by rw [phi_map_U]; exact hu'
    obtain ⟨u'', hu'', rfl⟩ := h1
    obtain ⟨u, hu, hue⟩ := ih hu''
    refine ⟨u, hu, ?_⟩
    rw [pow_succ']
    show phiF4 K ((phiF4 K ^ e) u) = _
    rw [hue]
    rfl

theorem chi_eq_of_twist_phiPow (ρ : Representation k (adjointGroup Tag.F4 K) (Fin m → k))
    (hρ : IsSimpleRep ρ) {y : Fin m → k} {χ : adjointGroup Tag.F4 K → k}
    {J : Finset (Fin Tag.F4.rank)} (ht : IsChevType Tag.F4 K 2 exists_weyl_neg_F4' ρ y χ J)
    (e : ℕ) (B' : Module.End k (Fin m → k)) (hB' : IsUnit B')
    (hBρ : ∀ s, B' * ρ s = ρ ((phiF4 K ^ e) s) * B') :
    ∃ c : k, c ≠ 0 ∧ B' y = c • y ∧ ∀ h ∈ (DF4 K).H, χ h = χ ((phiF4 K ^ e) h) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ
  have hy1 : B' y ∈ (DF4 K).fixU ρ := by
    intro u' hu'
    obtain ⟨u, hu, rfl⟩ := phiPow_surj_U e hu'
    have := congrArg (fun f : Module.End k (Fin m → k) => f y) (hBρ u)
    simp only [Module.End.mul_apply] at this
    rw [← this, ht.1 u hu]
  have hy10 : B' y ≠ 0 := by
    intro h0
    have hbij := (Module.End.isUnit_iff B').1 hB'
    exact ht.2.1 (hbij.injective (by rw [h0, map_zero]))
  obtain ⟨c, hc⟩ := (DF4 K).fixU_eq_smul hρ hμ hy1
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hy10 (by rw [hc, zero_smul])
  refine ⟨c, hc0, hc, fun h hh => ?_⟩
  have e1 : ρ ((phiF4 K ^ e) h) (B' y) = χ h • B' y := by
    have := congrArg (fun f : Module.End k (Fin m → k) => f y) (hBρ h)
    simp only [Module.End.mul_apply] at this
    rw [← this, ht.2.2.1 _ hh, map_smul]
  have e2 : ρ ((phiF4 K ^ e) h) (B' y) = χ ((phiF4 K ^ e) h) • B' y := by
    rw [hc, map_smul, ht.2.2.1 _ (phiPow_mem_H K e hh), smul_comm]
  exact smul_left_injective k hy10 (e1.symm.trans e2)

theorem permF4_end (s : Fin Tag.F4.rank) (hs : s.val = 0 ∨ s.val = 3) : permF4 s ≠ s := by
  revert s; decide

theorem survivor_not_twist_even {n : ℕ} (hK : Nat.card K = 2 ^ n) {r : ℕ} (hr : 1 ≤ r) (hnr : n = 2 * r)
    {χ : adjointGroup Tag.F4 K → k} {J : Finset (Fin Tag.F4.rank)} (hS : F4Surv K χ J)
    (hχ : ∀ h ∈ (DF4 K).H, χ h = χ ((phiF4 K ^ (2 * r)) h)) : False := by
  obtain ⟨b, s, hs, hJ, hχs⟩ := hS
  have h1 : ∀ t : Kˣ, (algebraMap K k (t : K)) ^ (2 ^ b) =
      (algebraMap K k (t : K)) ^ (2 ^ b * 2 ^ r) := by
    intro t
    have := hχ (dC Tag.F4 K s t) (dC_mem_H s t)
    rw [phiPow_even_dC, hχs, hχs] at this
    simp only [↓reduceIte] at this
    rw [this, Units.val_pow_eq_pow_val, map_pow, ← pow_mul, mul_comm]
  have hle : 2 ^ b ≤ 2 ^ b * 2 ^ r := Nat.le_mul_of_pos_right _ (by positivity)
  have hd := dvd_of_forall_pow_eq (k := k) hK hle h1
  have e2 : 2 ^ b * 2 ^ r - 2 ^ b = 2 ^ b * (2 ^ r - 1) := by
    rw [Nat.mul_sub, Nat.mul_one]
  rw [e2] at hd
  have hodd : Odd (2 ^ n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ⟨2 ^ m - 1, by have := Nat.one_le_two_pow (n := m); rw [pow_succ]; omega⟩
  have hcop : Nat.Coprime (2 ^ n - 1) (2 ^ b) := hodd.coprime_two_right.pow_right b
  have h3 := hcop.dvd_of_dvd_mul_left hd
  have h4 : 2 ^ r - 1 < 2 ^ n - 1 := by
    have : 2 ^ r < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have := @Nat.one_le_two_pow r
    omega
  have h5 : 0 < 2 ^ r - 1 := by
    have : 2 ≤ 2 ^ r := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
    omega
  exact absurd (Nat.le_of_dvd h5 h3) (by omega)

theorem survivor_not_twist_odd {n : ℕ} (hK : Nat.card K = 2 ^ n) {r : ℕ} (hr : 1 ≤ r) (hnr : n = 2 * r + 1)
    {χ : adjointGroup Tag.F4 K → k} {J : Finset (Fin Tag.F4.rank)} (hS : F4Surv K χ J)
    (hχ : ∀ h ∈ (DF4 K).H, χ h = χ ((phiF4 K ^ (2 * r + 1)) h)) : False := by
  obtain ⟨b, s, hs, hJ, hχs⟩ := hS
  have h1 : ∀ t : Kˣ, (algebraMap K k (t : K)) ^ 0 = (algebraMap K k (t : K)) ^ (2 ^ b) := by
    intro t
    have := hχ (dC Tag.F4 K s t) (dC_mem_H s t)
    rw [phiPow_odd_dC, hχs, hχs] at this
    simp only [↓reduceIte, if_neg (permF4_end s hs), pow_zero] at this
    rw [pow_zero]
    exact this.symm
  have hle : 0 ≤ 2 ^ b := Nat.zero_le _
  have hd := dvd_of_forall_pow_eq (k := k) hK hle h1
  have hodd : Odd (2 ^ n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ⟨2 ^ m - 1, by have := Nat.one_le_two_pow (n := m); rw [pow_succ]; omega⟩
  have hcop : Nat.Coprime (2 ^ n - 1) (2 ^ b) := hodd.coprime_two_right.pow_right b
  rw [Nat.sub_zero] at hd
  have h3 : 2 ^ n - 1 = 1 := Nat.Coprime.eq_one_of_dvd hcop hd
  have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem J_stable_of_twist_one (ρ : Representation k (adjointGroup Tag.F4 K) (Fin m → k))
    (hρ : IsSimpleRep ρ) {y : Fin m → k} {χ : adjointGroup Tag.F4 K → k}
    {J : Finset (Fin Tag.F4.rank)} (ht : IsChevType Tag.F4 K 2 exists_weyl_neg_F4' ρ y χ J)
    (B' : Module.End k (Fin m → k)) (hB' : IsUnit B')
    (hBρ : ∀ s, B' * ρ s = ρ ((phiF4 K ^ 1) s) * B') (i : Fin Tag.F4.rank) :
    permF4 i ∈ J ↔ i ∈ J := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨c, hc0, hc, hχ⟩ := chi_eq_of_twist_phiPow ρ hρ ht 1 B' hB' hBρ
  simp only [pow_one] at hBρ hχ
  have hbij := (Module.End.isUnit_iff B').1 hB'
  have hchi : ∀ (i : Fin Tag.F4.rank) (t : Kˣ),
      χ (dC Tag.F4 K i t) = χ (dC Tag.F4 K (permF4 i) (t ^ expF4 i)) := by
    intro i t
    have := hχ (dC Tag.F4 K i t) (dC_mem_H i t)
    rwa [phi_dC] at this
  have hall : (∀ t : Kˣ, χ (dC Tag.F4 K i t) = 1) ↔ (∀ s : Kˣ, χ (dC Tag.F4 K (permF4 i) s) = 1) := by
    constructor
    · intro h s
      obtain ⟨t, rfl⟩ := unit_pow_surj K i s
      rw [← hchi, h]
    · intro h t
      rw [hchi]
      exact h _
  have hT : B' ((DF4 K).heckeT ρ i y) = c • (DF4 K).heckeT ρ (permF4 i) y := by
    rw [heckeT_chevDatum, heckeT_chevDatum, map_sum]
    have hb := (pow_exp_bijective K i).sum_comp
      (fun c' : K => ρ (xC Tag.F4 K (permF4 i) c' * nC Tag.F4 K (permF4 i)) y)
    rw [← hb, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    have h1 := congrArg (fun f : Module.End k (Fin m → k) => f y)
      (hBρ (xC Tag.F4 K i c' * nC Tag.F4 K i))
    simp only [Module.End.mul_apply] at h1
    rw [h1, hc, map_smul, phi_xC_nC]
  have hT0 : (DF4 K).heckeT ρ i y = 0 ↔ (DF4 K).heckeT ρ (permF4 i) y = 0 := by
    constructor
    · intro h
      rw [h, map_zero] at hT
      exact (smul_eq_zero.1 hT.symm).resolve_left hc0
    · intro h
      rw [h, smul_zero] at hT
      exact hbij.injective (by rw [hT, map_zero])
  rw [ht.2.2.2 i, ht.2.2.2 (permF4 i), hall, hT0]

theorem survivor_no_twist {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k (adjointGroup Tag.F4 K) (Fin m → k)} (hρ : IsSimpleRep ρ)
    {y : Fin m → k} {χ : adjointGroup Tag.F4 K → k} {J : Finset (Fin Tag.F4.rank)}
    (ht : IsChevType Tag.F4 K 2 exists_weyl_neg_F4' ρ y χ J) (hS : F4Surv K χ J)
    (B : Module.End k (Fin m → k)) (hB : IsUnit B) (g : adjointGroup Tag.F4 K)
    (hBρ : ∀ s, B * ρ s = ρ ((MulAut.conj g * phiF4 K ^ n) s) * B) : False := by
  have hρunit : ∀ s, IsUnit (ρ s) := fun s =>
    ⟨⟨ρ s, ρ s⁻¹, by rw [← map_mul, mul_inv_cancel, map_one], by
      rw [← map_mul, inv_mul_cancel, map_one]⟩, rfl⟩
  have hB'unit : IsUnit (ρ g⁻¹ * B) := (hρunit g⁻¹).mul hB
  have hB'ρ : ∀ s, (ρ g⁻¹ * B) * ρ s = ρ ((phiF4 K ^ n) s) * (ρ g⁻¹ * B) := by
    intro s
    have h1 := hBρ s
    rw [MulAut.mul_apply, MulAut.conj_apply] at h1
    have key : ρ g⁻¹ * ρ (g * (phiF4 K ^ n) s * g⁻¹) = ρ ((phiF4 K ^ n) s) * ρ g⁻¹ := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    calc (ρ g⁻¹ * B) * ρ s = ρ g⁻¹ * (B * ρ s) := mul_assoc _ _ _
      _ = ρ g⁻¹ * (ρ (g * (phiF4 K ^ n) s * g⁻¹) * B) := by rw [h1]
      _ = (ρ g⁻¹ * ρ (g * (phiF4 K ^ n) s * g⁻¹)) * B := (mul_assoc _ _ _).symm
      _ = (ρ ((phiF4 K ^ n) s) * ρ g⁻¹) * B := by rw [key]
      _ = ρ ((phiF4 K ^ n) s) * (ρ g⁻¹ * B) := mul_assoc _ _ _
  obtain ⟨c, hc0, hc, hχ⟩ := chi_eq_of_twist_phiPow ρ hρ ht n (ρ g⁻¹ * B) hB'unit hB'ρ
  rcases Nat.even_or_odd' n with ⟨r, hr | hr⟩
  · subst hr
    exact survivor_not_twist_even hK (by omega) rfl hS hχ
  · subst hr
    by_cases hr0 : r = 0
    · subst hr0
      simp only [mul_zero, zero_add] at hB'ρ
      have := J_stable_of_twist_one ρ hρ ht (ρ g⁻¹ * B) hB'unit hB'ρ
      obtain ⟨b, s, hs, hJ, -⟩ := hS
      have hs1 : s ∈ J := (this s).1 (by
        rw [hJ]; exact Finset.mem_erase.2 ⟨permF4_end s hs, Finset.mem_univ _⟩)
      rw [hJ] at hs1
      exact (Finset.mem_erase.1 hs1).1 rfl
    · exact survivor_not_twist_odd hK (by omega) rfl hS hχ

end Twist

end CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc
