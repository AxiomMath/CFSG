module

public import CFSG.ClassicalInvolution.Q3.TL3T13

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516.Four

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC.Thin

theorem eq_one_of_pow_two_pow_three {X : Type} [Group X] (g : X) {k a : ℕ}
    (hk : g ^ 2 ^ k = 1) (ha : g ^ 3 ^ a = 1) : g = 1 :=
  orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow k a (by norm_num : Nat.Coprime 2 3))
    (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one ha))

section Hom

variable {Y M : Type} [Group Y] [Group M]

theorem exists_lift_pow_three_of [Finite Y] (φ : Y →* M) {x : M} (hx : x ∈ φ.range)
    (hx3 : x ^ 3 = 1) : ∃ y : Y, φ y = x ∧ ∃ a : ℕ, y ^ 3 ^ a = 1 := by
  obtain ⟨y₀, rfl⟩ := hx
  obtain ⟨a, r, hr, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y₀).ne' 3 (by norm_num)
  refine ⟨y₀ ^ (r * r), ?_, a, ?_⟩
  · have hr2 : r * r % 3 = 1 := by
      have : r % 3 = 1 ∨ r % 3 = 2 := by omega
      rcases this with h | h <;> simp [Nat.mul_mod, h]
    rw [map_pow, pow_eq_pow_mod _ hx3, hr2, pow_one]
  · rw [← pow_mul, show r * r * 3 ^ a = (3 ^ a * r) * r by ring, ← hN, pow_mul,
      pow_orderOf_eq_one, one_pow]

theorem comm_of_pow_three_of (φ : Y →* M) (hker : φ.ker ≤ Subgroup.center Y)
    (hk : IsPGroup 2 φ.ker) {y w : Y} {a : ℕ} (hy : y ^ 3 ^ a = 1)
    (h : φ y * φ w = φ w * φ y) : y * w = w * y := by
  set c := w⁻¹ * (y * w * y⁻¹) with hc
  have hcker : c ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hc, map_mul, map_inv, map_mul, map_mul, map_inv, h]
    group
  have hyw : y * w * y⁻¹ = w * c := by rw [hc]; group
  have hpow : ∀ k : ℕ, y ^ k * w * (y ^ k)⁻¹ = w * c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hck : y * c ^ k * y⁻¹ = c ^ k := by
        have := Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ (hker hcker) k) y
        rw [this]
        group
      calc y ^ (k + 1) * w * (y ^ (k + 1))⁻¹ = y * (y ^ k * w * (y ^ k)⁻¹) * y⁻¹ := by
            rw [pow_succ']
            group
        _ = (y * w * y⁻¹) * (y * c ^ k * y⁻¹) := by rw [ih]; group
        _ = w * c ^ (k + 1) := by rw [hyw, hck, pow_succ', mul_assoc]
  have hc3 : c ^ 3 ^ a = 1 := by
    have := hpow (3 ^ a)
    rw [hy, one_mul, inv_one, mul_one] at this
    exact mul_left_cancel (this.symm.trans (mul_one w).symm)
  obtain ⟨j, hj⟩ := hk ⟨c, hcker⟩
  have hj' : c ^ 2 ^ j = 1 := by
    have := congrArg Subtype.val hj
    rwa [Subgroup.coe_pow] at this
  have h1 : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow a j (by norm_num))
    (orderOf_dvd_of_pow_eq_one hc3) (orderOf_dvd_of_pow_eq_one hj')
  have hc1 : c = 1 := orderOf_eq_one_iff.mp h1
  calc y * w = (y * w * y⁻¹) * y := by group
    _ = w * y := by rw [hyw, hc1, mul_one]

end Hom

theorem false_of_aeIdent {X : Type} [Group X] [Finite X] {Ω : Set (Subgroup X)} {n : ℕ} (hn : 5 ≤ n)
    (I : TC.Thin.AEIdent Ω n) (hO : classicalInvolutionOddCore ↥(TC.Thin.pSpan Ω) = ⊥)
    {K : Subgroup X} (hK : K ∈ Ω) (h8 : Nat.card K = 8) {t : X} (ht : IsUniqueInvolution K t)
    (h2 : ∀ g : X, g * t = t * g → ∃ k : ℕ, g ^ 2 ^ k = 1) : False := by
  obtain ⟨α, h, b, hlab⟩ := I.label K hK
  have hz : I.φ ⟨t, le_pSpan hK ht.mem⟩ = AE.zBar α h := I.map_eq_zBar hn hK h8 hlab ht
  have hrange : AE.yBar α h ∈ I.φ.range := by
    rw [I.range_eq]
    exact AE.yBar_mem α h
  have hne : AE.yBar α h ≠ 1 := by
    intro h1
    obtain ⟨x, -, hx⟩ := AE.yBar_not_comm_memBar hn α h b
    exact hx (by rw [h1, one_mul, mul_one])
  obtain ⟨y, hy, a, hya⟩ := I.exists_lift_pow_three hrange (AE.yBar_pow_three α h)
  have hcomm : I.φ y * I.φ ⟨t, le_pSpan hK ht.mem⟩ =
      I.φ ⟨t, le_pSpan hK ht.mem⟩ * I.φ y := by
    rw [hy, hz]
    exact AE.yBar_comm_zBar α h
  have hyt := I.comm_of_pow_three (I.isPGroup_ker hO) hya hcomm
  have hyt' : (y : X) * t = t * (y : X) := congrArg Subtype.val hyt
  obtain ⟨k, hkpow⟩ := h2 (y : X) hyt'
  have hya' : (y : X) ^ 3 ^ a = 1 := by
    have := congrArg Subtype.val hya
    rwa [Subgroup.coe_pow] at this
  have hy1 : y = 1 := Subtype.ext (eq_one_of_pow_two_pow_three _ hkpow hya')
  apply hne
  rw [← hy, hy1, map_one]

theorem false_of_aeIdentOn {X : Type} [Group X] [Finite X] {Ω : Set (Subgroup X)} {n : ℕ}
    (hn : 5 ≤ n) {𝒜 : Set (Finset (Fin n))} {H : Subgroup (AE.AEQ n)}
    (I : TC.Thin.AEIdentOn Ω n 𝒜 H)
    (hO : classicalInvolutionOddCore ↥(TC.Thin.pSpan Ω) = ⊥)
    (hy : ∀ α ∈ 𝒜, ∀ h : α.card = 4, ∃ y ∈ H, y ^ 3 = 1 ∧ y * AE.zBar α h = AE.zBar α h * y ∧
      ∃ x ∈ AE.memBar α h true, y * x ≠ x * y)
    {K : Subgroup X} (hK : K ∈ Ω) (h8 : Nat.card K = 8) {t : X} (ht : IsUniqueInvolution K t)
    (h2 : ∀ g : X, g * t = t * g → ∃ k : ℕ, g ^ 2 ^ k = 1) : False := by
  obtain ⟨α, hα, h, b, hlab⟩ := I.label K hK
  have hz : I.φ ⟨t, le_pSpan hK ht.mem⟩ = AE.zBar α h :=
    TC.Thin.phi_map_eq_zBar I.φ hn hK h8 hlab ht
  obtain ⟨y', hyH, hy3, hyz, x, -, hx⟩ := hy α hα h
  have hyr : y' ∈ I.φ.range := by
    rw [I.range_eq]
    exact hyH
  have hne : y' ≠ 1 := by
    intro h1
    exact hx (by rw [h1, one_mul, mul_one])
  obtain ⟨y, hyφ, a, hya⟩ := exists_lift_pow_three_of I.φ hyr hy3
  have hk : IsPGroup 2 I.φ.ker := (isPGroup_center_of_corefree hO).to_le I.ker_le
  have hcomm : I.φ y * I.φ ⟨t, le_pSpan hK ht.mem⟩ =
      I.φ ⟨t, le_pSpan hK ht.mem⟩ * I.φ y := by
    rw [hyφ, hz]
    exact hyz
  have hyt := comm_of_pow_three_of I.φ I.ker_le hk hya hcomm
  have hyt' : (y : X) * t = t * (y : X) := congrArg Subtype.val hyt
  obtain ⟨k, hkpow⟩ := h2 (y : X) hyt'
  have hya' : (y : X) ^ 3 ^ a = 1 := by
    have := congrArg Subtype.val hya
    rwa [Subgroup.coe_pow] at this
  have hy1 : y = 1 := Subtype.ext (eq_one_of_pow_two_pow_three _ hkpow hya')
  apply hne
  rw [← hyφ, hy1, map_one]

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516.Four
