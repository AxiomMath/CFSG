module

public import CFSG.LieType.Ree.SuzukiOvoidAction
public import CFSG.LieType.Ree.SuzukiOrder

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint Matrix
open scoped LinearAlgebra.Projectivization Pointwise

variable {a : ℕ} {K : Type} [Field K]

theorem suzukiDElt_smul_suzukiLine_zero
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (l : Kˣ) : suzukiDElt a K l • suzukiLine a K 0 0 = suzukiLine a K 0 0 := by
  rw [(suzuki_ovoid_torus_action a hK l 0 0).2, mul_zero, mul_zero]

theorem suzukiDElt_injective
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Function.Injective (suzukiDElt a K) := fun l m h =>
  (suzuki_torus_identities a hK).2.2.1 l m (by
    have := congrArg (fun g : suzukiGroup a K =>
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) h
    simpa only [coe_suzukiDElt] using this)

theorem odd_card_units [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) : Odd (Nat.card Kˣ) := by
  rw [Nat.card_units, hK]
  obtain ⟨k, hk⟩ := (Nat.even_pow.2 ⟨even_two, by omega⟩ : Even (2 ^ (2 * a + 1)))
  have : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  exact ⟨k - 1, by omega⟩

theorem eq_one_of_sq_eq_one [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {l : Kˣ}
    (h : l ^ 2 = 1) : l = 1 := by
  have h1 : orderOf l ∣ 2 := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf l ∣ Nat.card Kˣ := orderOf_dvd_natCard l
  have hodd := odd_card_units hK
  rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h3 | h3
  · exact orderOf_eq_one_iff.1 h3
  · rw [h3] at h2
    exact absurd (even_iff_two_dvd.2 h2) (Nat.not_even_iff_odd.2 hodd)

theorem eq_zero_of_suzukiDElt_smul_eq
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {l : Kˣ}
    (hl : l ≠ 1) {u v : K} (h : suzukiDElt a K l • suzukiLine a K u v = suzukiLine a K u v) :
    u = 0 ∧ v = 0 := by
  rw [(suzuki_ovoid_torus_action a hK l u v).2, suzukiLine_eq_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hl' : (l : K) ≠ 1 := fun h => hl (Units.ext h)
  constructor
  · by_contra hu
    have h3 : (l : K)⁻¹ = 1 := mul_right_cancel₀ hu (h1.trans (one_mul u).symm)
    exact hl' (inv_eq_one.1 h3)
  · by_contra hv
    have h3 : ((l : K) ^ (2 ^ (a + 1) + 1))⁻¹ = 1 :=
      mul_right_cancel₀ hv (h2.trans (one_mul v).symm)
    have h4 : (l : K) ^ (2 ^ (a + 1) + 1) = 1 := inv_eq_one.1 h3
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hbij, -, -⟩ := suzuki_frobenius_exponents a K hK
    have h5 : l ^ (2 ^ (a + 1) + 1 : ℕ) = 1 :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, h4, Units.val_one])
    have h6 : l ^ ((2 : ℤ) ^ (a + 1) + 1) = (1 : Kˣ) ^ ((2 : ℤ) ^ (a + 1) + 1) := by
      rw [_root_.one_zpow, show ((2 : ℤ) ^ (a + 1) + 1) = ((2 ^ (a + 1) + 1 : ℕ) : ℤ) by
        push_cast; ring, zpow_natCast, h5]
    exact hl (hbij.1 h6)

theorem fixed_mem_suzukiOmega
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {l : Kˣ}
    (hl : l ≠ 1) {x : ℙ K (Fin 4 → K)} (hx : x ∈ suzukiOmega a K)
    (h : suzukiDElt a K l • x = x) : x = suzukiInfty K ∨ x = suzukiLine a K 0 0 := by
  rcases mem_suzukiOmega_iff.1 hx with rfl | ⟨u, v, rfl⟩
  · exact Or.inl rfl
  · obtain ⟨rfl, rfl⟩ := eq_zero_of_suzukiDElt_smul_eq hK hl h
    exact Or.inr rfl

theorem mem_suzukiT_of_smul_eq
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : suzukiGroup a K} (h1 : g • suzukiInfty K = suzukiInfty K)
    (h2 : g • suzukiLine a K 0 0 = suzukiLine a K 0 0) : g ∈ suzukiT a K := by
  have hB : g ∈ suzukiB a K := by
    rw [← (suzuki_ovoid_stabilizer hK).1]
    exact h1
  obtain ⟨u, v, l, rfl⟩ := (mem_suzukiB_iff hK).1 hB
  rw [mul_smul, suzukiDElt_smul_suzukiLine_zero hK, suzukiSElt_smul_suzukiLine hK] at h2
  simp only [add_zero, mul_zero] at h2
  obtain ⟨rfl, rfl⟩ := suzukiLine_eq_iff.1 h2
  rw [suzukiSElt_zero_zero hK, one_mul]
  exact suzukiDElt_mem_suzukiT a K l

theorem suzukiWElt_mul_suzukiDElt
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (l : Kˣ) :
    suzukiWElt a K * suzukiDElt a K l = suzukiDElt a K l⁻¹ * suzukiWElt a K := by
  rw [← suzukiWElt_D_W hK l, mul_assoc _ (suzukiWElt a K), suzukiWElt_mul_self, mul_one]

theorem centralizer_suzukiDElt
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {l : Kˣ}
    (hl : l ≠ 1) : Subgroup.centralizer {suzukiDElt a K l} = suzukiT a K := by
  apply le_antisymm
  · intro g hg
    have hc : suzukiDElt a K l * g = g * suzukiDElt a K l :=
      Subgroup.mem_centralizer_iff.1 hg _ rfl
    have hfix : ∀ x : ℙ K (Fin 4 → K), suzukiDElt a K l • x = x →
        suzukiDElt a K l • (g • x) = g • x := by
      intro x hx
      rw [← mul_smul, hc, mul_smul, hx]
    have hinf := hfix _ (suzuki_ovoid_torus_action a hK l 0 0).1
    have hzero := hfix _ (suzukiDElt_smul_suzukiLine_zero hK l)
    have hmem : ∀ x ∈ suzukiOmega a K, g • x ∈ suzukiOmega a K := fun x hx =>
      suzuki_smul_mem_suzukiOmega hK g hx
    have hne := suzukiLine_ne_suzukiInfty (a := a) (0 : K) 0
    rcases fixed_mem_suzukiOmega hK hl (hmem _ (suzukiInfty_mem_suzukiOmega a K)) hinf with
      h1 | h1
    · refine mem_suzukiT_of_smul_eq hK h1 ?_
      rcases fixed_mem_suzukiOmega hK hl (hmem _ (suzukiLine_mem_suzukiOmega a K 0 0)) hzero with
        h2 | h2
      · exact absurd (smul_left_cancel g (h2.trans h1.symm)) hne
      · exact h2
    · exfalso
      have h2 : g • suzukiLine a K 0 0 = suzukiInfty K := by
        rcases fixed_mem_suzukiOmega hK hl (hmem _ (suzukiLine_mem_suzukiOmega a K 0 0)) hzero
          with h2 | h2
        · exact h2
        · exact absurd (smul_left_cancel g (h2.trans h1.symm)) hne
      obtain ⟨hW1, hW2, -⟩ := suzuki_ovoid_weyl_action a hK
      have hgW : g * suzukiWElt a K ∈ suzukiT a K := mem_suzukiT_of_smul_eq hK
        (by rw [mul_smul, hW1, h2]) (by rw [mul_smul, hW2, h1])
      obtain ⟨μ, hμ⟩ := mem_suzukiT_iff.1 hgW
      have hg : g = suzukiDElt a K μ * suzukiWElt a K := by
        rw [hμ, mul_assoc, suzukiWElt_mul_self, mul_one]
      rw [hg, mul_assoc, suzukiWElt_mul_suzukiDElt hK, ← mul_assoc, ← mul_assoc,
        suzukiDElt_mul, suzukiDElt_mul] at hc
      have h3 := suzukiDElt_injective hK (mul_right_cancel hc)
      have h4 : l ^ 2 = 1 := by
        have : l * μ * l = μ * l⁻¹ * l := by rw [h3]
        rw [inv_mul_cancel_right, mul_comm l μ, mul_assoc] at this
        rw [sq]
        exact mul_left_cancel (this.trans (mul_one μ).symm)
      exact hl (eq_one_of_sq_eq_one hK h4)
  · intro g hg
    obtain ⟨μ, rfl⟩ := mem_suzukiT_iff.1 hg
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff.1 hh, suzukiDElt_mul, suzukiDElt_mul, mul_comm]

theorem two_le_two_pow_odd (a : ℕ) : 2 ≤ 2 ^ (2 * a + 1) :=
  calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem finite_suzukiGroup
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Finite (suzukiGroup a K) := by
  have h2 := two_le_two_pow_odd a
  refine Nat.finite_of_card_ne_zero ?_
  rw [suzuki_order hK]
  exact Nat.mul_ne_zero (Nat.mul_ne_zero (by positivity) (by omega)) (by positivity)

theorem exists_conj_mem_suzukiT
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hrq : r ∣ 2 ^ (2 * a + 1) - 1) {x : suzukiGroup a K}
    (hx : orderOf x = r) : ∃ g : suzukiGroup a K, g⁻¹ * x * g ∈ suzukiT a K := by
  have := Fact.mk hr
  have := finite_suzukiGroup hK
  set q := 2 ^ (2 * a + 1) with hq
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have hr2' : ∀ k, ¬ r ∣ 2 ^ k := fun k h =>
    hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  have hrq2 : ¬ r ∣ q ^ 2 + 1 := by
    intro h
    have h1 : r ∣ (q - 1) * (q + 1) := dvd_mul_of_dvd_left hrq _
    have h2 : q ^ 2 + 1 = (q - 1) * (q + 1) + 2 := by
      zify [hq1]
      ring
    rw [h2] at h
    exact hr2' 1 (by simpa using (Nat.dvd_add_right h1).1 h)
  have hT : Nat.card (suzukiT a K) = q - 1 := (suzuki_borel_structure hK).2.2.1
  have hfact : (Nat.card (suzukiGroup a K)).factorization r =
      (Nat.card (suzukiT a K)).factorization r := by
    rw [suzuki_order hK, hT]
    have hq0 : q ^ 2 ≠ 0 := by positivity
    have hq10 : q - 1 ≠ 0 := by
      have := two_le_two_pow_odd a
      omega
    rw [Nat.factorization_mul (mul_ne_zero hq0 hq10) (by positivity),
      Nat.factorization_mul hq0 hq10, Finsupp.add_apply, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (show ¬ r ∣ q ^ 2 by
        rw [hq, ← pow_mul]; exact hr2' _),
      Nat.factorization_eq_zero_of_not_dvd hrq2, zero_add, add_zero]
  obtain ⟨Q⟩ : Nonempty (Sylow r (suzukiT a K)) := inferInstance
  set Q' := (Q : Subgroup (suzukiT a K)).map (suzukiT a K).subtype with hQ'
  have hQ'card : Nat.card Q' = r ^ (Nat.card (suzukiGroup a K)).factorization r := by
    rw [hQ', Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Sylow.card_eq_multiplicity, hfact]
  let P := Sylow.ofCard Q' hQ'card
  have hxp : IsPGroup r (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨S, hS⟩ := hxp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (suzukiGroup a K) P S
  have hxS : x ∈ (S : Subgroup (suzukiGroup a K)) := hS (Subgroup.mem_zpowers x)
  rw [← hg, Sylow.coe_subgroup_smul,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxS
  refine ⟨g, ?_⟩
  have hmem : (MulAut.conj g)⁻¹ • x ∈ Q' := hxS
  obtain ⟨y, -, hy⟩ := Subgroup.mem_map.1 hmem
  rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv] at hy
  rw [← hy]
  exact y.2

theorem suzuki_split_torus_odd_prime_centralizers [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (∀ t ∈ suzukiT a K, t ≠ 1 → Subgroup.centralizer {t} = suzukiT a K) ∧
      ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ 2 ^ (2 * a + 1) - 1 → ∀ x : suzukiGroup a K,
        orderOf x = r →
          (∃ g : suzukiGroup a K, Subgroup.centralizer {x} =
            (suzukiT a K).map (MulAut.conj g).toMonoidHom) ∧
          ∀ y ∈ Subgroup.centralizer {x}, ∀ z ∈ Subgroup.centralizer {x}, y * z = z * y := by
  have hcent : ∀ t ∈ suzukiT a K, t ≠ 1 → Subgroup.centralizer {t} = suzukiT a K := by
    intro t ht ht1
    obtain ⟨l, rfl⟩ := mem_suzukiT_iff.1 ht
    refine centralizer_suzukiDElt hK fun hl => ht1 ?_
    rw [hl, suzukiDElt_one]
  have hTab := (suzuki_borel_structure hK).2.1
  refine ⟨hcent, fun r hr hr2 hrq x hx => ?_⟩
  obtain ⟨g, hg⟩ := exists_conj_mem_suzukiT hK hr hr2 hrq hx
  have hne : g⁻¹ * x * g ≠ 1 := by
    intro h1
    have : x = 1 := by
      have := congrArg (fun y => g * y * g⁻¹) h1
      simpa [mul_assoc] using this
    rw [this, orderOf_one] at hx
    exact hr.one_lt.ne hx
  have hC := hcent _ hg hne
  have hmap : Subgroup.centralizer {x} = (suzukiT a K).map (MulAut.conj g).toMonoidHom := by
    ext y
    rw [← hC, Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hy
      refine ⟨g⁻¹ * y * g, Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
      · calc g⁻¹ * y * g * (g⁻¹ * x * g) = g⁻¹ * (y * x) * g := by group
          _ = g⁻¹ * (x * y) * g := by rw [hy]
          _ = g⁻¹ * x * g * (g⁻¹ * y * g) := by group
      · simp [MulAut.conj_apply, mul_assoc]
    · rintro ⟨z, hz, rfl⟩
      have hz' := Subgroup.mem_centralizer_singleton_iff.1 hz
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * z * g⁻¹ * x = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by rw [hz']
        _ = x * (g * z * g⁻¹) := by group
  refine ⟨⟨g, hmap⟩, fun y hy z hz => ?_⟩
  rw [hmap] at hy hz
  obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.1 hz
  rw [← map_mul, ← map_mul, hTab y' hy' z' hz']

end CFSG.LieType.Ree
