module

public import CFSG.LargeExtraspecial.AS35LLocal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35Z

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.Fischer.Classification.Unitary CFSG.LargeExtraspecial.S12InspPSU
  CFSG.LargeExtraspecial.AS35L
open CFSG.Blueprint.Fischer (K)

variable {k : ℕ}

theorem K_cases (c : K) : c = 0 ∨ c = 1 ∨ c = ω ∨ c = ω * ω := by
  by_cases hc : c = 0
  · exact Or.inl hc
  have hω2 : ω * ω = ω + 1 := by rw [← frob_omega, frob_apply, sq]
  have h2 : (2 : K) = 0 := two_eq_zero
  have h3 : c ^ 3 = 1 := by
    have h := frob_mul_self hc
    rw [frob_apply] at h
    linear_combination h
  have e : (c - 1) * ((c - ω) * (c - ω * ω)) = 0 := by
    have e2 : c * c + c + 1 = (c - ω) * (c - ω * ω) := by
      linear_combination (c - ω - 1) * hω2 + (c + c * ω - ω) * h2
    rw [← e2]
    linear_combination h3
  rcases mul_eq_zero.1 e with h | h
  · exact Or.inr (Or.inl (sub_eq_zero.1 h))
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.1 h)))
  · exact Or.inr (Or.inr (Or.inr (sub_eq_zero.1 h)))

theorem pow_three_K {c : K} (hc : c ≠ 0) : c ^ 3 = 1 := by
  have h := frob_mul_self hc
  rw [frob_apply] at h
  linear_combination h

theorem eq_one_of_pow_two_pow_K {c : K} (hc : c ≠ 0) {j : ℕ} (hj : c ^ 2 ^ j = 1) : c = 1 := by
  have h1 : orderOf c ∣ Nat.gcd (2 ^ j) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hj) (orderOf_dvd_of_pow_eq_one (pow_three_K hc))
  have h2 : Nat.gcd (2 ^ j) 3 = 1 := Nat.Coprime.pow_left _ (by norm_num)
  rwa [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1

theorem exists_smul_eq_of_perp_two {y z : Fin 2 → K} (hy0 : y ≠ 0) (hy : herm frob y y = 0)
    (hzy : herm frob z y = 0) : ∃ c : K, z = c • y := by
  have hsum : ∀ a b : Fin 2 → K, herm frob a b = frob (a 0) * b 0 + frob (a 1) * b 1 := by
    intro a b
    rw [herm_def, Fin.sum_univ_two]
  rw [hsum] at hy hzy
  have hy00 : y 0 ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul, zero_add] at hy
    have h1 : y 1 = 0 := by
      by_contra h1
      rw [frob_mul_self h1] at hy
      exact one_ne_zero hy
    exact hy0 (funext fun i => by fin_cases i <;> simp [h0, h1])
  have hy10 : y 1 ≠ 0 := by
    intro h1
    rw [h1, map_zero, zero_mul, add_zero, frob_mul_self hy00] at hy
    exact one_ne_zero hy
  refine ⟨z 0 / y 0, funext fun i => ?_⟩
  fin_cases i
  · simp [div_mul_cancel₀ _ hy00]
  · simp only [Pi.smul_apply, smul_eq_mul]
    have e1 : frob (z 1) * y 1 = frob (z 0) * y 0 := by
      have := eq_neg_of_add_eq_zero_right hzy
      rw [this, neg_K]
    have n0 := frob_mul_self hy00
    have n1 := frob_mul_self hy10
    apply frob.injective
    rw [map_mul, map_div₀]
    have hfy0 : frob (y 0) ≠ 0 := frob_ne_zero hy00
    field_simp
    have e2 : frob (z 1) * frob (y 0) * (y 0 * y 1) = frob (z 0) * frob (y 1) * (y 0 * y 1) := by
      calc frob (z 1) * frob (y 0) * (y 0 * y 1)
          = (frob (z 1) * y 1) * (frob (y 0) * y 0) := by ring
        _ = (frob (z 0) * y 0) * 1 := by rw [e1, n0]
        _ = (frob (z 0) * y 0) * (frob (y 1) * y 1) := by rw [n1]
        _ = frob (z 0) * frob (y 1) * (y 0 * y 1) := by ring
    exact mul_right_cancel₀ (mul_ne_zero hy00 hy10) e2

theorem eq_univ_of_isotropic_mem (hk : 2 ≤ k) {U : Set (Fin k → K)} (h0 : (0 : Fin k → K) ∈ U)
    (hadd : ∀ a ∈ U, ∀ b ∈ U, a + b ∈ U)
    (hiso : ∀ z : Fin k → K, herm frob z z = 0 → z ∈ U) (x : Fin k → K) : x ∈ U := by
  have hne : (1 : K) - ω ≠ 0 := sub_ne_zero.2 (Ne.symm omega_ne_one)
  have hs : ∀ (j : Fin k) (c : K), c • (Pi.single j 1 : Fin k → K) ∈ U := by
    intro j c
    obtain ⟨i, hij⟩ := exists_ne_of_two_le hk j
    set e := c * (1 - ω)⁻¹ with he
    have h1 : herm frob (e • (Pi.single i 1 + Pi.single j 1 : Fin k → K))
        (e • (Pi.single i 1 + Pi.single j 1)) = 0 :=
      herm_smul_smul_self (isotropic_single_add_single hij one_ne_zero) e
    have h2 : herm frob (e • (Pi.single i 1 + Pi.single j ω : Fin k → K))
        (e • (Pi.single i 1 + Pi.single j ω)) = 0 :=
      herm_smul_smul_self (isotropic_single_add_single hij omega_ne_zero) e
    have hsj : (Pi.single j ω : Fin k → K) = ω • (Pi.single j 1 : Fin k → K) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    have key : c • (Pi.single j 1 : Fin k → K) =
        e • (Pi.single i 1 + Pi.single j 1 : Fin k → K) +
          e • (Pi.single i 1 + Pi.single j ω) := by
      rw [← smul_add, show (Pi.single i 1 + Pi.single j 1 : Fin k → K) +
          (Pi.single i 1 + Pi.single j ω) = (1 - ω) • (Pi.single j 1 : Fin k → K) by
        rw [hsj]
        linear_combination (norm := module)
          two_eq_zero • ((Pi.single i 1 : Fin k → K) + ω • (Pi.single j 1 : Fin k → K)),
        smul_smul, he, mul_assoc, inv_mul_cancel₀ hne, mul_one]
    rw [key]
    exact hadd _ (hiso _ h1) _ (hiso _ h2)
  rw [← Finset.univ_sum_single x]
  have : ∀ s : Finset (Fin k), ∑ j ∈ s, (Pi.single j (x j) : Fin k → K) ∈ U := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty]; exact h0
    | insert j s hj ih =>
      rw [Finset.sum_insert hj]
      refine hadd _ ?_ _ ih
      rw [show (Pi.single j (x j) : Fin k → K) = x j • (Pi.single j 1 : Fin k → K) by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]]
      exact hs j (x j)
  exact this _

theorem exists_lift_pgroup (hk : 1 ≤ k) {Y : Subgroup (PG (k + 2))} (hY2 : IsPGroup 2 Y)
    (hcent : ∀ x ∈ Y, x * tq (v₀ k) = tq (v₀ k) * x) :
    ∃ Yh : Subgroup (SUid frob (k + 2)),
      Yh.map (QuotientGroup.mk' (Subgroup.center (SUid frob (k + 2)))) = Y ∧
      (∀ x ∈ Yh, QuotientGroup.mk' (Subgroup.center (SUid frob (k + 2))) x = 1 → x = 1) ∧
      (∀ x ∈ Yh, ∃ j : ℕ, x ^ 2 ^ j = 1) ∧ (∀ x ∈ Yh, x • v₀ k = v₀ k) ∧
      ∀ c : SUid frob (k + 2), (∀ x ∈ Y, (QuotientGroup.mk c : PG (k + 2)) * x *
        (QuotientGroup.mk c)⁻¹ ∈ Y) → ∀ x ∈ Yh, c * x * c⁻¹ ∈ Yh := by
  have hm : 3 ≤ k + 2 := by omega
  obtain ⟨Yh, hmap, hinj⟩ := AS35U.exists_lift hm Y hY2
  set f := QuotientGroup.mk' (Subgroup.center (SUid frob (k + 2))) with hf
  have hmk : ∀ x ∈ Yh, f x ∈ Y := fun x hx => hmap ▸ Subgroup.mem_map_of_mem f hx
  have hpow : ∀ x ∈ Yh, ∃ j : ℕ, x ^ 2 ^ j = 1 := by
    intro x hx
    obtain ⟨j, hj⟩ := hY2 ⟨f x, hmk x hx⟩
    refine ⟨j, hinj _ (Yh.pow_mem hx _) ?_⟩
    rw [map_pow]
    exact congrArg Subtype.val hj
  refine ⟨Yh, hmap, hinj, hpow, ?_, ?_⟩
  · intro x hx
    have h1 : tq (x • v₀ k) = tq (v₀ k) := by
      rw [← conj_tq x herm_v₀_v₀, show (QuotientGroup.mk x : PG (k + 2)) = f x from rfl,
        hcent _ (hmk x hx), mul_inv_cancel_right]
    have hx0 : x • v₀ k ≠ 0 := (smul_ne_zero_iff_ne x).2 v₀_ne_zero
    obtain ⟨c, hc⟩ := (tq_eq_tq_iff hm hx0 (by rw [herm_smul_smul, herm_v₀_v₀]) v₀_ne_zero
      herm_v₀_v₀).1 h1
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact v₀_ne_zero hc
    have hxv : x • v₀ k = c⁻¹ • v₀ k := by
      calc x • v₀ k = c⁻¹ • (c • (x • v₀ k)) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
        _ = c⁻¹ • v₀ k := by rw [← hc]
    have hpowv : ∀ m : ℕ, x ^ m • v₀ k = c⁻¹ ^ m • v₀ k := by
      intro m
      induction m with
      | zero => rw [pow_zero, pow_zero, one_smul, one_smul]
      | succ m ih => rw [pow_succ, mul_smul, hxv, smul_comm, ih, smul_smul, ← pow_succ']
    obtain ⟨j, hj⟩ := hpow x hx
    have h2 : (c⁻¹ ^ 2 ^ j - 1) • v₀ k = 0 := by
      rw [sub_smul, ← hpowv, hj, one_smul, one_smul, sub_self]
    have h3 : c⁻¹ ^ 2 ^ j = 1 :=
      sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right v₀_ne_zero)
    rw [hxv, eq_one_of_pow_two_pow_K (inv_ne_zero hc0) h3, one_smul]
  · intro c hc x hx
    set w := c * x * c⁻¹ with hw
    have hfw : f w ∈ Y := by
      rw [hw, map_mul, map_mul, map_inv]
      exact hc _ (hmk x hx)
    rw [← hmap] at hfw
    obtain ⟨y, hy, hyw⟩ := Subgroup.mem_map.1 hfw
    have hζ : y⁻¹ * w ∈ Subgroup.center (SUid frob (k + 2)) := QuotientGroup.eq.1 hyw
    obtain ⟨a, ha⟩ := hpow y hy
    obtain ⟨b, hb⟩ := hpow x hx
    have hwb : w ^ 2 ^ b = 1 := by
      rw [hw, conj_pow, hb, mul_one, mul_inv_cancel]
    have hcomm : Commute y (y⁻¹ * w) := (Subgroup.mem_center_iff.1 hζ) y
    have hζ2 : (y⁻¹ * w) ^ 2 ^ (a + b) = 1 := by
      have e : w = y * (y⁻¹ * w) := by group
      have h1 : w ^ 2 ^ (a + b) = y ^ 2 ^ (a + b) * (y⁻¹ * w) ^ 2 ^ (a + b) := by
        conv_lhs => rw [e]
        exact hcomm.mul_pow _
      have hw1 : w ^ 2 ^ (a + b) = 1 := by rw [pow_add, mul_comm, pow_mul, hwb, one_pow]
      have hy1 : y ^ 2 ^ (a + b) = 1 := by rw [pow_add, pow_mul, ha, one_pow]
      rw [hw1, hy1, one_mul] at h1
      exact h1.symm
    have hζ1 := AS35U.eq_one_of_mem_center hm hζ hζ2
    have hwy : w = y := by rw [← mul_inv_cancel_left y w, hζ1, mul_one]
    rw [hwy]
    exact hy

theorem two_pow_le_card_of_normalized (hk : 2 ≤ k) {Y : Subgroup (PG (k + 2))}
    (hY2 : IsPGroup 2 Y) (hτ : tq (v₀ k) ∈ Y)
    (hcent : ∀ x ∈ Y, x * tq (v₀ k) = tq (v₀ k) * x)
    (hnorm : ∀ c : PG (k + 2), c * tq (v₀ k) = tq (v₀ k) * c → ∀ x ∈ Y, c * x * c⁻¹ ∈ Y)
    (hne : ∃ y ∈ Y, y ≠ 1 ∧ y ≠ tq (v₀ k)) :
    2 ^ (2 * k + 1) ≤ Nat.card Y := by
  have hm : 3 ≤ k + 2 := by omega
  obtain ⟨Yh, hmap, hinj, hpow, hfix, hconj⟩ := exists_lift_pgroup (by omega) hY2 hcent
  set f := QuotientGroup.mk' (Subgroup.center (SUid frob (k + 2))) with hf
  have hNS : Yh ≤ Stab k := fun x hx => MulAction.mem_stabilizer_iff.2 (hfix x hx)
  have hτz : ∀ z : Fin k → K, z ≠ 0 → herm frob z z = 0 → ∀ x ∈ Yh,
      tvU (ι k z) * x * tvU (ι k z) ∈ Yh := by
    intro z _ hz x hx
    have hz' : herm frob (ι k z) (ι k z) = 0 := by rw [herm_ι_ι, hz]
    have h := hconj (tvU (ι k z)) (fun y hy => hnorm _ (tq_ι_mul_tq_v₀ hz) y hy) x hx
    rwa [tvU_inv hz'] at h
  set P : Subgroup (GL (Fin k) K) := (Yh.subgroupOf (Stab k)).map (rho k) with hP
  have hP2 : IsPGroup 2 P := by
    rintro ⟨p, hp⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hp
    obtain ⟨j, hj⟩ := hpow _ (Subgroup.mem_subgroupOf.1 hx)
    refine ⟨j, Subtype.ext ?_⟩
    have hx2 : x ^ 2 ^ j = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hj)
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, hx2, map_one]
  have hPn : ∀ z : Fin k → K, z ≠ 0 → herm frob z z = 0 → ∀ p ∈ P,
      ((tvU z : SUid frob k) : GL (Fin k) K)⁻¹ * p * (tvU z : SUid frob k) ∈ P := by
    intro z hz0 hz p hp
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hp
    have hz' : herm frob (ι k z) (ι k z) = 0 := by rw [herm_ι_ι, hz]
    have hvz : herm frob (v₀ k) (ι k z) = 0 := herm_v₀_ι z
    have hρt : rho k ⟨tvU (ι k z), tvU_mem_Stab hz' hvz⟩ =
        ((tvU z : SUid frob k) : GL (Fin k) K) := by
      have := rho_tvU hz' hvz
      rwa [π_ι] at this
    rw [← hρt, ← map_inv, ← map_mul, ← map_mul]
    refine Subgroup.mem_map.2 ⟨_, Subgroup.mem_subgroupOf.2 ?_, rfl⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, tvU_inv hz']
    exact hτz z hz0 hz _ (Subgroup.mem_subgroupOf.1 hx)
  have hPbot := eq_bot_of_isPGroup_of_normalized hk hP2 hPn
  have hρ : ∀ x ∈ Yh, ∀ z, π k (x • ι k z) = z := by
    intro x hx
    have hmem : rho k ⟨x, hNS hx⟩ ∈ P :=
      Subgroup.mem_map.2 ⟨⟨x, hNS hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    rw [hPbot, Subgroup.mem_bot] at hmem
    exact (rho_eq_one_iff _).1 hmem
  set U : Set (Fin k → K) := {d | ∃ x ∈ Yh, π k (x • u₀ k) = d} with hU
  have hU0 : (0 : Fin k → K) ∈ U := ⟨1, Yh.one_mem, by rw [one_smul, π_u₀]⟩
  have hUadd : ∀ a ∈ U, ∀ b ∈ U, a + b ∈ U := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨x * y, Yh.mul_mem hx hy, pi_mul_smul_u₀ (hfix x hx) (hρ x hx) (hfix y hy)⟩
  have hUtv : ∀ z : Fin k → K, z ≠ 0 → herm frob z z = 0 → ∀ a ∈ U, tvU z • a ∈ U := by
    rintro z hz0 hz _ ⟨x, hx, rfl⟩
    exact ⟨_, hτz z hz0 hz x hx, pi_conj_smul_u₀ hz x (hfix x hx)⟩
  have hUh : ∀ a ∈ U, ∀ z : Fin k → K, herm frob z z = 0 → herm frob z a • z ∈ U := by
    intro a ha z hz
    by_cases hz0 : z = 0
    · rw [hz0, smul_zero]
      exact hU0
    have h1 := hUadd _ (hUtv z hz0 hz a ha) a ha
    have e : tvU z • a + a = herm frob z a • z := by
      rw [tvU_smul hz, add_comm, ← add_assoc, ← two_smul K a, two_eq_zero, zero_smul, zero_add]
    rwa [e] at h1
  obtain ⟨y, hyY, hy1, hyτ⟩ := hne
  have hyY' := hyY
  rw [← hmap] at hyY'
  obtain ⟨x₁, hx₁, rfl⟩ := Subgroup.mem_map.1 hyY'
  have ha0 : π k (x₁ • u₀ k) ≠ 0 := by
    intro h0
    rcases eq_one_or_eq_tvU_of_fix (hfix x₁ hx₁) (fun z => by
        rw [smul_ι_eq_of_rho (hfix x₁ hx₁) (hρ x₁ hx₁), h0, herm_zero_left, zero_smul,
          add_zero]) with h | h
    · exact hy1 (by rw [h, map_one])
    · exact hyτ (by rw [h]; rfl)
  obtain ⟨z, hz, hza⟩ : ∃ z : Fin k → K, herm frob z z = 0 ∧
      herm frob z (π k (x₁ • u₀ k)) ≠ 0 := by
    by_contra h
    push Not at h
    exact ha0 (eq_zero_of_forall_isotropic hk h)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hza (herm_zero_left frob _)
  set y₀ := herm frob z (π k (x₁ • u₀ k)) • z with hy₀
  have hy₀U : y₀ ∈ U := hUh _ ⟨x₁, hx₁, rfl⟩ z hz
  have hy₀0 : y₀ ≠ 0 := smul_ne_zero hza hz0
  have hy₀iso : herm frob y₀ y₀ = 0 := herm_smul_smul_self hz _
  have hiso : ∀ w : Fin k → K, herm frob w w = 0 → w ∈ U := by
    rcases Nat.lt_or_ge k 3 with hk3 | hk3
    · obtain rfl : k = 2 := by omega
      have hω : ∀ a ∈ U, ω • a ∈ U := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨_, hconj sω (fun y hy => hnorm _ sω_mem_centralizer y hy) x hx,
          pi_conj_sω_smul_u₀ (hfix x hx)⟩
      have hsmul : ∀ c : K, ∀ a ∈ U, c • a ∈ U := by
        intro c a ha
        rcases K_cases c with rfl | rfl | rfl | rfl
        · rw [zero_smul]; exact hU0
        · rw [one_smul]; exact ha
        · exact hω a ha
        · rw [mul_smul]; exact hω _ (hω a ha)
      intro w hw
      by_cases hwy : herm frob w y₀ = 0
      · obtain ⟨c, rfl⟩ := exists_smul_eq_of_perp_two hy₀0 hy₀iso hwy
        exact hsmul c _ hy₀U
      · have h1 := hsmul (herm frob w y₀)⁻¹ _ (hUh _ hy₀U w hw)
        rwa [smul_smul, inv_mul_cancel₀ hwy, one_smul] at h1
    · have hUT : ∀ g ∈ T frob k, ∀ a ∈ U, g • a ∈ U := by
        intro g hg
        rw [T_eq_closure_tvU] at hg
        refine (Subgroup.closure_induction
          (p := fun g _ => (∀ a ∈ U, g • a ∈ U) ∧ ∀ a ∈ U, g⁻¹ • a ∈ U) ?_ ?_ ?_ ?_ hg).1
        · rintro _ ⟨v, hv0, hv, rfl⟩
          refine ⟨hUtv v hv0 hv, ?_⟩
          rw [tvU_inv hv]
          exact hUtv v hv0 hv
        · exact ⟨fun a ha => by rwa [one_smul], fun a ha => by rwa [inv_one, one_smul]⟩
        · intro x y _ _ hx hy
          refine ⟨fun a ha => ?_, fun a ha => ?_⟩
          · rw [mul_smul]
            exact hx.1 _ (hy.1 a ha)
          · rw [_root_.mul_inv_rev, mul_smul]
            exact hy.2 _ (hx.2 a ha)
        · intro x _ hx
          exact ⟨hx.2, fun a ha => by rw [inv_inv]; exact hx.1 a ha⟩
      intro w hw
      by_cases hw0 : w = 0
      · rw [hw0]; exact hU0
      obtain ⟨g, hg, hgw⟩ :=
        exists_mem_T_smul_eq_of_iso isUnitaryInvolution_frob hk3 hy₀0 hy₀iso hw0 hw
      rw [← hgw]
      exact hUT g hg _ hy₀U
  have hUall : ∀ v : Fin k → K, v ∈ U := eq_univ_of_isotropic_mem hk hU0 hUadd hiso
  let d : Yh →* Multiplicative (Fin k → K) :=
    { toFun := fun x => Multiplicative.ofAdd (π k ((x : SUid frob (k + 2)) • u₀ k))
      map_one' := by
        simp only [OneMemClass.coe_one, one_smul, π_u₀, ofAdd_zero]
      map_mul' := fun x y => by
        simp only [Subgroup.coe_mul]
        rw [pi_mul_smul_u₀ (hfix x x.2) (hρ x x.2) (hfix y y.2), ofAdd_add] }
  have hdsurj : d.range = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨x, hx, hxv⟩ := hUall (Multiplicative.toAdd v)
    exact ⟨⟨x, hx⟩, by
      change Multiplicative.ofAdd (π k (x • u₀ k)) = v
      rw [hxv]
      rfl⟩
  have hτ' := hτ
  rw [← hmap] at hτ'
  obtain ⟨x₀, hx₀, hx₀τ⟩ := Subgroup.mem_map.1 hτ'
  have hx₀1 : (⟨x₀, hx₀⟩ : Yh) ≠ 1 := by
    intro h1
    have h1' : x₀ = 1 := congrArg Subtype.val h1
    rw [h1', map_one] at hx₀τ
    exact tq_ne_one hm v₀_ne_zero herm_v₀_v₀ hx₀τ.symm
  have hx₀ker : (⟨x₀, hx₀⟩ : Yh) ∈ d.ker := by
    rw [MonoidHom.mem_ker]
    change Multiplicative.ofAdd (π k (x₀ • u₀ k)) = 1
    have hζ : (tvU (v₀ k))⁻¹ * x₀ ∈ Subgroup.center (SUid frob (k + 2)) :=
      QuotientGroup.eq.1 hx₀τ.symm
    rw [center_SUid hm] at hζ
    obtain ⟨c, hc⟩ := exists_smul_eq_of_mem_scalars hζ
    have e : x₀ • u₀ k = c • (tvU (v₀ k) • u₀ k) := by
      rw [← smul_comm (tvU (v₀ k)) c (u₀ k), ← hc, ← mul_smul, mul_inv_cancel_left]
    rw [e, tvU_smul herm_v₀_v₀, herm_v₀_u₀, one_smul]
    simp only [map_smul, map_add, π_u₀, π_v₀, add_zero, smul_zero, ofAdd_zero]
  have hker : 1 < Nat.card d.ker :=
    (Subgroup.one_lt_card_iff_ne_bot _).2 fun hbot => hx₀1 (by
      rw [hbot] at hx₀ker
      exact hx₀ker)
  have hcardYh : Nat.card Yh = Nat.card d.ker * 4 ^ k := by
    have h1 := Subgroup.card_mul_index d.ker
    rw [Subgroup.index_ker, hdsurj, Subgroup.card_top] at h1
    have h2 : Nat.card (Multiplicative (Fin k → K)) = 4 ^ k := by
      change Nat.card (Fin k → K) = 4 ^ k
      rw [Nat.card_fun, card_K, Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num
    rw [← h1, h2]
  have hinjOn : Set.InjOn f Yh := by
    intro a ha b hb hab
    have h1 := hinj (a⁻¹ * b) (Yh.mul_mem (Yh.inv_mem ha) hb) (by
      rw [map_mul, map_inv, hab, inv_mul_cancel])
    rw [← mul_inv_cancel_left a b, h1, mul_one]
  have hcardY : Nat.card Y = Nat.card Yh := by
    rw [← hmap]
    change Nat.card (↑(Yh.map f) : Set (PG (k + 2))) =
      Nat.card ((Yh : Set (SUid frob (k + 2))))
    rw [Subgroup.coe_map, Nat.card_image_of_injOn hinjOn]
  rw [hcardY, hcardYh, pow_succ, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num, mul_comm]
  exact Nat.mul_le_mul_right _ hker

end CFSG.LargeExtraspecial.AS35Z
