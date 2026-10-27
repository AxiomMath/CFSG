module

public import CFSG.HardMathSupport.Dickson.I271.Support.CyclicCenter

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.U43Six
  CFSG.LieType.Multipliers.U43 Subgroup

theorem psub_conj_mem_A {y a : X₀} (hy : y ∈ Psub) (ha : a ∈ thetaBar.range) :
    y * a * y⁻¹ ∈ thetaBar.range := by
  obtain ⟨a₁, ha₁, t, ht, rfl⟩ := hy
  have h1 := tBar_mem_normalizer ht ha
  have h2 : a₁ * t * a * (a₁ * t)⁻¹ = a₁ * (t * a * t⁻¹) * a₁⁻¹ := by group
  rw [h2]
  exact thetaBar.range.mul_mem (thetaBar.range.mul_mem ha₁ h1) (thetaBar.range.inv_mem ha₁)

theorem exists_conj_mem_Psub (x : X₀) (hx : x ^ 3 = 1) : ∃ g : X₀, g * x * g⁻¹ ∈ Psub := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.card X₀).factorization 3 = 6 := by
    rw [CFSG.LieType.Multipliers.U43.card_X₀]
    have h6 := (Nat.prime_three.pow_dvd_iff_le_factorization (by norm_num : (3265920 : ℕ) ≠ 0)).1
      (by norm_num : 3 ^ 6 ∣ 3265920)
    have h7 : ¬ 7 ≤ (3265920 : ℕ).factorization 3 := fun h =>
      absurd ((Nat.prime_three.pow_dvd_iff_le_factorization (by norm_num : (3265920 : ℕ) ≠ 0)).2 h)
        (by norm_num)
    omega
  let P0 : Sylow 3 X₀ := Sylow.ofCard Psub (by rw [card_Psub, hfac])
  have hpg : IsPGroup 3 (Subgroup.zpowers x) := by
    have hord : orderOf x ∣ 3 ^ 1 := orderOf_dvd_of_pow_eq_one (by simpa using hx)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hord
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  obtain ⟨Q, hxQ⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X₀ P0 Q
  have hxQ' : x ∈ (Q : Subgroup X₀) := hxQ (Subgroup.mem_zpowers x)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ'
  refine ⟨g⁻¹, ?_⟩
  have h3 : g⁻¹ * x * g ∈ (P0 : Subgroup X₀) := by simpa using hxQ'
  have h4 : g⁻¹ * x * g ∈ Psub := h3
  simpa using h4

theorem exists_pow_three_ne_one (s : Multiplicative F9) (hs : s ≠ 1) :
    ∃ b ∈ thetaBar.range, (b * tBar s) ^ 3 ≠ 1 := by
  have hs0 : s.toAdd ≠ 0 := fun h => hs (Multiplicative.toAdd.injective h)
  have hcub : ∀ s : Multiplicative F9, s ^ 3 = 1 := by decide
  have hnorm : ∀ s : F9, s ≠ 0 →
      ((0 : ZMod 3), (1 : ZMod 3), (0 : ZMod 3), (0 : ZMod 3)) + act s (0, 1, 0, 0) +
        act s (act s (0, 1, 0, 0)) ≠ 0 := by decide +kernel
  set x : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) := Multiplicative.ofAdd (0, 1, 0, 0)
  refine ⟨thetaBar x, ⟨x, rfl⟩, ?_⟩
  intro h
  set t := tBar s with ht
  have h3 : t ^ 3 = 1 := by rw [ht, ← map_pow, hcub, map_one]
  have h1 : t * thetaBar x * t⁻¹ = thetaBar (Multiplicative.ofAdd (act s.toAdd x.toAdd)) :=
    tBar_conj s x
  have h2 : t * thetaBar (Multiplicative.ofAdd (act s.toAdd x.toAdd)) * t⁻¹ =
      thetaBar (Multiplicative.ofAdd (act s.toAdd (act s.toAdd x.toAdd))) := by
    have := tBar_conj s (Multiplicative.ofAdd (act s.toAdd x.toAdd))
    simpa using this
  have hexp : (thetaBar x * t) ^ 3 = thetaBar x * (t * thetaBar x * t⁻¹) *
      (t * (t * thetaBar x * t⁻¹) * t⁻¹) * t ^ 3 := by
    rw [pow_succ, pow_succ, pow_one]
    group
  rw [hexp, h3, h1, h2, mul_one, ← map_mul, ← map_mul] at h
  have hinj := thetaBar_injective (h.trans (map_one thetaBar).symm)
  apply hnorm s.toAdd hs0
  have := congrArg Multiplicative.toAdd hinj
  simpa [x] using this

section Core

variable {K : Type} [Group K] [Finite K]

theorem nineFold_core (φ : K →* X₀) (hφ : Function.Surjective φ) (hker : φ.ker = Subgroup.center K)
    (hZ9 : Nat.card (Subgroup.center K) = 9) (hZ3 : ∀ z ∈ Subgroup.center K, z ^ 3 = 1)
    {k : K} (hkZ : k ∉ Subgroup.center K) (hk3 : k ^ 3 ∈ Subgroup.center K) (hkP : φ k ∈ Psub) :
    ∃ x : K, x ^ 3 = 1 ∧ x * k = k * x ∧ x ∉ Subgroup.zpowers k ⊔ Subgroup.center K := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  set Z := Subgroup.center K with hZdef
  set D : Subgroup K := thetaBar.range.comap φ with hD
  have hker' : φ.ker ≤ Subgroup.center K := hker.le
  have hmemD : ∀ x : K, x ∈ D ↔ φ x ∈ thetaBar.range := fun x => Iff.rfl
  have hZD : Z ≤ D := fun z hz => by
    rw [hmemD, show φ z = 1 from MonoidHom.mem_ker.1 (hker ▸ hz)]
    exact thetaBar.range.one_mem
  have hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    commute_of_mem_range hφ hker' hx hy
  have hD3 : ∀ x ∈ D, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨y, hy, hy3⟩ := exists_lift_of_mem_range hφ hker' (e := φ x) hx
    have hz : y⁻¹ * x ∈ Z := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hy, inv_mul_cancel]
    have hcomm : Commute y (y⁻¹ * x) := Subgroup.mem_center_iff.1 hz y
    have hxy : x = y * (y⁻¹ * x) := by group
    rw [hxy, hcomm.mul_pow, hy3, hZ3 _ hz, one_mul]
  by_cases hkA : φ k ∈ thetaBar.range
  ·
    have hkD : k ∈ D := hkA
    have hk1 : k ^ 3 = 1 := hD3 k hkD
    by_contra hno
    push Not at hno
    have hDM : D ≤ Z ⊔ Subgroup.zpowers k := by
      intro x hx
      rw [sup_comm]
      exact hno x (hD3 x hx) (hDab x hx k hkD)
    have hMcard : Nat.card ↥(Z ⊔ Subgroup.zpowers k) = 27 := by
      rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp3 Z hk1 hkZ
        (fun e he => (Subgroup.mem_center_iff.1 he k).symm), hZ9]
    have hAD : Nat.card thetaBar.range ≤ Nat.card D := by
      refine Nat.card_le_card_of_surjective (fun d : D => (⟨φ d, d.2⟩ : thetaBar.range)) ?_
      rintro ⟨a, ha⟩
      obtain ⟨d, rfl⟩ := hφ a
      exact ⟨⟨d, ha⟩, rfl⟩
    have := Subgroup.card_le_of_le hDM
    rw [card_range_thetaBar] at hAD
    omega
  ·
    obtain ⟨a, ha, t, ⟨s, rfl⟩, hat⟩ := hkP
    have hs : s ≠ 1 := by
      rintro rfl
      apply hkA
      rw [hat, map_one, mul_one]
      exact ha
    obtain ⟨b, hbA, hb3⟩ := exists_pow_three_ne_one s hs
    obtain ⟨d, hd⟩ := hφ (b * a⁻¹)
    have hdD : d ∈ D := by
      rw [hmemD, hd]
      exact thetaBar.range.mul_mem hbA (thetaBar.range.inv_mem ha)
    have hkn : ∀ y ∈ D, k * y * k⁻¹ ∈ D := by
      intro y hy
      rw [hmemD, map_mul, map_mul, map_inv]
      exact psub_conj_mem_A (hat ▸ ⟨a, ha, tBar s, ⟨s, rfl⟩, rfl⟩) hy
    have hkd : k * d * k⁻¹ ∈ D := hkn d hdD
    have hkkd : k * (k * d * k⁻¹) * k⁻¹ ∈ D := hkn _ hkd
    set x₀ : K := d * (k * d * k⁻¹) * (k * (k * d * k⁻¹) * k⁻¹) with hx₀
    have hx₀D : x₀ ∈ D := D.mul_mem (D.mul_mem hdD hkd) hkkd
    have hcube : (d * k) ^ 3 = x₀ * k ^ 3 := by
      rw [hx₀]
      rw [pow_succ, pow_succ, pow_one, pow_succ, pow_succ, pow_one]
      group
    have hx₀Z : x₀ ∉ Z := by
      intro hx
      have hc : (d * k) ^ 3 ∈ Z := by rw [hcube]; exact Z.mul_mem hx hk3
      apply hb3
      have : φ ((d * k) ^ 3) = 1 := MonoidHom.mem_ker.1 (hker ▸ hc)
      rw [map_pow, map_mul, hd, hat, show b * a⁻¹ * (a * tBar s) = b * tBar s by group] at this
      exact this
    have hx₀k : x₀ * k = k * x₀ := by
      have h1 : k * (k * (k * d * k⁻¹) * k⁻¹) * k⁻¹ = d := by
        have hc : k * (k * k) * d = d * (k * (k * k)) := by
          have := (Subgroup.mem_center_iff.1 hk3 d).symm
          rwa [pow_three] at this
        calc k * (k * (k * d * k⁻¹) * k⁻¹) * k⁻¹ = (k * (k * k)) * d * (k * (k * k))⁻¹ := by
              simp [mul_assoc]
          _ = d := by rw [hc]; exact mul_inv_cancel_right _ _
      have h2 : k * x₀ * k⁻¹ = x₀ := by
        calc k * x₀ * k⁻¹ = (k * d * k⁻¹) * (k * (k * d * k⁻¹) * k⁻¹) *
              (k * (k * (k * d * k⁻¹) * k⁻¹) * k⁻¹) := by rw [hx₀]; group
          _ = (k * d * k⁻¹) * (k * (k * d * k⁻¹) * k⁻¹) * d := by rw [h1]
          _ = d * (k * d * k⁻¹) * (k * (k * d * k⁻¹) * k⁻¹) := by
            have c1 := hDab d hdD _ hkd
            have c2 := hDab d hdD _ hkkd
            calc (k * d * k⁻¹) * (k * (k * d * k⁻¹) * k⁻¹) * d
                = (k * d * k⁻¹) * ((k * (k * d * k⁻¹) * k⁻¹) * d) := by group
              _ = (k * d * k⁻¹) * (d * (k * (k * d * k⁻¹) * k⁻¹)) := by rw [← c2]
              _ = ((k * d * k⁻¹) * d) * (k * (k * d * k⁻¹) * k⁻¹) := by group
              _ = (d * (k * d * k⁻¹)) * (k * (k * d * k⁻¹) * k⁻¹) := by rw [← c1]
          _ = x₀ := hx₀.symm
      exact (mul_inv_eq_iff_eq_mul.1 h2).symm
    refine ⟨x₀, hD3 _ hx₀D, hx₀k, ?_⟩
    intro hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.1 hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hzD : z ∈ D := hZD hz
    have hk3Z : ∀ m : ℤ, (k ^ 3) ^ m ∈ Z := fun m => Z.zpow_mem hk3 m
    have hkiD : k ^ i ∈ D := by
      have : k ^ i = x₀ * z⁻¹ := by rw [← hyz]; group
      rw [this]
      exact D.mul_mem hx₀D (D.inv_mem hzD)
    have hkdec : k ^ i = (k ^ 3) ^ (i / 3) * k ^ (i % 3) := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_add]
      congr 1
      push_cast
      omega
    have hr : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases hr with hr | hr | hr
    · apply hx₀Z
      rw [hkdec, hr, zpow_zero, mul_one] at hyz
      rw [← hyz]
      exact Z.mul_mem (hk3Z _) hz
    · apply hkA
      rw [hkdec, hr, zpow_one] at hkiD
      have : k = ((k ^ 3) ^ (i / 3))⁻¹ * ((k ^ 3) ^ (i / 3) * k) := by group
      rw [this]
      exact D.mul_mem (D.inv_mem (hZD (hk3Z _))) hkiD
    · apply hkA
      rw [hkdec, hr] at hkiD
      have hk2 : k ^ (2 : ℤ) ∈ D := by
        have : k ^ (2 : ℤ) = ((k ^ 3) ^ (i / 3))⁻¹ * ((k ^ 3) ^ (i / 3) * k ^ (2 : ℤ)) := by group
        rw [this]
        exact D.mul_mem (D.inv_mem (hZD (hk3Z _))) hkiD
      have : k = (k ^ (2 : ℤ))⁻¹ * k ^ 3 := by group
      rw [this]
      exact D.mul_mem (D.inv_mem hk2) (hZD hk3)

end Core

theorem kdU43NineFold_holds : KDU43NineFold := by
  intro K _ _ hq ⟨e⟩ hZ9 hZ3 k hkZ hk3
  let φ : K →* X₀ := (e : K ⧸ Subgroup.center K →* X₀).comp (QuotientGroup.mk' (Subgroup.center K))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center K := by
    ext x
    simp [φ]
  have hkbar3 : φ k ^ 3 = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (hker ▸ hk3)
  obtain ⟨g, hg⟩ := exists_conj_mem_Psub (φ k) hkbar3
  obtain ⟨g', rfl⟩ := hφ g
  set k' : K := g' * k * g'⁻¹ with hk'
  have hk'P : φ k' ∈ Psub := by
    rw [hk', map_mul, map_mul, map_inv]
    exact hg
  have hZn : (Subgroup.center K).Normal := inferInstance
  have hk'Z : k' ∉ Subgroup.center K := by
    intro h
    apply hkZ
    have h1 := hZn.conj_mem _ h g'⁻¹
    have h2 : g'⁻¹ * k' * g'⁻¹⁻¹ = k := by rw [hk']; group
    rwa [h2] at h1
  have hk'3 : k' ^ 3 ∈ Subgroup.center K := by
    have := hZn.conj_mem _ hk3 g'
    rwa [hk', conj_pow]
  obtain ⟨x', hx'3, hx'k, hx'M⟩ := nineFold_core φ hφ hker hZ9 hZ3 hk'Z hk'3 hk'P
  refine ⟨g'⁻¹ * x' * g', ?_, ?_, ?_⟩
  · have h1 : (g'⁻¹ * x' * g') ^ 3 = g'⁻¹ * x' ^ 3 * g' := by
      rw [pow_succ, pow_succ, pow_one, pow_succ, pow_succ, pow_one]
      group
    rw [h1, hx'3]
    group
  · have h1 : x' * (g' * k * g'⁻¹) = (g' * k * g'⁻¹) * x' := hx'k
    calc g'⁻¹ * x' * g' * k = g'⁻¹ * (x' * (g' * k * g'⁻¹)) * g' := by group
      _ = g'⁻¹ * ((g' * k * g'⁻¹) * x') * g' := by rw [h1]
      _ = k * (g'⁻¹ * x' * g') := by group
  · intro hmem
    apply hx'M
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.1 hmem
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    refine Subgroup.mem_sup_of_normal_right.2
      ⟨k' ^ i, Subgroup.mem_zpowers_iff.2 ⟨i, rfl⟩, z, hz, ?_⟩
    have hz' : g' * z * g'⁻¹ = z := by
      rw [mul_inv_eq_iff_eq_mul]
      exact Subgroup.mem_center_iff.1 hz g'
    calc k' ^ i * z = (g' * k ^ i * g'⁻¹) * (g' * z * g'⁻¹) := by rw [hk', conj_zpow, hz']
      _ = g' * (k ^ i * z) * g'⁻¹ := by group
      _ = g' * (g'⁻¹ * x' * g') * g'⁻¹ := by rw [hyz]
      _ = x' := by group

section Final


theorem kdCenterCase_holds (hGA : CFSG.Open.GriessAllModelsStatement) : KDCenterCase :=
  kdCenterCase_of_nineFold hGA kdU43NineFold_holds

end Final

end CFSG.HardMathSupport.Dickson.I271
