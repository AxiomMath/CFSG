module

public import CFSG.CharacterTheory.Wreathed.BrauerWongOmega

public noncomputable section

namespace CFSG.Wreathed.AdaptedBaseFusion

open CFSG.Wreathed CFSG.Wreathed.BrauerWong

universe u

variable {G : Type u} [Group G]

theorem eq_pow_half_of_mem_zpowers {n : ℕ} (hn : 1 ≤ n) {x c : G} (hx : orderOf x = 2 ^ n)
    (hc : c ∈ Subgroup.zpowers x) (hc2 : orderOf c = 2) : c = x ^ 2 ^ (n - 1) := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have hsq : (x ^ i) ^ (2 : ℕ) = 1 := by rw [← hc2]; exact pow_orderOf_eq_one _
  rw [← zpow_natCast, ← zpow_mul, ← orderOf_dvd_iff_zpow_eq_one, hx] at hsq
  have htwo : ((2 ^ n : ℕ) : ℤ) = 2 * 2 ^ (n - 1) := by
    rw [← twice_half_two_pow n hn]
    push_cast
    ring
  rw [htwo] at hsq
  push_cast at hsq
  rw [mul_comm i] at hsq
  have hsq' : (2 : ℤ) ^ (n - 1) ∣ i := (mul_dvd_mul_iff_left (two_ne_zero)).mp hsq
  obtain ⟨l, rfl⟩ := hsq'
  have hy2 : (x ^ 2 ^ (n - 1)) ^ 2 = 1 := by
    rw [← pow_mul, ← pow_succ, show n - 1 + 1 = n by omega, ← hx]
    exact pow_orderOf_eq_one x
  have hpow : x ^ ((2 : ℤ) ^ (n - 1) * l) = (x ^ 2 ^ (n - 1)) ^ l := by
    rw [zpow_mul]
    norm_cast
  rw [hpow]
  rcases Int.emod_two_eq_zero_or_one l with hl | hl
  · exfalso
    have : (x ^ 2 ^ (n - 1)) ^ l = 1 := by
      obtain ⟨q, hq⟩ := Int.dvd_of_emod_eq_zero hl
      rw [hq, zpow_mul]
      norm_cast
      rw [hy2, one_zpow]
    rw [hpow, this, orderOf_one] at hc2
    omega
  · have hl' : l = 2 * (l / 2) + 1 := by omega
    rw [hl', zpow_add, zpow_mul]
    norm_cast
    rw [hy2, one_zpow, one_mul, pow_one]

theorem exists_pow_eq_pow_half {n : ℕ} (hn : 1 ≤ n) {x c : G} (hx : orderOf x = 2 ^ n)
    (hc : c ∈ Subgroup.zpowers x) (hc1 : c ≠ 1) :
    ∃ k : ℕ, c ^ k = x ^ 2 ^ (n - 1) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : orderOf c ∣ 2 ^ n := hx ▸ orderOf_dvd_of_mem_zpowers hc
  obtain ⟨r, hr, hcr⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hcr
    exact hc1 hcr
  have hord0 : orderOf c ≠ 0 := by rw [hcr]; positivity
  have h2 : 2 ∣ orderOf c := by rw [hcr]; exact dvd_pow_self 2 hr0
  refine ⟨orderOf c / 2, ?_⟩
  apply eq_pow_half_of_mem_zpowers hn hx _ (orderOf_pow_orderOf_div hord0 h2)
  exact Subgroup.pow_mem _ hc _

theorem zpowers_inf_eq_bot_of_pow_half_ne {n : ℕ} (hn : 1 ≤ n) {σ υ : G}
    (hσ : orderOf σ = 2 ^ n) (hυ : orderOf υ = 2 ^ n)
    (hne : σ ^ 2 ^ (n - 1) ≠ υ ^ 2 ^ (n - 1)) :
    Subgroup.zpowers σ ⊓ Subgroup.zpowers υ = ⊥ := by
  rw [eq_bot_iff]
  rintro c ⟨hcσ, hcυ⟩
  rw [Subgroup.mem_bot]
  by_contra hc1
  obtain ⟨k, hk⟩ := exists_pow_eq_pow_half hn hσ hcσ hc1
  have hk' : c ^ k = υ ^ 2 ^ (n - 1) := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply eq_pow_half_of_mem_zpowers hn hυ (Subgroup.pow_mem _ hcυ _)
    rw [hk]
    have hy2 : (σ ^ 2 ^ (n - 1)) ^ 2 = 1 := by
      rw [← pow_mul, ← pow_succ, show n - 1 + 1 = n by omega, ← hσ]
      exact pow_orderOf_eq_one σ
    apply orderOf_eq_prime hy2
    intro h1
    have := orderOf_le_of_pow_eq_one (pow_pos two_pos (n - 1)) h1
    rw [hσ] at this
    have : 2 ^ n ≤ 2 ^ (n - 1) := this
    have h' : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  exact hne (hk.symm.trans hk')

variable {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))

theorem card_modelBase : Nat.card (modelBase S e) = (2 ^ n) ^ 2 := by
  rw [← Nat.card_congr (modelBaseEquiv S e).toEquiv, card_base]

theorem pow_modulus_eq_one_of_mem_modelBase {x : G} (hx : x ∈ modelBase S e) :
    x ^ 2 ^ n = 1 := by
  obtain ⟨w, hw, rfl⟩ := hx
  obtain ⟨⟨i, j, f⟩, rfl⟩ := (coordinateEquiv (2 ^ n)).symm.surjective w
  change element _ i j f ∈ baseSubgroup _ at hw
  rw [element_mem_base] at hw
  subst hw
  rw [← map_pow]
  change wreathModelHom S e (element _ i j 0 ^ 2 ^ n) = 1
  rw [element_base_pow_modulus, map_one]

@[expose] def zpowersMul {σ υ : G} (h : Commute σ υ) :
    Subgroup.zpowers σ × Subgroup.zpowers υ →* G :=
  (Subgroup.zpowers σ).subtype.noncommCoprod (Subgroup.zpowers υ).subtype (by
    rintro ⟨c, hc⟩ ⟨d, hd⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    exact (h.zpow_left i).zpow_right j)

theorem zpowersMul_range {σ υ : G} (h : Commute σ υ) :
    (zpowersMul h).range = Subgroup.closure {σ, υ} := by
  apply le_antisymm
  · rintro _ ⟨⟨c, d⟩, rfl⟩
    refine Subgroup.mul_mem _ ?_ ?_
    · exact (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) c.property
    · exact (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) d.property
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨(⟨_, Subgroup.mem_zpowers _⟩, 1), by simp [zpowersMul]⟩
    · exact ⟨(1, ⟨_, Subgroup.mem_zpowers _⟩), by simp [zpowersMul]⟩

theorem zpowersMul_injective {σ υ : G} (h : Commute σ υ)
    (hinf : Subgroup.zpowers σ ⊓ Subgroup.zpowers υ = ⊥) :
    Function.Injective (zpowersMul h) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨c, d⟩ hcd
  change (c : G) * d = 1 at hcd
  have hc : (c : G) ∈ Subgroup.zpowers σ ⊓ Subgroup.zpowers υ := by
    refine ⟨c.property, ?_⟩
    rw [eq_inv_of_mul_eq_one_left hcd]
    exact Subgroup.inv_mem _ d.property
  rw [hinf, Subgroup.mem_bot] at hc
  rw [hc, one_mul] at hcd
  rw [Subgroup.mem_bot]
  exact Prod.ext (Subtype.ext hc) (Subtype.ext hcd)

variable [Finite G]

theorem closure_pair_eq_modelBase_iff {σ υ : G} (hσ : σ ∈ modelBase S e)
    (hυ : υ ∈ modelBase S e) :
    Subgroup.closure {σ, υ} = modelBase S e ↔
      orderOf σ = 2 ^ n ∧ orderOf υ = 2 ^ n ∧
        Subgroup.zpowers σ ⊓ Subgroup.zpowers υ = ⊥ := by
  have hcomm : Commute σ υ := modelBase_commute S e σ υ hσ hυ
  have hdvdσ : orderOf σ ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one
    (pow_modulus_eq_one_of_mem_modelBase S e hσ)
  have hdvdυ : orderOf υ ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one
    (pow_modulus_eq_one_of_mem_modelBase S e hυ)
  have hleσ := Nat.le_of_dvd (pow_pos two_pos n) hdvdσ
  have hleυ := Nat.le_of_dvd (pow_pos two_pos n) hdvdυ
  have hdom : Nat.card (Subgroup.zpowers σ × Subgroup.zpowers υ) = orderOf σ * orderOf υ := by
    rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers]
  constructor
  · intro hcl
    have hsurj : Function.Surjective (zpowersMul hcomm).rangeRestrict :=
      MonoidHom.rangeRestrict_surjective _
    have hle := Nat.card_le_card_of_surjective _ hsurj
    rw [zpowersMul_range, hcl, card_modelBase, hdom] at hle
    have hσeq : orderOf σ = 2 ^ n := by
      by_contra hne
      have hlt : orderOf σ < 2 ^ n := lt_of_le_of_ne hleσ hne
      have := Nat.mul_lt_mul_of_lt_of_le hlt hleυ (pow_pos two_pos n)
      rw [sq] at hle
      omega
    have hυeq : orderOf υ = 2 ^ n := by
      by_contra hne
      have hlt : orderOf υ < 2 ^ n := lt_of_le_of_ne hleυ hne
      have := Nat.mul_lt_mul_of_le_of_lt hleσ hlt (pow_pos two_pos n)
      rw [sq] at hle
      omega
    refine ⟨hσeq, hυeq, ?_⟩
    have hbij := (Function.Surjective.bijective_of_nat_card_le hsurj (by
      rw [zpowersMul_range, hcl, card_modelBase, hdom, hσeq, hυeq, sq]))
    rw [eq_bot_iff]
    intro c ⟨hcσ, hcυ⟩
    have h := hbij.1 (a₁ := (⟨c, hcσ⟩, ⟨c⁻¹, Subgroup.inv_mem _ hcυ⟩)) (a₂ := 1) (by
      apply Subtype.ext
      change c * c⁻¹ = (1 : G) * 1
      rw [mul_inv_cancel, one_mul])
    have := congrArg (fun p => (p.1 : G)) h
    simpa using this
  · rintro ⟨hσeq, hυeq, hinf⟩
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hσ
      · exact hυ
    · have hinj := zpowersMul_injective hcomm hinf
      have hcard : Nat.card (zpowersMul hcomm).range = (2 ^ n) ^ 2 := by
        rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hdom, hσeq, hυeq, sq]
      rw [← zpowersMul_range hcomm]
      apply le_of_eq
      symm
      apply Subgroup.eq_of_le_of_card_ge
      · rw [zpowersMul_range]
        rw [Subgroup.closure_le]
        rintro _ (rfl | rfl)
        · exact hσ
        · exact hυ
      · rw [hcard, card_modelBase]

theorem closure_pair_eq_modelBase_of_pow_half (hn : 2 ≤ n) {σ υ : G}
    (hσ : σ ∈ modelBase S e) (hυ : υ ∈ modelBase S e) (hσ1 : σ ^ 2 ^ (n - 1) ≠ 1)
    (hυ1 : υ ^ 2 ^ (n - 1) ≠ 1) (hne : σ ^ 2 ^ (n - 1) ≠ υ ^ 2 ^ (n - 1)) :
    Subgroup.closure {σ, υ} = modelBase S e := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord (x : G) (hx : x ∈ modelBase S e) (hx1 : x ^ 2 ^ (n - 1) ≠ 1) :
      orderOf x = 2 ^ n := by
    have h := orderOf_eq_prime_pow (p := 2) (n := n - 1) hx1 (by
      rw [show n - 1 + 1 = n by omega]
      exact pow_modulus_eq_one_of_mem_modelBase S e hx)
    rwa [show n - 1 + 1 = n by omega] at h
  have hσo := hord σ hσ hσ1
  have hυo := hord υ hυ hυ1
  exact (closure_pair_eq_modelBase_iff S e hσ hυ).mpr
    ⟨hσo, hυo, zpowers_inf_eq_bot_of_pow_half_ne (by omega) hσo hυo hne⟩

end CFSG.Wreathed.AdaptedBaseFusion
