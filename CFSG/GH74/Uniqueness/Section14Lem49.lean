module

public import CFSG.GH74.Uniqueness.Section14Lem46b
public import CFSG.GH74.Uniqueness.Section14Tools

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] {Z : Set X} {M : Subgroup X} {t : X} {n r : ℕ}
  {L K J Mo P U T S2 : Subgroup X}

theorem commutatorElement_mul_of_commute {G : Type*} [Group G] {x y z₁ z₂ : G}
    (h1x : Commute z₁ x) (h1y : Commute z₁ y) (h2x : Commute z₂ x) (h2y : Commute z₂ y)
    (h12 : Commute z₁ z₂) : ⁅z₁ * x, z₂ * y⁆ = ⁅x, y⁆ := by
  have hA : Commute z₁ (x * z₂ * y * x⁻¹) :=
    ((h1x.mul_right h12).mul_right h1y).mul_right h1x.inv_right
  have hB : Commute z₂ (y * x⁻¹ * y⁻¹) := (h2y.mul_right h2x.inv_right).mul_right h2y.inv_right
  calc ⁅z₁ * x, z₂ * y⁆ = (z₁ * (x * z₂ * y * x⁻¹) * z₁⁻¹) * y⁻¹ * z₂⁻¹ := by
        rw [commutatorElement_def]; group
    _ = x * (z₂ * (y * x⁻¹ * y⁻¹) * z₂⁻¹) := by rw [hA.eq, mul_inv_cancel_right]; group
    _ = ⁅x, y⁆ := by rw [hB.eq, mul_inv_cancel_right, commutatorElement_def]; group

namespace Sec149

theorem exists_odd_part {G : Type*} [Group G] [Finite G] (g : G) :
    ∃ a : ℕ, Odd (orderOf (g ^ 2 ^ a)) := by
  obtain ⟨a, m, hm, hom⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨a, ?_⟩
  rw [orderOf_pow_of_dvd (by positivity) (by rw [hom]; exact dvd_mul_right _ _), hom,
    Nat.mul_div_cancel_left _ (by positivity)]
  exact hm

variable (F : Facts14 Z M t n r L K J Mo P U T S2)
include F

theorem S2_sylow_M [Finite X] (h146 : Concl146 M t n K Mo U T S2) :
    ABGLocalTools.IsSylowOf 2 S2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply ABGLocalTools.isSylowOf_of_card h146.S2_le_M
  have hX : Nat.card S2 = 2 ^ (Nat.card X).factorization 2 := by rw [h146.card_S2, F.two_part]
  rw [hX]
  congr 1
  apply le_antisymm
  · have h1 : Nat.card S2 ∣ Nat.card M := Subgroup.card_dvd_of_le h146.S2_le_M
    rw [hX] at h1
    exact (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h1
  · exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
      (Subgroup.card_subgroup_dvd_card M) 2

theorem odd_centralizes_T [Finite X] {w : X} (hodd : Odd (orderOf w))
    (hwT : ∀ x ∈ T, w * x * w⁻¹ * x⁻¹ ∈ Mo) : w = 1 := by
  have hMoT : ∀ m ∈ Mo, ∀ x ∈ T, m * x = x * m := fun m hm x hx =>
    Sec146.MoU_central F m (mem_sup_left hm) x hx
  have hwMo : ∀ m ∈ Mo, w * m = m * w := by
    have hle : Mo ≤ centralizer ({w} : Set X) := by
      rw [← F.comm_T, commutator_le]
      intro a ha b hb
      rw [mem_centralizer_singleton_iff]
      set ca := w * a * w⁻¹ * a⁻¹ with hca
      set cb := w * b * w⁻¹ * b⁻¹ with hcb
      have hwa : w * a * w⁻¹ = ca * a := by rw [hca]; group
      have hwb : w * b * w⁻¹ = cb * b := by rw [hcb]; group
      have hcaMo := hwT a ha
      have hcbMo := hwT b hb
      have h1 : w * ⁅a, b⁆ * w⁻¹ = ⁅a, b⁆ := by
        have e : w * ⁅a, b⁆ * w⁻¹ = ⁅w * a * w⁻¹, w * b * w⁻¹⁆ := by
          rw [commutatorElement_def, commutatorElement_def]; group
        rw [e, hwa, hwb]
        exact commutatorElement_mul_of_commute (hMoT ca hcaMo a ha) (hMoT ca hcaMo b hb)
          (hMoT cb hcbMo a ha) (hMoT cb hcbMo b hb) (Sec146.Mo_comm F ca hcaMo cb hcbMo)
      calc ⁅a, b⁆ * w = w * ⁅a, b⁆ * w⁻¹ * w := by rw [h1]
        _ = w * ⁅a, b⁆ := by group
    intro m hm
    exact (mem_centralizer_singleton_iff.mp (hle hm)).symm
  have hwTc : ∀ x ∈ T, w * x = x * w := by
    intro x hx
    apply commute_of_odd_of_commutator_mem hodd
    · exact hwMo _ (hwT x hx)
    · exact F.Mo_sq _ (hwT x hx)
  have hwT' := Sec146.cent_MoU_le F fun y hy => hwTc y (Sec146.MoU_le_T F hy)
  have hzodd : Odd (Nat.card (zpowers w)) := by rw [Nat.card_zpowers]; exact hodd
  exact Bender.eq_one_of_isPGroup_two_of_odd F.T_sylow.isPGroup hzodd hwT' (mem_zpowers w)

theorem U_eq [Finite X] (h148 : Nat.card U = 2) {u : X} (hu : u ∈ U) (hu1 : u ≠ 1) :
    ∀ v ∈ U, v = 1 ∨ v = u := by
  classical
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact F.U_sq u hu) hu1
  have hz : zpowers u = U := by
    apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hu)
    rw [h148, Nat.card_zpowers, hu2]
  intro v hv
  rw [← hz, mem_zpowers_iff_mem_range_orderOf, hu2] at hv
  simp only [Finset.mem_image, Finset.mem_range] at hv
  obtain ⟨k, hk, rfl⟩ := hv
  interval_cases k <;> simp

theorem odd_card_K : Odd (Nat.card K) := by
  rw [F.K_card]
  have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : Even (2 ^ n) := (Nat.even_pow' (by have := F.three_le; omega)).mpr even_two
  obtain ⟨m, hm⟩ := h2
  exact ⟨m - 1, by omega⟩

theorem odd_orderOf_K {y : X} (hy : y ∈ K) : Odd (orderOf y) := by
  have h1 : orderOf y ∣ Nat.card K := by
    have := orderOf_dvd_natCard (⟨y, hy⟩ : ↥K)
    rwa [Subgroup.orderOf_mk] at this
  exact Odd.of_dvd_nat (odd_card_K F) h1

theorem not_dvd_two_pow_of_K {y : X} (hy : y ∈ K) (hyp : (orderOf y).Prime) (k : ℕ) :
    ¬ orderOf y ∣ 2 ^ k := by
  intro h
  have h2 := (Nat.prime_dvd_prime_iff_eq hyp Nat.prime_two).mp (hyp.dvd_of_dvd_pow h)
  have := odd_orderOf_K F hy
  rw [h2] at this
  exact (Nat.not_even_iff_odd.mpr this) even_two

theorem D_norm_K {d : X} (hd : d ∈ dGrp M t) : d ∈ normalizer (K : Set X) := by
  have key : ∀ d ∈ dGrp M t, ∀ x ∈ K, d * x * d⁻¹ ∈ K := by
    intro d hd x hx
    rw [F.K_eq] at hx ⊢
    obtain ⟨hxD, hxL⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hd hxD) (inv_mem hd),
      (mem_normalizer_iff.mp (F.D_norm_L hd) x).mp hxL⟩
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key d hd x, fun hx => ?_⟩
  have := key d⁻¹ (inv_mem hd) _ hx
  simpa [mul_assoc] using this

theorem hCy [Finite X] (h146 : Concl146 M t n K Mo U T S2) (h148 : Nat.card U = 2) {u : X}
    (hu : u ∈ U) (hu1 : u ≠ 1) :
    ∀ y ∈ K, (orderOf y).Prime → ∀ s ∈ S2, s * y * s⁻¹ * y⁻¹ ∈ Mo → s ∈ Mo ∨ s * u⁻¹ ∈ Mo := by
  intro y hyK hyp s hs hsy
  set A : Set X := (fun m => s * m) '' (Mo : Set X) with hA
  have hsC : s ∈ centralizer (Mo : Set X) := h146.S2_le_C0 hs
  set c := y * s * y⁻¹ * s⁻¹ with hcdef
  have hc : c ∈ Mo := by
    have : c = (s * y * s⁻¹ * y⁻¹)⁻¹ := by rw [hcdef]; group
    rw [this]
    exact inv_mem hsy
  have hcs : c * s = s * c := (mem_centralizer_iff.mp hsC) c hc
  have hinv : ∀ a ∈ A, y * a * y⁻¹ ∈ A := by
    rintro _ ⟨m, hm, rfl⟩
    refine ⟨c * (y * m * y⁻¹), mul_mem hc (Sec146.K_norm_Mo F y hyK m hm), ?_⟩
    calc s * (c * (y * m * y⁻¹)) = (c * s) * (y * m * y⁻¹) := by rw [hcs]; group
      _ = y * (s * m) * y⁻¹ := by rw [hcdef]; group
  have hyp1 : y ^ orderOf y = 1 := pow_orderOf_eq_one y
  have hxp : ∀ a ∈ A, y ^ orderOf y * a = a * y ^ orderOf y := by
    intro a _
    rw [hyp1, one_mul, mul_one]
  have hAcard : A.ncard = 2 ^ n := by
    rw [hA, Set.ncard_image_of_injective _ (mul_right_injective s), ← Nat.card_coe_set_eq]
    exact F.card_Mo
  obtain ⟨a, ⟨m, hm, rfl⟩, hya⟩ := exists_commute_of_pow_central (Set.toFinite A) hyp hinv hxp
    (orderOf_pos y) hyp1 (by rw [hAcard]; exact not_dvd_two_pow_of_K F hyK hyp n)
  have hy1 : y ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hyp; exact Nat.not_prime_one hyp
  have hmC : m ∈ centralizer (Mo : Set X) := by
    rw [mem_centralizer_iff]
    intro m' hm'
    exact Sec146.Mo_comm F m' hm' m hm
  have hsmJ : s * m ∈ J := by
    rw [← F.cent_K_C0 y hyK hy1]
    exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hya.symm, mul_mem hsC hmC⟩
  have hsmS : s * m ∈ S2 := mul_mem hs (F.T_le_S2 (Sec146.Mo_le_T F hm))
  have hsmT : s * m ∈ T := Sec146.S2_inf_NL F hsmS (Sec146.J_le_NL F hsmJ)
  have hsmU : s * m ∈ U := Sec146.T_inf_J F _ hsmT hsmJ
  rcases U_eq F h148 hu hu1 _ hsmU with h1 | h1
  · left
    have : s = m⁻¹ := by rw [← mul_eq_one_iff_eq_inv]; exact h1
    rw [this]
    exact inv_mem hm
  · right
    have hsm : s * m = m * s := ((mem_centralizer_iff.mp hsC) m hm).symm
    have : s * u⁻¹ = m⁻¹ := by
      calc s * u⁻¹ = s * (s * m)⁻¹ := by rw [h1]
        _ = s * (m * s)⁻¹ := by rw [hsm]
        _ = m⁻¹ := by group
    rw [this]
    exact inv_mem hm

theorem exists_mul_mem_D [Finite X] (h146 : Concl146 M t n K Mo U T S2) :
    ∀ y ∈ K, (orderOf y).Prime → ∀ g ∈ M, g ∈ normalizer (S2 : Set X) →
      g * y * g⁻¹ * y⁻¹ ∈ S2 → ∃ s ∈ S2, s * g ∈ dGrp M t := by
  intro y hyK hyp g hgM hgN hgy
  have hyN : y ∈ normalizer (S2 : Set X) := h146.K_norm_S2 hyK
  set A : Set X := (fun s => s * g) '' (S2 : Set X) with hA
  have hinv : ∀ a ∈ A, y * a * y⁻¹ ∈ A := by
    rintro _ ⟨s, hs, rfl⟩
    have h1 : y * s * y⁻¹ ∈ S2 := (mem_normalizer_iff.mp hyN s).mp hs
    have h2 : y * g * y⁻¹ * g⁻¹ ∈ S2 := by
      have : y * g * y⁻¹ * g⁻¹ = (g * y * g⁻¹ * y⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem hgy
    refine ⟨(y * s * y⁻¹) * (y * g * y⁻¹ * g⁻¹), mul_mem h1 h2, ?_⟩
    show (y * s * y⁻¹) * (y * g * y⁻¹ * g⁻¹) * g = y * (s * g) * y⁻¹
    group
  have hyp1 : y ^ orderOf y = 1 := pow_orderOf_eq_one y
  have hxp : ∀ a ∈ A, y ^ orderOf y * a = a * y ^ orderOf y := by
    intro a _
    rw [hyp1, one_mul, mul_one]
  have hAcard : A.ncard = Nat.card S2 := by
    rw [hA, Set.ncard_image_of_injective _ (mul_left_injective g), ← Nat.card_coe_set_eq]
    rfl
  obtain ⟨k, hk⟩ := F.S2_sylow.isPGroup.exists_card_eq
  obtain ⟨a, ⟨s, hs, rfl⟩, hya⟩ := exists_commute_of_pow_central (Set.toFinite A) hyp hinv hxp
    (orderOf_pos y) hyp1 (by rw [hAcard, hk]; exact not_dvd_two_pow_of_K F hyK hyp k)
  have hy1 : y ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hyp; exact Nat.not_prime_one hyp
  refine ⟨s, hs, F.cent_K_M y hyK hy1 (mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hya.symm,
    mul_mem (h146.S2_le_M hs) hgM⟩)⟩

theorem h14G [Finite X] (h146 : Concl146 M t n K Mo U T S2) :
    ∀ y ∈ K, (orderOf y).Prime → ∀ g ∈ M, g ∈ normalizer (S2 : Set X) →
      g * y * g⁻¹ * y⁻¹ ∈ S2 → ∃ s ∈ S2, s * g ∈ normalizer (K : Set X) := by
  intro y hyK hyp g hgM hgN hgy
  obtain ⟨s, hs, hsg⟩ := exists_mul_mem_D F h146 y hyK hyp g hgM hgN hgy
  exact ⟨s, hs, D_norm_K F hsg⟩

theorem hCK [Finite X] (h146 : Concl146 M t n K Mo U T S2) (h148 : Nat.card U = 2) :
    ∀ g ∈ M, g ∈ normalizer (S2 : Set X) → (∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ S2) →
      ∃ k ∈ K, ∃ s ∈ S2, g = k * s := by
  intro g hgM hgN hgK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨p, hp, hpK⟩ : ∃ p, p.Prime ∧ p ∣ Nat.card K := by
    refine Nat.exists_prime_and_dvd ?_
    rw [F.K_card]
    have : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) F.three_le
    omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) p hpK
  have hyp : (orderOf (y : X)).Prime := by rw [Subgroup.orderOf_coe, hy]; exact hp
  obtain ⟨s₁, hs₁, hdD⟩ := exists_mul_mem_D F h146 y y.2 hyp g hgM hgN (hgK y y.2)
  set d := s₁ * g with hd
  have hdN : d ∈ normalizer (S2 : Set X) := mul_mem (le_normalizer hs₁) hgN
  have hdK : ∀ k ∈ K, d * k = k * d := by
    intro k hk
    have hkN := h146.K_norm_S2 hk
    have h1 : d * k * d⁻¹ * k⁻¹ ∈ S2 := by
      have e : d * k * d⁻¹ * k⁻¹ = s₁ * (g * k * g⁻¹ * k⁻¹) * (k * s₁⁻¹ * k⁻¹) := by
        rw [hd]; group
      rw [e]
      exact mul_mem (mul_mem hs₁ (hgK k hk)) ((mem_normalizer_iff.mp hkN _).mp (inv_mem hs₁))
    have h2 : d * k * d⁻¹ * k⁻¹ ∈ K :=
      mul_mem ((mem_normalizer_iff.mp (D_norm_K F hdD) k).mp hk) (inv_mem hk)
    have h3 := Bender.eq_one_of_isPGroup_two_of_odd F.S2_sylow.isPGroup (odd_card_K F) h1 h2
    calc d * k = d * k * d⁻¹ * k⁻¹ * k * d := by group
      _ = k * d := by rw [h3, one_mul]
  obtain ⟨k₀, hk₀, j, hj, hdkj⟩ := F.cent_D_K d hdD hdK
  have hjN : j ∈ normalizer (S2 : Set X) := by
    have : j = k₀⁻¹ * d := by rw [hdkj]; group
    rw [this]
    exact mul_mem (inv_mem (h146.K_norm_S2 hk₀)) hdN
  obtain ⟨u, hu, hu1⟩ : ∃ u ∈ U, u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact F.U_ne_bot (eq_bot_iff.mpr fun x hx => mem_bot.mpr (hcon x hx))
  have hjL : j ∈ normalizer (L : Set X) := Sec146.J_le_NL F hj
  have hju : j * u * j⁻¹ ∈ U := by
    have h1 : j * u * j⁻¹ ∈ S2 :=
      (mem_normalizer_iff.mp hjN u).mp (F.T_le_S2 (Sec146.U_le_T F hu))
    have h2 : j * u * j⁻¹ ∈ normalizer (L : Set X) :=
      mul_mem (mul_mem hjL (Sec146.J_le_NL F (F.U_le_J hu))) (inv_mem hjL)
    have h3 : j * u * j⁻¹ ∈ J := mul_mem (mul_mem hj (F.U_le_J hu)) (inv_mem hj)
    exact Sec146.T_inf_J F _ (Sec146.S2_inf_NL F h1 h2) h3
  have hju1 : j * u * j⁻¹ ≠ 1 := by
    intro h1
    apply hu1
    have := congrArg (fun w => j⁻¹ * w * j) h1
    simpa [mul_assoc] using this
  have hjuu : j * u * j⁻¹ = u := (U_eq F h148 hu hu1 _ hju).resolve_left hju1
  have hjU : j ∈ U := by
    rw [← F.cent_U_J u hu hu1]
    refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, hj⟩
    calc j * u = j * u * j⁻¹ * j := by group
      _ = u * j := by rw [hjuu]
  have hjS : j ∈ S2 := F.T_le_S2 (Sec146.U_le_T F hjU)
  refine ⟨k₀, hk₀, k₀⁻¹ * s₁⁻¹ * k₀ * j, mul_mem ?_ hjS, ?_⟩
  · have := (mem_normalizer_iff.mp (h146.K_norm_S2 (inv_mem hk₀)) s₁⁻¹).mp (inv_mem hs₁)
    simpa using this
  · calc g = s₁⁻¹ * d := by rw [hd]; group
      _ = s₁⁻¹ * (k₀ * j) := by rw [hdkj]
      _ = k₀ * (k₀⁻¹ * s₁⁻¹ * k₀ * j) := by group

theorem h3 (h148 : Nat.card U = 2) :
    n = 3 → ∀ p a : ℕ, p.Prime → p ≠ 2 → 0 < a → p ^ a ∣ Nat.card M → p ^ a % 7 ≠ 1 := by
  intro hn3 p a hp hp2 ha hdvd
  have hJ7 : 7 ∣ Nat.card J := by
    have h1 : ¬ Nat.Coprime (Nat.card J) 7 := by
      have := F.coprime_J
      rwa [hn3] at this
    by_contra h7
    exact h1 ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h7)))
  have hJ14 : Nat.card J = 14 := F.card_J_14 hn3 hJ7 h148
  obtain ⟨d, hd, hdn, hdodd⟩ := F.card_D
  rw [hn3] at hdn
  have hM : Nat.card M = 2 ^ 10 * (3 * 7 ^ 2 * 19) * d := by
    rw [F.card_M, hd, hJ14, hn3]
    have e1 : (2 : ℕ) ^ (3 * 3) * (2 ^ (2 * 3) - 2 ^ 3 + 1) * ((2 ^ 3 - 1) * 14) =
        2 ^ 10 * (3 * 7 ^ 2 * 19) := by norm_num
    calc 2 ^ (3 * 3) * (2 ^ (2 * 3) - 2 ^ 3 + 1) * ((2 ^ 3 - 1) * 14 * d)
        = (2 ^ (3 * 3) * (2 ^ (2 * 3) - 2 ^ 3 + 1) * ((2 ^ 3 - 1) * 14)) * d := by ring
      _ = 2 ^ 10 * (3 * 7 ^ 2 * 19) * d := by rw [e1]
  have hM' : Nat.card M ∣ 2 ^ 10 * (3 ^ 2 * 7 ^ 2 * 19) := by
    rw [hM]
    rcases (Nat.dvd_prime Nat.prime_three).mp hdn with rfl | rfl <;> norm_num
  have hcop2 : Nat.Coprime (p ^ a) (2 ^ 10) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have h1 : p ^ a ∣ 3 ^ 2 * 7 ^ 2 * 19 := hcop2.dvd_of_dvd_mul_left (hdvd.trans hM')
  have hp' : p ∣ 3 ^ 2 * 7 ^ 2 * 19 := (dvd_pow_self p ha.ne').trans h1
  rcases (Nat.Prime.dvd_mul hp).mp hp' with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
    · have hp3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h')
      subst hp3
      have h2 : 3 ^ a ∣ 3 ^ 2 := by
        rw [mul_assoc] at h1
        have hc : Nat.Coprime (3 ^ a) (7 ^ 2 * 19) := Nat.Coprime.pow_left a (by norm_num)
        exact hc.dvd_of_dvd_mul_right h1
      have ha2 : a ≤ 2 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2
      interval_cases a <;> norm_num
    · have hp7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp
        (hp.dvd_of_dvd_pow h')
      subst hp7
      rw [Nat.pow_mod]
      simp [Nat.zero_pow ha]
  · have hp19 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 19)).mp h
    subst hp19
    have h2 : 19 ^ a ∣ 19 ^ 1 := by
      rw [pow_one]
      have hc : Nat.Coprime (19 ^ a) (3 ^ 2 * 7 ^ 2) := Nat.Coprime.pow_left a (by norm_num)
      exact hc.dvd_of_dvd_mul_left h1
    have ha1 : a ≤ 1 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2
    interval_cases a
    norm_num

theorem hfaith [Finite X] (h146 : Concl146 M t n K Mo U T S2) :
    ∀ g ∈ M, g ∈ normalizer (S2 : Set X) → (∀ s ∈ S2, g * s * g⁻¹ * s⁻¹ ∈ Mo) → g ∈ S2 := by
  intro g hgM hgN hgS
  obtain ⟨a, ha⟩ := exists_odd_part g
  have hpow : ∀ k : ℕ, ∀ s ∈ S2, g ^ k * s * (g ^ k)⁻¹ * s⁻¹ ∈ Mo := by
    intro k
    induction k with
    | zero => intro s _; simp
    | succ k ih =>
      intro s hs
      set c := g ^ k * s * (g ^ k)⁻¹ * s⁻¹ with hc
      have hcMo := ih s hs
      have e : g ^ (k + 1) * s * (g ^ (k + 1))⁻¹ * s⁻¹ =
          (g * c * g⁻¹) * (g * s * g⁻¹ * s⁻¹) := by rw [hc, pow_succ']; group
      rw [e]
      exact mul_mem (F.Mo_normal g hgM c hcMo) (hgS s hs)
  have h1 := odd_centralizes_T F ha fun x hx => hpow (2 ^ a) x (F.T_le_S2 hx)
  have hg2 : IsPGroup 2 (zpowers g) := by
    rintro ⟨y, hy⟩
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    refine ⟨a, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h1, one_zpow]
  have hW : IsPGroup 2 ↥(zpowers g ⊔ S2) :=
    IsPGroup.to_sup_of_normal_right' hg2 F.S2_sylow.isPGroup (zpowers_le.mpr hgN)
  have heq := (S2_sylow_M F h146).eq_of_le le_sup_right
    (sup_le (zpowers_le.mpr hgM) h146.S2_le_M) hW
  rw [← heq]
  exact mem_sup_left (mem_zpowers g)

theorem card_T [Finite X] : Nat.card T = 2 ^ (2 * n) * Nat.card U := by
  rw [F.T_eq, Bender.card_sup_eq_mul_of_le_normalizer (Sec146.U_le_normalizer_P F)
    (Sec146.P_inf_U F), F.card_P]

theorem lemma149 [Finite X] (h146 : Concl146 M t n K Mo U T S2)
    (h147 : Concl147 n K J Mo U T S2) (h148 : Nat.card U = 2) (hW : Weak149Stmt) :
    ∀ u ∈ U, ∀ g ∈ M, g * u * g⁻¹ ∈ S2 → g * u * g⁻¹ * u⁻¹ ∈ Mo := by
  intro u hu g hgM hgu
  by_cases hu1 : u = 1
  · rw [hu1]
    simp
  have huMo : u ∉ Mo := by
    intro h
    have : u ∈ Mo ⊓ U := mem_inf.mpr ⟨h, hu⟩
    rw [Sec146.Mo_inf_U F, mem_bot] at this
    exact hu1 this
  by_cases hinv : ∃ a ∈ S2, a ∉ T ∧ a * a = 1
  · have hel := h147.elem hinv
    have hcard : Nat.card S2 = 2 ^ (2 * n + 1) * Nat.card Mo := by
      rw [h146.card_S2, card_T F, h148, F.card_Mo]
      ring
    exact hW M Mo S2 K u n F.Mo_le_M F.Mo_normal ((Sec146.Mo_le_T F).trans F.T_le_S2)
      (S2_sylow_M F h146) hel F.three_le hcard (F.T_le_S2 (Sec146.U_le_T F hu)) huMo
      (Sec146.K_le_M F) h146.K_norm_S2 F.K_card (fun k hk => Sec146.K_comm_U F k hk u hu)
      (hfaith F h146) (hCy F h146 h148 hu hu1) (h14G F h146) (hCK F h146 h148) (h3 F h148)
      g hgM hgu
  · push Not at hinv
    have hu2 : u * u = 1 := F.U_sq u hu
    have hv2 : (g * u * g⁻¹) * (g * u * g⁻¹) = 1 := by
      calc (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
        _ = 1 := by rw [hu2]; group
    have hvT : g * u * g⁻¹ ∈ T := by
      by_contra h
      exact hinv _ hgu h hv2
    obtain ⟨p, hp, u', hu', hpu⟩ := (Sec146.mem_T_iff F).mp hvT
    have hp2 : p * p = 1 := by
      have h1 : u' * p = p * u' := (Sec146.comm_P_U F p hp u' hu').symm
      rw [hpu] at hv2
      have : (p * p) * (u' * u') = 1 := by
        calc (p * p) * (u' * u') = p * (p * u') * u' := by group
          _ = p * (u' * p) * u' := by rw [h1]
          _ = 1 := by rw [← hv2]; group
      rw [F.U_sq u' hu', mul_one] at this
      exact this
    have hpMo : p ∈ Mo := by
      by_contra h
      exact F.P_sq_ne p hp h hp2
    have hu'1 : u' ≠ 1 := by
      intro h
      rw [h, mul_one] at hpu
      apply huMo
      have hv : g * u * g⁻¹ ∈ Mo := by rw [hpu]; exact hpMo
      have := F.Mo_normal g⁻¹ (M.inv_mem hgM) _ hv
      simpa [mul_assoc] using this
    have hu'u : u' = u := (U_eq F h148 hu hu1 u' hu').resolve_left hu'1
    rw [hpu, hu'u, mul_inv_cancel_right]
    exact hpMo

end Sec149

theorem lemma149 {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X} {t : X} {n r : ℕ}
    {L K J Mo P U T S2 : Subgroup X} (F : Facts14 Z M t n r L K J Mo P U T S2)
    (h146 : Concl146 M t n K Mo U T S2) (h147 : Concl147 n K J Mo U T S2)
    (h148 : Nat.card U = 2) (hW : Weak149Stmt) :
    ∀ u ∈ U, ∀ g ∈ M, g * u * g⁻¹ ∈ S2 → g * u * g⁻¹ * u⁻¹ ∈ Mo :=
  Sec149.lemma149 F h146 h147 h148 hW

end CFSG.GH74.Uniqueness
