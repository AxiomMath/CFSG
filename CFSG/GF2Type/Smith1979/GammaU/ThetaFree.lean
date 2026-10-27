module

public import CFSG.GF2Type.Smith1979.GammaU.FpfThree
public import Certificates.Certificate16973
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GF2Type.Smith1979.GammaU.SigmaP

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum Subgroup

variable {i : ℕ}

theorem sylow_facts (hi : i = 0 ∨ i = 1) : SylowFacts i :=
  Certificates.certificate16973 i hi

section

variable (hi : i = 0 ∨ i = 1)
include hi

theorem thetaU_mem_p2 : thetaU ∈ p2 i := by
  obtain ⟨U, hU, hUx⟩ := theta0_mem_p2 hi
  have : U = thetaU := LinearEquiv.ext hUx
  exact this ▸ hU

theorem theta_comm : ∀ u ∈ p2 i, u * thetaU = thetaU * u := fun u hu =>
  LinearEquiv.ext fun v => by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, thetaU_apply, thetaU_apply,
      (sylow_facts hi).theta_comm u hu v]

end

theorem factorization_17280_three : (17280 : ℕ).factorization 3 = 3 := by
  rw [show (17280 : ℕ) = 3 ^ 3 * 640 by norm_num, Nat.factorization_mul (by norm_num)
    (by norm_num), Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three,
    Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem factorization_five_eq_one {n m : ℕ} (h : n = 5 * m) (hm : ¬ 5 ∣ m) :
    n.factorization 5 = 1 := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 5)
  rw [h, show 5 * m = 5 ^ 1 * m by ring, Nat.factorization_mul (by norm_num) hm0,
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_five, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm]

section

variable (hi : i = 0 ∨ i = 1)
include hi

theorem exists_noncomm_sylow3 :
    ∃ T : Sylow 3 (p2 i), ∃ a ∈ (T : Subgroup (p2 i)), ∃ b ∈ (T : Subgroup (p2 i)),
      a * b ≠ b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, hle, hT27, a, ha, b, hb, hab⟩ := (sylow_facts hi).exists_noncomm_27
  replace hle : T ≤ p2 i := hle
  set T0 : Subgroup (p2 i) := T.subgroupOf (p2 i)
  have hT0 : Nat.card T0 = 3 ^ (Nat.card (p2 i)).factorization 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, hT27, card_p2 hi,
      factorization_17280_three]
    norm_num
  refine ⟨Sylow.ofCard T0 hT0, ⟨a, hle ha⟩, ?_, ⟨b, hle hb⟩, ?_, fun h => hab ?_⟩
  · rw [Sylow.coe_ofCard, mem_subgroupOf]
    exact ha
  · rw [Sylow.coe_ofCard, mem_subgroupOf]
    exact hb
  · exact congrArg Subtype.val h

theorem not_nine_dvd (S : Subgroup (p2 i)) {θ' : p2 i} (hθ' : (θ' : V12 ≃ₗ[ZMod 2] V12) = thetaU)
    (hθS : θ' ∉ S) : ¬ 9 ∣ Nat.card S := by
  intro h9
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : Nat.card (p2 i) = 17280 := card_p2 hi
  have hcent : ∀ x : p2 i, x * θ' = θ' * x := fun x =>
    Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hθ']; exact theta_comm hi x x.2)
  obtain ⟨T, hT⟩ := Sylow.exists_subgroup_card_pow_prime (G := S) 3 (n := 2) (by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num]
    exact h9)
  set T' : Subgroup (p2 i) := T.map S.subtype with hT'def
  have hT' : Nat.card T' = 9 := by
    rw [hT'def, Subgroup.card_map_of_injective S.subtype_injective, hT]
    norm_num
  have hTS : T' ≤ S := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hθT : θ' ∉ T' := fun h => hθS (hTS h)
  have hcommT : ∀ a ∈ T', ∀ b ∈ T', a * b = b * a := by
    intro a ha b hb
    have := IsPGroup.commutative_of_card_eq_prime_sq (p := 3) (G := T') (by rw [hT']; norm_num)
      ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hTp : IsPGroup 3 T' := IsPGroup.of_card (n := 2) (by rw [hT']; norm_num)
  obtain ⟨T3, hT3⟩ := hTp.exists_le_sylow
  have hθ3 : θ' ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hθ', Subgroup.coe_one]
    exact thetaU_pow_three)
  have hθ1 : θ' ≠ 1 := fun h => hθS (h ▸ S.one_mem)
  have hθord : orderOf θ' = 3 := orderOf_eq_prime hθ3 hθ1
  have hZnorm : (zpowers θ').Normal := ⟨fun n hn g => by
    have hc : g * n * g⁻¹ = n := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
      have hck : ∀ k : ℤ, g * θ' ^ k = θ' ^ k * g := fun k =>
        (Commute.zpow_right (show Commute g θ' from hcent g) k).eq
      rw [hck k, mul_inv_cancel_right]
    rw [hc]
    exact hn⟩
  have hZp : IsPGroup 3 (zpowers θ') := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hθord, pow_one])
  haveI := hZnorm
  have hθT3 : θ' ∈ (T3 : Subgroup (p2 i)) := hZp.le_sylow_of_normal T3 (mem_zpowers θ')
  set A : Subgroup (p2 i) := T' ⊔ zpowers θ' with hA
  have hAT3 : A ≤ T3 := sup_le hT3 (zpowers_le.2 hθT3)
  have hZc : ∀ K : Subgroup (p2 i), zpowers θ' ≤ centralizer (K : Set (p2 i)) := fun K =>
    zpowers_le.2 (mem_centralizer_iff.2 fun h _ => hcent h)
  have hAc : A ≤ centralizer (A : Set (p2 i)) := by
    refine sup_le ?_ (hZc A)
    rw [le_centralizer_iff]
    refine sup_le ?_ (hZc T')
    intro b hb
    rw [mem_centralizer_iff]
    intro a ha
    exact hcommT a ha b hb
  have hcard3 : Nat.card (T3 : Subgroup (p2 i)) = 27 := by
    rw [Sylow.card_eq_multiplicity T3, hP, factorization_17280_three]
    norm_num
  have hAcard : Nat.card A = 27 := by
    have hlt : T' < A := lt_of_le_of_ne le_sup_left fun h =>
      hθT (h ▸ mem_sup_right (mem_zpowers θ'))
    have h1 := Subgroup.card_lt_of_lt hlt
    have h2 := Subgroup.card_dvd_of_le hAT3
    rw [hT'] at h1
    rw [hcard3] at h2
    have h3 := Nat.le_of_dvd (by norm_num) h2
    generalize Nat.card A = k at h1 h2 h3 ⊢
    interval_cases k <;> omega
  have hAS : Nat.card A = 3 ^ (Nat.card (p2 i)).factorization 3 := by
    rw [hAcard, hP, factorization_17280_three]
    norm_num
  obtain ⟨T0, a, ha, b, hb, hab⟩ := exists_noncomm_sylow3 hi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (p2 i) (Sylow.ofCard A hAS) T0
  have hconj : ∀ x ∈ (T0 : Subgroup (p2 i)), ∃ y ∈ A, g * y * g⁻¹ = x := by
    intro x hx
    rw [← hg] at hx
    have hx' : x ∈ ((g • Sylow.ofCard A hAS : Sylow 3 (p2 i)) : Set (p2 i)) := hx
    rw [Sylow.coe_smul, Set.mem_smul_set] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    exact ⟨y, hy, by simpa [MulAut.smul_def, MulAut.conj_apply] using hyx⟩
  obtain ⟨a', ha', rfl⟩ := hconj a ha
  obtain ⟨b', hb', rfl⟩ := hconj b hb
  apply hab
  have := (mem_centralizer_iff.1 (hAc hb')) a' ha'
  calc g * a' * g⁻¹ * (g * b' * g⁻¹) = g * (a' * b') * g⁻¹ := by group
    _ = g * (b' * a') * g⁻¹ := by rw [this]
    _ = g * b' * g⁻¹ * (g * a' * g⁻¹) := by group

theorem card_normalizer_five_dvd (F : Subgroup (p2 i)) (hF : Nat.card F = 5) :
    Nat.card (normalizer (F : Set (p2 i))) ∣ 30 :=
  (sylow_facts hi).card_normalizer_five_dvd F hF

theorem index_ne (S : Subgroup (p2 i)) : S.index ≠ 9 ∧ S.index ≠ 27 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hP : Nat.card (p2 i) = 17280 := card_p2 hi
  have hmul : Nat.card S * S.index = 17280 := by rw [card_mul_index, hP]
  suffices h : ∀ m q, S.index = m → Nat.card S = 5 * q → ¬ 5 ∣ q → (m = 9 ∨ m = 27) → False by
    refine ⟨fun h9 => h 9 384 h9 ?_ (by norm_num) (Or.inl rfl),
      fun h27 => h 27 128 h27 ?_ (by norm_num) (Or.inr rfl)⟩
    · rw [h9] at hmul
      omega
    · rw [h27] at hmul
      omega
  intro m q hm hS hq hm'
  obtain ⟨F⟩ : Nonempty (Sylow 5 S) := inferInstance
  have hF : Nat.card (F : Subgroup S) = 5 := by
    rw [Sylow.card_eq_multiplicity, factorization_five_eq_one hS hq, pow_one]
  set F' : Subgroup (p2 i) := (F : Subgroup S).map S.subtype with hF'def
  have hF' : Nat.card F' = 5 := by
    rw [hF'def, Subgroup.card_map_of_injective S.subtype_injective, hF]
  set NS := normalizer ((F : Subgroup S) : Set S) with hNS
  have h30 : Nat.card NS ∣ 30 := by
    have h1 : NS.map S.subtype ≤ normalizer (F' : Set (p2 i)) := le_normalizer_map S.subtype
    have h2 := Subgroup.card_dvd_of_le h1
    rw [Subgroup.card_map_of_injective S.subtype_injective] at h2
    exact h2.trans (card_normalizer_five_dvd hi F' hF')
  have h5 : 5 ∣ Nat.card NS := by
    have := Subgroup.card_dvd_of_le (Subgroup.le_normalizer (H := (F : Subgroup S)))
    rwa [hF] at this
  have hmod := card_sylow_modEq_one 5 S
  rw [Sylow.card_eq_index_normalizer F] at hmod
  have hmulS := card_mul_index NS
  rw [hS] at hmulS
  have hle := Nat.le_of_dvd (by norm_num) h30
  have hmod' : NS.index % 5 = 1 := hmod
  have hq' : q = 384 ∨ q = 128 := by
    rcases hm' with rfl | rfl
    · rw [hm] at hmul
      omega
    · rw [hm] at hmul
      omega
  generalize Nat.card NS = k at h30 h5 hmulS hle ⊢
  interval_cases k <;> omega

theorem theta_free_index (S : Subgroup (p2 i))
    (hS : ∀ x ∈ S, (x : V12 ≃ₗ[ZMod 2] V12) ≠ thetaU) :
    9 ∣ S.index ∧ S.index ≠ 9 ∧ S.index ≠ 27 := by
  have hP : Nat.card (p2 i) = 17280 := card_p2 hi
  have hmul : Nat.card S * S.index = 17280 := by rw [card_mul_index, hP]
  have h9 := not_nine_dvd hi S (θ' := ⟨thetaU, thetaU_mem_p2 hi⟩) rfl fun h => hS _ h rfl
  refine ⟨?_, index_ne hi S⟩
  by_contra hm
  apply h9
  by_cases h3 : 3 ∣ S.index
  · obtain ⟨m', hm'⟩ := h3
    have hm3 : ¬ 3 ∣ m' := fun ⟨k, hk⟩ => hm ⟨k, by rw [hm', hk]; ring⟩
    have hco : Nat.Coprime (3 ^ 2) m' :=
      Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm3)
    rw [hm'] at hmul
    have hS' : Nat.card S * m' = 5760 := by
      have : 3 * (Nat.card S * m') = 3 * 5760 := by
        rw [show 3 * (Nat.card S * m') = Nat.card S * (3 * m') by ring, hmul]
      omega
    have : 3 ^ 2 ∣ Nat.card S * m' := ⟨640, by rw [hS']; norm_num⟩
    have h' := hco.dvd_of_dvd_mul_right this
    norm_num at h'
    exact h'
  · have hco : Nat.Coprime (3 ^ 3) S.index :=
      Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)
    have : 3 ^ 3 ∣ Nat.card S * S.index := ⟨640, by rw [hmul]; norm_num⟩
    exact dvd_trans (by norm_num : (9 : ℕ) ∣ 3 ^ 3) (hco.dvd_of_dvd_mul_right this)

theorem theta_free_index_le (S : Subgroup (p2 i))
    (hS : ∀ x ∈ S, (x : V12 ≃ₗ[ZMod 2] V12) ≠ thetaU) (h45 : S.index ≤ 45) :
    S.index = 18 ∨ S.index = 36 ∨ S.index = 45 := by
  obtain ⟨⟨k, hk⟩, h9, h27⟩ := theta_free_index hi S hS
  have h0 : S.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hk5 : k ≤ 5 := by omega
  interval_cases k <;> omega

end

end CFSG.GF2Type.Smith1979.GammaU.SigmaP
