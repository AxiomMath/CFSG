module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4Cent
public import CFSG.LieType.Chevalley.RootLocalComponentFree
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.D4

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement Matrix

section Field

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {m : ℕ}

theorem charP_two_of_card_d4 (hK : Nat.card K = (2 ^ m) ^ 3) : CharP K 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (f := m * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])

theorem sigma_cube_of_card_d4 (hK : Nat.card K = (2 ^ m) ^ 3) (hσq : ∀ c, σ c = c ^ 2 ^ m) :
    ∀ c, σ (σ (σ c)) = c := fun c => by
  have := Fintype.ofFinite K
  rw [hσq, hσq, hσq, ← pow_mul, ← pow_mul, show 2 ^ m * (2 ^ m * 2 ^ m) = (2 ^ m) ^ 3 by ring,
    ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]

omit [Finite K] in
theorem card_d4k_of_card
    (hm : 1 ≤ m) (hK : Nat.card K = (2 ^ m) ^ 3)
    (hσq : ∀ c, σ c = c ^ 2 ^ m) : Nat.card (d4k K σ) = 2 ^ m := by
  have h := card_orbitField_D4_orientation (ℓ := 2) (f := m) Nat.prime_two hm hK (r := 1)
    (Or.inl rfl) (σ := σ.toRingHom) (fun c => by simpa using hσq c) ⟨1, by decide⟩
  have he : orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ =
      trialityFixedField K σ.toRingHom := by
    ext c
    rw [mem_orbitField, show (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 by decide, pow_one,
      mem_trialityFixedField]
  rw [he, show (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 by decide, pow_one] at h
  exact h

omit [Finite K] in
theorem exists_not_fixed_d4
    (hm : 1 ≤ m) (hK : Nat.card K = (2 ^ m) ^ 3)
    (hσq : ∀ c, σ c = c ^ 2 ^ m) : ∃ x : K, σ x ≠ x := by
  by_contra h
  push Not at h
  have hk := card_d4k_of_card σ hm hK hσq
  have htop : d4k K σ = ⊤ := eq_top_iff.2 fun x _ => h x
  rw [htop] at hk
  have h1 : Nat.card (⊤ : Subfield K) = Nat.card K := Nat.card_congr Subfield.topEquiv.toEquiv
  rw [h1, hK] at hk
  have h2 : 2 ^ m < (2 ^ m) ^ 3 := by
    have h4 : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    calc 2 ^ m = (2 ^ m) ^ 1 := by ring
      _ < (2 ^ m) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

end Field

section Cross

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem cross_eq_one_of_Q {s : K} (hs : s + σ s + σ (σ s) = 0)
    (hQ : s * s + s * σ s + σ s * σ s ≠ 0) :
    ∃ s' : K, s' + σ s' + σ (σ s') = 0 ∧ σ s * σ (σ s') + σ (σ s) * σ s' = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hss : σ (σ s) = s + σ s := by linear_combination hs - (s + σ s) * h2
  have hσQ : σ (s * s + s * σ s + σ s * σ s) = s * s + s * σ s + σ s * σ s := by
    rw [map_add, map_add, map_mul, map_mul, map_mul, hss]
    linear_combination (σ s * σ s + s * σ s) * h2
  have hQinv := inv_mul_cancel₀ hQ
  refine ⟨(s * s + s * σ s + σ s * σ s)⁻¹ * σ s, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv₀, map_inv₀, hσQ, hσQ, hσ]
    linear_combination (s * s + s * σ s + σ s * σ s)⁻¹ * hs
  · rw [map_mul, map_mul, map_inv₀, map_inv₀, hσQ, hσQ, hσ, hss]
    linear_combination hQinv + ((s * s + s * σ s + σ s * σ s)⁻¹ * s * σ s) * h2

include hσ in
theorem exists_cross_eq_one_d4 {x : K} (hx : σ x ≠ x) :
    ∃ s s' : K, s + σ s + σ (σ s) = 0 ∧ s' + σ s' + σ (σ s') = 0 ∧
      σ s * σ (σ s') + σ (σ s) * σ s' = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hT : ∀ y : K, (y + σ y) + σ (y + σ y) + σ (σ (y + σ y)) = 0 := fun y => by
    simp only [map_add, hσ]
    linear_combination (y + σ y + σ (σ y)) * h2
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : K, s₀ = x + σ x := ⟨_, rfl⟩
  have hs₀0 : s₀ ≠ 0 := fun h => hx (by linear_combination h - hs₀ - x * h2)
  have hσs₀ : σ s₀ ≠ 0 := (map_ne_zero σ).2 hs₀0
  have hd : s₀ + σ s₀ ≠ 0 := by
    intro h
    rw [hs₀, map_add] at h
    have h' : σ (σ x) = x := by linear_combination h - (x + σ x) * h2
    apply hx
    calc σ x = σ (σ (σ x)) := by rw [h']
      _ = x := hσ x
  have hsq : s₀ * s₀ = (x * x) + σ (x * x) := by
    rw [hs₀, map_mul]
    linear_combination (x * σ x) * h2
  have hsum : s₀ + s₀ * s₀ = (x + x * x) + σ (x + x * x) := by
    rw [hsq, map_add, hs₀]
    ring
  have hT₀ : s₀ + σ s₀ + σ (σ s₀) = 0 := hs₀ ▸ hT x
  have hT₁ : s₀ * s₀ + σ (s₀ * s₀) + σ (σ (s₀ * s₀)) = 0 := hsq ▸ hT (x * x)
  have hT₂ : (s₀ + s₀ * s₀) + σ (s₀ + s₀ * s₀) + σ (σ (s₀ + s₀ * s₀)) = 0 :=
    hsum ▸ hT (x + x * x)
  by_cases h1 : s₀ * s₀ + s₀ * σ s₀ + σ s₀ * σ s₀ = 0
  · by_cases h3 : s₀ * s₀ * (s₀ * s₀) + s₀ * s₀ * σ (s₀ * s₀) + σ (s₀ * s₀) * σ (s₀ * s₀) = 0
    · have hQs : (s₀ + s₀ * s₀) * (s₀ + s₀ * s₀) + (s₀ + s₀ * s₀) * σ (s₀ + s₀ * s₀) +
          σ (s₀ + s₀ * s₀) * σ (s₀ + s₀ * s₀) ≠ 0 := by
        have e : (s₀ + s₀ * s₀) * (s₀ + s₀ * s₀) + (s₀ + s₀ * s₀) * σ (s₀ + s₀ * s₀) +
            σ (s₀ + s₀ * s₀) * σ (s₀ + s₀ * s₀) = s₀ * σ s₀ * (s₀ + σ s₀) := by
          have h3' := h3
          simp only [map_mul] at h3'
          simp only [map_add, map_mul]
          linear_combination h1 + h3' + (s₀ * s₀ * s₀ + σ s₀ * σ s₀ * σ s₀) * h2
        rw [e]
        exact mul_ne_zero (mul_ne_zero hs₀0 hσs₀) hd
      obtain ⟨s', hs', h⟩ := cross_eq_one_of_Q σ hσ hT₂ hQs
      exact ⟨_, s', hT₂, hs', h⟩
    · obtain ⟨s', hs', h⟩ := cross_eq_one_of_Q σ hσ hT₁ h3
      exact ⟨_, s', hT₁, hs', h⟩
  · obtain ⟨s', hs', h⟩ := cross_eq_one_of_Q σ hσ hT₀ h1
    exact ⟨_, s', hT₀, hs', h⟩

end Cross

section ResZ

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem charTwo_d4
    {x : ↥(d4C K σ)} (hx2 : x * x = 1) (hx1 : x ≠ 1) : Exc.CharTwo x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf x = 2 := orderOf_eq_prime (by rw [sq, hx2]) hx1
  have hQp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hord, pow_one])
  have h := (RootWeightDatum.defining_characteristic_root_local_groups_component_free
    (D := RootWeightDatum.fixed TwistTag.D4 σ (ringEquiv_cube_d4 σ hσ)) 2 (zpowers x) hQp
    (zpowers_ne_bot.2 hx1) (centralizer (zpowers x : Set ↥(d4C K σ))) (Or.inr rfl)).1
  have he : centralizer (zpowers x : Set ↥(d4C K σ)) = Exc.cent x := by
    rw [Exc.cent, zpowers_eq_closure, centralizer_closure]
  unfold Exc.CharTwo
  rw [← he]
  exact h

omit [Finite K] [CharP K 2] in
theorem coe_commutatorElement_d4C
    (a b : ↥(d4C K σ)) :
    ((⁅a, b⁆ : ↥(d4C K σ)) : ModGL TwistTag.D4.tag K) =
      ⁅(a : ModGL TwistTag.D4.tag K), (b : ModGL TwistTag.D4.tag K)⁆ := by
  simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]

omit [Finite K] in
theorem exists_ne_norm_d4 {x : K} (hx : σ x ≠ x) :
    ∃ a : K, a ≠ 0 ∧ a ≠ σ a * σ (σ a) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  by_cases h : x = σ x * σ (σ x)
  · refine ⟨x + 1, fun h0 => hx ?_, fun h1 => hx ?_⟩
    · have hx1 : x = 1 := by linear_combination h0 - h2
      rw [hx1, map_one]
    · rw [map_add, map_add, map_one, map_one] at h1
      have h3 : σ x = σ (σ x) := by linear_combination h - h1 - σ (σ x) * h2
      exact (σ.injective h3).symm
  · exact ⟨x, fun h0 => hx (by rw [h0, map_zero]), h⟩

include hσ in
theorem trialityOuterTorus_mem_d4C
    (a : Kˣ) : trialityOuterTorus K σ a ∈ d4C K σ := by
  obtain ⟨-, ⟨e, he⟩, -⟩ :=
    even_triality_faithful_torus_coordinates K σ (ringEquiv_cube_d4 σ hσ)
  have h1 := (e (a, 1)).2
  rw [he, trialityMiddleTorus, map_one, torusElt_one, mul_one] at h1
  exact (mem_inf.1 h1).2

include hσ in
theorem residualMem_z
    {x : K} (hx : σ x ≠ x) {z : ↥(d4C K σ)}
    (hz : (z : ModGL TwistTag.D4.tag K) = d4z K) : Exc.ResidualMem z := by
  have hσ3 := toRingHom_pow_three_d4 σ hσ
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨a, ha0, ha⟩ := exists_ne_norm_d4 σ hx
  have hσa : σ a ≠ 0 := (map_ne_zero σ).2 ha0
  have hσσa : σ (σ a) ≠ 0 := (map_ne_zero σ).2 hσa
  have hN : a * σ a * σ (σ a) ≠ 0 := mul_ne_zero (mul_ne_zero ha0 hσa) hσσa
  set A : Kˣ := Units.mk0 a ha0 with hA
  have hAv : (A : K) = a := rfl
  set h : ↥(d4C K σ) := ⟨trialityOuterTorus K σ A, trialityOuterTorus_mem_d4C σ hσ A⟩ with hh
  set κ₃ : K := a ^ 2 * (a * σ a * σ (σ a))⁻¹ with hκ₃
  set κ₄ : K := σ a ^ 2 * σ (σ a) ^ 2 * (a * σ a * σ (σ a))⁻¹ with hκ₄
  have hκ₃1 : κ₃ + 1 ≠ 0 := by
    intro h0
    apply ha
    have h1 : κ₃ = 1 := by linear_combination h0 - h2
    rw [hκ₃, mul_inv_eq_one₀ hN] at h1
    exact mul_left_cancel₀ ha0 (by linear_combination h1)
  have hκ₄1 : κ₄ + 1 ≠ 0 := by
    intro h0
    apply ha
    have h1 : κ₄ = 1 := by linear_combination h0 - h2
    rw [hκ₄, mul_inv_eq_one₀ hN] at h1
    exact (mul_left_cancel₀ (mul_ne_zero hσa hσσa) (by linear_combination h1)).symm
  obtain ⟨z, hzC⟩ := z
  change z = d4z K at hz
  subst hz
  set Y₃ : ↥(d4C K σ) := ⟨d4x₃ K σ (κ₃ + 1)⁻¹, (d4x_short_mem σ hσ3 _).2.1⟩
  set Y₄ : ↥(d4C K σ) := ⟨d4x₄ K σ (κ₄ + 1)⁻¹, (d4x_short_mem σ hσ3 _).2.2⟩
  set X₃ : ↥(d4C K σ) := ⟨d4x₃ K σ 1, (d4x_short_mem σ hσ3 _).2.1⟩
  set X₄ : ↥(d4C K σ) := ⟨d4x₄ K σ 1, (d4x_short_mem σ hσ3 _).2.2⟩
  have hcz : ∀ {y : ↥(d4C K σ)}, (y : ModGL TwistTag.D4.tag K) * d4z K = d4z K * y →
      y ∈ Exc.cent (⟨d4z K, hzC⟩ : ↥(d4C K σ)) := fun hy => Exc.mem_cent_iff.2 hy
  have hhz : h ∈ Exc.cent (⟨d4z K, hzC⟩ : ↥(d4C K σ)) :=
    hcz (commute_of_conj_eq_d4 (ho_conj_d4x₆ σ A 1))
  have hX₃ : X₃ = ⁅h, Y₃⁆ := by
    refine Subtype.ext ?_
    rw [coe_commutatorElement_d4C, commutatorElement_def]
    change d4x₃ K σ 1 = trialityOuterTorus K σ A * d4x₃ K σ (κ₃ + 1)⁻¹ *
      (trialityOuterTorus K σ A)⁻¹ * (d4x₃ K σ (κ₃ + 1)⁻¹)⁻¹
    rw [ho_conj_d4x₃ σ hσ, d4x₃_inv, ← d4x₃_add, hAv]
    congr 1
    rw [← hκ₃]
    field_simp
  have hX₄ : X₄ = ⁅h, Y₄⁆ := by
    refine Subtype.ext ?_
    rw [coe_commutatorElement_d4C, commutatorElement_def]
    change d4x₄ K σ 1 = trialityOuterTorus K σ A * d4x₄ K σ (κ₄ + 1)⁻¹ *
      (trialityOuterTorus K σ A)⁻¹ * (d4x₄ K σ (κ₄ + 1)⁻¹)⁻¹
    rw [ho_conj_d4x₄ σ hσ, d4x₄_inv, ← d4x₄_add, hAv]
    congr 1
    rw [← hκ₄]
    field_simp
  set P : Subgroup ↥(d4C K σ) := closure {X₃, X₄}
  have hPX : P ≤ CFSG.ComponentClassification.AS76b.oUpperTwo (Exc.cent (⟨d4z K,
      hzC⟩ : ↥(d4C K σ))) ⊔
      ⁅Exc.cent (⟨d4z K, hzC⟩ : ↥(d4C K σ)), Exc.cent (⟨d4z K, hzC⟩ : ↥(d4C K σ))⁆ := by
    refine closure_le _ |>.2 fun y hy => le_sup_right (b := ⁅Exc.cent _, Exc.cent _⁆) ?_
    rcases hy with rfl | rfl
    · rw [hX₃]
      exact commutator_mem_commutator hhz (hcz (commute_d4x₆_d4x₃ σ 1 _).eq.symm)
    · rw [hX₄]
      exact commutator_mem_commutator hhz (hcz (commute_d4x₄_d4x₆ σ _ 1).eq)
  have hP : IsPGroup 2 P := by
    refine (isPGroup_graphFixedPosUnipotent_subgroupOf 2).to_le (closure_le _ |>.2 ?_)
    rintro y (rfl | rfl)
    · exact mem_subgroupOf.2 (rootSpan_trialityOrbit_le 2 (trialityOrbitProd_mem
        (Or.inr (Or.inl rfl)) hσ3 1))
    · exact mem_subgroupOf.2 (rootSpan_trialityOrbit_le 3 (trialityOrbitProd_mem
        (Or.inr (Or.inr rfl)) hσ3 1))
  have hz : (⟨d4z K, hzC⟩ : ↥(d4C K σ)) = ⁅X₄, X₃⁆ := by
    refine Subtype.ext ?_
    rw [coe_commutatorElement_d4C]
    change d4x₆ K 1 = ⁅d4x₄ K σ 1, d4x₃ K σ 1⁆
    rw [comm_d4x₄_d4x₃ σ hσ, mul_one, map_one, map_one]
    congr 1
    linear_combination -h2
  have hmem := commutator_le_admResidual_of_isPGroup hPX hP
    (commutator_mem_commutator (subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      (subset_closure (Set.mem_insert _ _)))
  rw [← hz] at hmem
  exact hmem

end ResZ

theorem map_commutatorElement_conj_d4 {G : Type*} [Group G] (n a b : G) :
    ⁅n * a * n⁻¹, n * b * n⁻¹⁆ = n * ⁅a, b⁆ * n⁻¹ := by
  simp only [commutatorElement_def]
  group

section ResT

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem comm_d4x₁_d4v0
    (s c d e f : K) :
    ⁅d4x₁ K σ s, d4v K σ 0 c d e f⁆ = d4v K σ 0 0 (σ s * σ (σ c) + σ (σ s) * σ c)
      ((σ s * σ (σ s) * c + σ (σ s * σ (σ s) * c) + σ (σ (σ s * σ (σ s) * c))) +
        (s * d + σ (s * d) + σ (σ (s * d))))
      (s * (σ c * σ (σ c)) + σ (s * (σ c * σ (σ c))) + σ (σ (s * (σ c * σ (σ c))))) := by
  have hconj : ∀ y, d4x₁ K σ s * y * (d4x₁ K σ s)⁻¹ = ⁅d4x₁ K σ s, y⁆ * y := fun y => by
    simp only [commutatorElement_def]
    group
  have hdef : ⁅d4x₁ K σ s, d4v K σ 0 c d e f⁆ =
      d4x₁ K σ s * d4v K σ 0 c d e f * (d4x₁ K σ s)⁻¹ * (d4v K σ 0 c d e f)⁻¹ := rfl
  rw [hdef, d4v_inv σ hσ, ← MulAut.conj_apply, d4v, map_mul, map_mul, map_mul, map_mul,
    MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply,
    d4x₂_zero, mul_one, mul_inv_cancel, one_mul, hconj, hconj, comm_d4x₁_d4x₃ σ hσ,
    comm_d4x₁_d4x₄ σ hσ, (commute_d4x₁_d4x₅ σ s e).eq, mul_inv_cancel_right,
    (commute_d4x₁_d4x₆ σ s f).eq, mul_inv_cancel_right]
  simp only [d4x₃_eq_d4v σ, d4x₄_eq_d4v σ, d4x₅_eq_d4v σ, d4x₆_eq_d4v σ, d4v_mul σ hσ]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine d4v_congr σ (by ring) (by linear_combination c * h2) (by linear_combination d * h2)
    (by linear_combination e * h2) ?_
  simp only [mul_zero, zero_mul, map_zero, add_zero, zero_add, add_mul, map_add]
  rw [mul_comm c d]
  linear_combination ((σ s * σ (σ c) + σ (σ s) * σ c) * c +
    (σ (σ s * σ (σ c) * c) + σ (σ (σ s) * σ c * c)) +
    (σ (σ (σ s * σ (σ c) * c)) + σ (σ (σ (σ s) * σ c * c))) +
    (d * c + σ (d * c) + σ (σ (d * c))) + f) * h2

include hσ in
theorem comm_d4v_d4v
    (b c d e f b' c' d' e' f' : K) :
    ⁅d4v K σ b c d e f, d4v K σ b' c' d' e' f'⁆ =
      d4x₆ K ((d * c' + σ (d * c') + σ (σ (d * c'))) + e * b' +
        (d' * c + σ (d' * c) + σ (σ (d' * c))) + e' * b) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [commutatorElement_def, d4v_inv σ hσ, d4v_inv σ hσ, d4v_mul σ hσ, d4v_mul σ hσ,
    d4v_mul σ hσ, d4x₆_eq_d4v σ]
  refine d4v_congr σ (by linear_combination (b + b') * h2) (by linear_combination (c + c') * h2)
    (by linear_combination (d + d') * h2) (by linear_combination (e + e') * h2) ?_
  simp only [add_mul, map_add]
  rw [mul_comm c d, mul_comm c' d']
  linear_combination (d * c + σ (d * c) + σ (σ (d * c)) + e * b + f +
    (d' * c' + σ (d' * c') + σ (σ (d' * c')) + e' * b' + f') +
    (d * c' + σ (d * c') + σ (σ (d * c')) + e * b')) * h2

include hσ in
theorem trialityMiddleRep_conj_d4v0
    (c d e f : K) :
    trialityMiddleRep K * d4v K σ 0 c d e f * (trialityMiddleRep K)⁻¹ =
      d4x₁ K σ c * d4v K σ 0 0 d f e := by
  rw [← MulAut.conj_apply, d4v, map_mul, map_mul, map_mul, map_mul, MulAut.conj_apply,
    MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, d4x₂_zero,
    mul_one, mul_inv_cancel, one_mul, trialityMiddleRep_conj_d4x₃, trialityMiddleRep_conj_d4x₄,
    trialityMiddleRep_conj_d4x₅, trialityMiddleRep_conj_d4x₆]
  rw [d4x₄_eq_d4v σ, d4x₆_eq_d4v σ, d4x₅_eq_d4v σ, mul_assoc, mul_assoc, d4v_mul σ hσ,
    d4v_mul σ hσ]
  refine congrArg _ (d4v_congr σ (by ring) (by ring) (by ring) (by ring) ?_)
  simp only [mul_zero, map_zero, add_zero, zero_add]

include hσ in
theorem comm_d4x₂_d4x₁_one
    (s : K) :
    ⁅d4x₂ K 1, d4x₁ K σ s⁆ =
      d4v K σ 0 s (σ s * σ (σ s)) (s * σ s * σ (σ s)) (s * σ s * σ (σ s)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hN : σ (s * σ s * σ (σ s)) = s * σ s * σ (σ s) := by
    rw [map_mul, map_mul, hσ]
    ring
  rw [← commutatorElement_inv, comm_d4x₁_d4x₂ σ hσ s 1 (map_one σ)]
  simp only [one_mul, one_pow]
  rw [d4x₅_eq_d4v σ, d4x₄_eq_d4v σ, d4x₆_eq_d4v σ, d4x₃_eq_d4v σ, d4v_mul σ hσ, d4v_mul σ hσ,
    d4v_mul σ hσ, d4v_inv σ hσ]
  refine d4v_congr σ (by ring) (by ring) (by ring) (by ring) ?_
  simp only [mul_zero, map_zero, add_zero, zero_add, zero_mul,
    show σ s * σ (σ s) * s = s * σ s * σ (σ s) by ring,
    show s * (σ s * σ (σ s)) = s * σ s * σ (σ s) by ring, hN]
  linear_combination (3 * (s * σ s * σ (σ s))) * h2

include hσ in
theorem comm_d4y₂_d4x₃_one
    (s : K) :
    ⁅d4y₂ K 1, d4x₃ K σ s⁆ =
      d4x₁ K σ s * d4v K σ 0 0 (σ s * σ (σ s)) (s * σ s * σ (σ s)) (s * σ s * σ (σ s)) := by
  rw [← trialityMiddleRep_conj_d4x₂ (1 : K), ← trialityMiddleRep_conj_d4x₁ σ s,
    map_commutatorElement_conj_d4, comm_d4x₂_d4x₁_one σ hσ, trialityMiddleRep_conj_d4v0 σ hσ]

theorem commutatorElement_mul_left_d4 {G : Type*} [Group G] {g a h : G}
    (hc : g * ⁅a, h⁆ = ⁅a, h⁆ * g) : ⁅g * a, h⁆ = ⁅a, h⁆ * ⁅g, h⁆ := by
  calc ⁅g * a, h⁆ = g * ⁅a, h⁆ * h * g⁻¹ * h⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅a, h⁆ * g * h * g⁻¹ * h⁻¹ := by rw [hc]
    _ = ⁅a, h⁆ * ⁅g, h⁆ := by simp only [commutatorElement_def]; group

include hσ in
theorem comm_g_h_d4
    (s s' : K) :
    ⁅d4x₁ K σ s * d4v K σ 0 0 (σ s * σ (σ s)) (s * σ s * σ (σ s)) (s * σ s * σ (σ s)),
        d4v K σ 0 s' (σ s' * σ (σ s')) (s' * σ s' * σ (σ s')) (s' * σ s' * σ (σ s'))⁆ =
      d4v K σ 0 0 (σ s * σ (σ s') + σ (σ s) * σ s')
        ((σ s * σ (σ s) * s' + σ (σ s * σ (σ s) * s') + σ (σ (σ s * σ (σ s) * s'))) +
          (s * (σ s' * σ (σ s')) + σ (s * (σ s' * σ (σ s'))) + σ (σ (s * (σ s' * σ (σ s'))))))
        ((σ s * σ (σ s) * s' + σ (σ s * σ (σ s) * s') + σ (σ (σ s * σ (σ s) * s'))) +
          (s * (σ s' * σ (σ s')) + σ (s * (σ s' * σ (σ s'))) + σ (σ (s * (σ s' * σ (σ s')))))) := by
  have hah := comm_d4v_d4v σ hσ 0 0 (σ s * σ (σ s)) (s * σ s * σ (σ s)) (s * σ s * σ (σ s)) 0 s'
    (σ s' * σ (σ s')) (s' * σ s' * σ (σ s')) (s' * σ s' * σ (σ s'))
  rw [commutatorElement_mul_left_d4 (by rw [hah]; exact (commute_d4x₁_d4x₆ σ s _).eq), hah,
    comm_d4x₁_d4v0 σ hσ, d4x₆_eq_d4v σ, d4v_mul σ hσ]
  refine d4v_congr σ (by ring) (by ring) (by ring) (by ring) ?_
  simp only [mul_zero, map_zero, add_zero, zero_add]

theorem commute_d4y₂_d4x₄_one
    : d4y₂ K 1 * d4t K σ = d4t K σ * d4y₂ K 1 := by
  have h₄ : trialityMiddleRep K * d4t K σ * (trialityMiddleRep K)⁻¹ = d4t K σ :=
    trialityMiddleRep_conj_d4x₄ σ (1 : K)
  rw [← trialityMiddleRep_conj_d4x₂ (1 : K), ← h₄]
  have h := (commute_d4x₄_d4x₂ σ 1 1).eq
  calc trialityMiddleRep K * d4x₂ K 1 * (trialityMiddleRep K)⁻¹ *
        (trialityMiddleRep K * d4t K σ * (trialityMiddleRep K)⁻¹) =
      trialityMiddleRep K * (d4x₂ K 1 * d4x₄ K σ 1) * (trialityMiddleRep K)⁻¹ := by
        rw [d4t]; group
    _ = trialityMiddleRep K * (d4x₄ K σ 1 * d4x₂ K 1) * (trialityMiddleRep K)⁻¹ := by rw [← h]
    _ = _ := by rw [d4t]; group

include hσ in
theorem residualMem_t
    [Finite K] {x : K} (hx : σ x ≠ x) {t : ↥(d4C K σ)}
    (ht : (t : ModGL TwistTag.D4.tag K) = d4t K σ) : Exc.ResidualMem t := by
  have hσ3 := toRingHom_pow_three_d4 σ hσ
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨s, s', hs, hs', hcross⟩ := exists_cross_eq_one_d4 σ hσ hx
  obtain ⟨t, htC⟩ := t
  change t = d4t K σ at ht
  subst ht
  set T₀ : ↥(d4C K σ) := ⟨d4t K σ, htC⟩
  have hct : ∀ {y : ↥(d4C K σ)}, (y : ModGL TwistTag.D4.tag K) * d4t K σ = d4t K σ * y →
      y ∈ Exc.cent T₀ := fun hy => Exc.mem_cent_iff.2 hy
  set Y₂ : ↥(d4C K σ) := ⟨d4y₂ K 1, (d4y_long_mem σ (map_one σ)).1⟩
  set X₂ : ↥(d4C K σ) := ⟨d4x₂ K 1, (d4x_long_mem σ (map_one σ)).1⟩
  have hY₂ : Y₂ ∈ Exc.cent T₀ := hct (commute_d4y₂_d4x₄_one σ)
  have hX₂ : X₂ ∈ Exc.cent T₀ := hct (commute_d4x₄_d4x₂ σ 1 1).eq.symm
  have hX₁ : ∀ u : K, u + σ u + σ (σ u) = 0 →
      (⟨d4x₁ K σ u, (d4x_short_mem σ hσ3 u).1⟩ : ↥(d4C K σ)) ∈ Exc.cent T₀ := fun u hu => by
    refine hct ?_
    have h := comm_d4x₁_d4x₄ σ hσ u 1
    rw [mul_one, hu, d4x₅_zero, commutatorElement_eq_one_iff_mul_comm] at h
    exact h
  have hX₃ : ∀ u : K, u + σ u + σ (σ u) = 0 →
      (⟨d4x₃ K σ u, (d4x_short_mem σ hσ3 u).2.1⟩ : ↥(d4C K σ)) ∈ Exc.cent T₀ := fun u hu => by
    refine hct ?_
    have h := comm_d4x₄_d4x₃ σ hσ 1 u
    rw [one_mul, hu, d4x₆_zero, commutatorElement_eq_one_iff_mul_comm] at h
    exact h.symm
  obtain ⟨G, hGd⟩ : ∃ G : K → ↥(d4C K σ),
      ∀ u, G u = ⁅Y₂, ⟨d4x₃ K σ u, (d4x_short_mem σ hσ3 u).2.1⟩⁆ := ⟨_, fun _ => rfl⟩
  obtain ⟨H, hHd⟩ : ∃ H : K → ↥(d4C K σ),
      ∀ u, H u = ⁅X₂, ⟨d4x₁ K σ u, (d4x_short_mem σ hσ3 u).1⟩⁆ := ⟨_, fun _ => rfl⟩
  have hG : ∀ u, ((G u : ↥(d4C K σ)) : ModGL TwistTag.D4.tag K) =
      d4x₁ K σ u * d4v K σ 0 0 (σ u * σ (σ u)) (u * σ u * σ (σ u)) (u * σ u * σ (σ u)) :=
    fun u => by rw [hGd, coe_commutatorElement_d4C]; exact comm_d4y₂_d4x₃_one σ hσ u
  have hH : ∀ u, ((H u : ↥(d4C K σ)) : ModGL TwistTag.D4.tag K) =
      d4v K σ 0 u (σ u * σ (σ u)) (u * σ u * σ (σ u)) (u * σ u * σ (σ u)) :=
    fun u => by rw [hHd, coe_commutatorElement_d4C]; exact comm_d4x₂_d4x₁_one σ hσ u
  have hGH : ∀ u, ((G u : ↥(d4C K σ)) : ModGL TwistTag.D4.tag K) =
      trialityMiddleRep K * (H u : ModGL TwistTag.D4.tag K) * (trialityMiddleRep K)⁻¹ :=
    fun u => by
      rw [hGd, hHd, coe_commutatorElement_d4C, coe_commutatorElement_d4C,
        ← map_commutatorElement_conj_d4, trialityMiddleRep_conj_d4x₂, trialityMiddleRep_conj_d4x₁]
  set P : Subgroup ↥(d4C K σ) := closure {G s, G s', H s, H s'}
  have hPX : P ≤ CFSG.ComponentClassification.AS76b.oUpperTwo (Exc.cent T₀) ⊔
      ⁅Exc.cent T₀, Exc.cent T₀⁆ := by
    refine closure_le _ |>.2 fun y hy => le_sup_right (b := ⁅Exc.cent T₀, Exc.cent T₀⁆) ?_
    rcases hy with rfl | rfl | rfl | rfl
    · rw [hGd]; exact commutator_mem_commutator hY₂ (hX₃ s hs)
    · rw [hGd]; exact commutator_mem_commutator hY₂ (hX₃ s' hs')
    · rw [hHd]; exact commutator_mem_commutator hX₂ (hX₁ s hs)
    · rw [hHd]; exact commutator_mem_commutator hX₂ (hX₁ s' hs')
  have hU : ∀ y : ↥(d4C K σ), (y : ModGL TwistTag.D4.tag K) ∈ posUnipotent TwistTag.D4.tag K →
      y ∈ (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf (d4C K σ) := fun y hy =>
    mem_subgroupOf.2 (mem_inf.2 ⟨hy, graphFixedRootGroup_le _ _ _ y.2⟩)
  have hP : IsPGroup 2 P := by
    refine (isPGroup_graphFixedPosUnipotent_subgroupOf 2).to_le (closure_le _ |>.2 ?_)
    rintro y (rfl | rfl | rfl | rfl)
    · exact hU _ (by rw [hG]; exact d4coord_mem_posUnipotent σ _ _ _ _ _ _)
    · exact hU _ (by rw [hG]; exact d4coord_mem_posUnipotent σ _ _ _ _ _ _)
    · exact hU _ (by rw [hH]; exact d4v_mem_posUnipotent σ _ _ _ _ _)
    · exact hU _ (by rw [hH]; exact d4v_mem_posUnipotent σ _ _ _ _ _)
  have hteq : T₀ = ⁅G s, H s'⁆ * ⁅G s, G s'⁆ * ⁅H s, H s'⁆ := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_commutatorElement_d4C, coe_commutatorElement_d4C,
      coe_commutatorElement_d4C, hGH s', hGH s, map_commutatorElement_conj_d4, ← hGH s, hG, hH,
      hH, comm_g_h_d4 σ hσ, comm_d4v_d4v σ hσ, trialityMiddleRep_conj_d4x₆, d4x₅_eq_d4v σ,
      d4x₆_eq_d4v σ, d4v_mul σ hσ, d4v_mul σ hσ]
    change d4x₄ K σ 1 = _
    rw [d4x₄_eq_d4v σ]
    refine d4v_congr σ (by ring) (by ring) (by rw [hcross]; ring) ?_ ?_
    · simp only [map_mul, hσ]
      linear_combination (-(σ s * σ (σ s) * s' + σ (σ s) * s * σ s' + s * σ s * σ (σ s') +
        s * σ s' * σ (σ s') + σ s * σ (σ s') * s' + σ (σ s) * s' * σ s')) * h2
    · simp only [mul_zero, map_zero, add_zero, zero_add, map_mul, hσ]
      linear_combination (-(σ s * σ (σ s) * s' + σ (σ s) * s * σ s' + s * σ s * σ (σ s') +
        s * σ s' * σ (σ s') + σ s * σ (σ s') * s' + σ (σ s) * s' * σ s')) * h2
  have hGs : G s ∈ P := subset_closure (Set.mem_insert _ _)
  have hGs' : G s' ∈ P := subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hHs : H s ∈ P :=
    subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have hHs' : H s' ∈ P := subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
    (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  have hmem := commutator_le_admResidual_of_isPGroup hPX hP
    (mul_mem (mul_mem (commutator_mem_commutator hGs hHs') (commutator_mem_commutator hGs hGs'))
      (commutator_mem_commutator hHs hHs'))
  rw [← hteq] at hmem
  exact hmem

end ResT

section ClassData

theorem d4Zz_le
    (K : Type) [Field K] [CharP K 2] (σ : K ≃+* K) : d4Zz K σ ≤ d4C K σ :=
    fun x hx => by
  obtain ⟨c, hc, rfl⟩ := (mem_d4Zz σ).1 hx
  exact (d4x_long_mem σ hc).2.2

theorem d4Zt_le
    {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K)
    (hσ : ∀ c, σ (σ (σ c)) = c) :
    d4Zt K σ ≤ d4C K σ := fun x hx => by
  obtain ⟨c, -, rfl⟩ := (mem_d4Zt σ).1 hx
  exact (d4x_short_mem σ (toRingHom_pow_three_d4 σ hσ) c).2.2

theorem d4_classData_z
    (m : ℕ) (hm : 1 ≤ m) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ m) ^ 3) (σ : K ≃+* K) (hσq : ∀ c, σ c = c ^ 2 ^ m)
    (z : ↥(d4C K σ)) (hz : (z : ModGL TwistTag.D4.tag K) = d4z K) :
    Exc.ClassData (2 ^ m) z ((d4Zz K σ).subgroupOf (d4C K σ)) ∧ Exc.ResidualMem z := by
  have := charP_two_of_card_d4 hK
  have hσ := sigma_cube_of_card_d4 σ hK hσq
  obtain ⟨x, hx⟩ := exists_not_fixed_d4 σ hm hK hσq
  have hres := residualMem_z σ hσ hx hz
  have hcen := d4_centreData_z σ hσ hz
  refine ⟨⟨hcen, ?_, charTwo_d4 σ hσ (Subtype.ext ?_) hcen.ne_one, Or.inl hres⟩, hres⟩
  · rw [Nat.card_congr (subgroupOfEquivOfLe (d4Zz_le K σ)).toEquiv, card_d4Zz σ,
      card_d4k_of_card σ hm hK hσq]
  · rw [Subgroup.coe_mul, hz, Subgroup.coe_one, d4z]
    exact d4x₆_mul_self K 1

theorem d4_classData_t
    (m : ℕ) (hm : 1 ≤ m) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ m) ^ 3) (σ : K ≃+* K) (hσq : ∀ c, σ c = c ^ 2 ^ m)
    (t : ↥(d4C K σ)) (ht : (t : ModGL TwistTag.D4.tag K) = d4t K σ) :
    Exc.ClassData (2 ^ m) t ((d4Zt K σ).subgroupOf (d4C K σ)) ∧ Exc.ResidualMem t := by
  have := charP_two_of_card_d4 hK
  have hσ := sigma_cube_of_card_d4 σ hK hσq
  obtain ⟨x, hx⟩ := exists_not_fixed_d4 σ hm hK hσq
  have hres := residualMem_t σ hσ hx ht
  have hcen := d4_centreData_t σ hσ ht
  refine ⟨⟨hcen, ?_, charTwo_d4 σ hσ (Subtype.ext ?_) hcen.ne_one, Or.inl hres⟩, hres⟩
  · rw [Nat.card_congr (subgroupOfEquivOfLe (d4Zt_le σ hσ)).toEquiv, card_d4Zt σ,
      card_d4k_of_card σ hm hK hσq]
  · rw [Subgroup.coe_mul, ht, Subgroup.coe_one, d4t]
    exact d4x₄_mul_self σ 1

end ClassData

end CFSG.ComponentClassification.RankTwoExceptional.D4
