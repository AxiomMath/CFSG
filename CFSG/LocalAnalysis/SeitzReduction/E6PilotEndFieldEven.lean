module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotEndFieldEvenAut
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotMainRows

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut)

section Generic

theorem exists_orderOf_eq_two_pow_of_odd_ker {G : Type*} [Group G] [Finite G] {B : Type*}
    [Group B] (φ : G →* B) (hker : Odd (Nat.card φ.ker)) {ξ : B} (hξ : ξ ∈ φ.range) {c : ℕ}
    (hξo : orderOf ξ = 2 ^ c) : ∃ x : G, φ x = ξ ∧ orderOf x = 2 ^ c := by
  obtain ⟨x₀, rfl⟩ := hξ
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · refine ⟨1, ?_, by rw [orderOf_one, pow_zero]⟩
    rw [pow_zero, orderOf_eq_one_iff] at hξo
    rw [map_one, hξo]
  set y := x₀ ^ (2 ^ c) with hy
  have hyker : y ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hy, map_pow, ← hξo, pow_orderOf_eq_one]
  have hr : Odd (orderOf y) := by
    have h1 : orderOf (⟨y, hyker⟩ : φ.ker) ∣ Nat.card φ.ker := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hker h1
  have hcop : Nat.Coprime (orderOf y) (2 ^ c) :=
    Nat.Coprime.pow_right c (Nat.coprime_two_right.2 hr)
  have h2c : 1 < 2 ^ c := Nat.one_lt_two_pow (by omega)
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h2c
  refine ⟨x₀ ^ (orderOf y * u), ?_, ?_⟩
  · rw [map_pow, ← pow_mod_orderOf, hξo, hu, pow_one]
  · have hx1 : (x₀ ^ (orderOf y * u)) ^ 2 ^ c = 1 := by
      rw [← pow_mul, mul_comm (orderOf y * u), pow_mul, ← hy, pow_mul, pow_orderOf_eq_one,
        one_pow]
    have hdvd1 : orderOf (x₀ ^ (orderOf y * u)) ∣ 2 ^ c := orderOf_dvd_of_pow_eq_one hx1
    have hdvd2 : 2 ^ c ∣ orderOf (x₀ ^ (orderOf y * u)) := by
      have h := orderOf_map_dvd φ (x₀ ^ (orderOf y * u))
      rwa [map_pow, ← pow_mod_orderOf, hξo, hu, pow_one, hξo] at h
    exact Nat.dvd_antisymm hdvd1 hdvd2

variable {N B : Type*} [Group N] [Group B]

theorem orderOf_mk_ker (Φ : N →* B) (x : N) :
    orderOf (QuotientGroup.mk' Φ.ker x) = orderOf (Φ x) := by
  rw [← orderOf_injective (QuotientGroup.kerLift Φ) (QuotientGroup.kerLift_injective Φ),
    QuotientGroup.mk'_apply, QuotientGroup.kerLift_mk]

theorem card_quotient_ker (Φ : N →* B) : Nat.card (N ⧸ Φ.ker) = Nat.card Φ.range :=
  Nat.card_congr (QuotientGroup.quotientKerEquivRange Φ).toEquiv

end Generic

section Endgame


variable {G : Type} [Group G] [Finite G] {G₀ : Subgroup G}

theorem exists_normal_index_two_of_E6_field_even {f : ℕ} (hfe : Even f) (hf : 1 ≤ f)
    (K₂ : Type) [Field K₂] [Finite K₂] (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (hperf : ⁅G₀, G₀⁆ = G₀)
    (hC : Odd (Nat.card (centralizer (G₀ : Set G))))
    (e₀ : G₀ ⧸ center G₀ ≃* adjointGroup .E6 K₂) {t : G} (htN : t ∈ normalizer (G₀ : Set G))
    (ht : orderOf t = 2)
    (hfield : ∃ (σ : K₂ ≃+* K₂) (φ : MulAut (adjointGroup .E6 K₂)), σ ^ 2 = 1 ∧ σ ≠ 1 ∧
      φ * normalizerQuotMulAut e₀ ⟨t, htN⟩ * φ⁻¹ = entrywiseAdjointAut .E6 σ)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  obtain ⟨σ, φ, hσ2, hσ1, hφ⟩ := hfield
  have : Group.IsPerfect G₀ := Subgroup.isPerfect_iff.2 hperf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2f : 1 ≤ 2 * f := by omega
  obtain ⟨-, hσq, -⟩ := ringEquiv_sq_eq_one_facts Nat.prime_two h2f hK₂ hσ2 hσ1
  rw [show 2 * f / 2 = f by omega] at hσq
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    have h := congrArg (fun φ : K₂ ≃+* K₂ => φ c) hσ2
    simpa [sq] using h
  obtain ⟨-, hcyc⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K₂ hK₂
  have hcomm : ∀ a b : RingAut K₂, a * b = b * a := (IsCyclic.commGroup).mul_comm
  set N := normalizer (G₀ : Set G) with hN
  set ρ := normalizerQuotMulAut e₀ with hρ
  set t₀ : N := ⟨t, htN⟩ with ht₀
  have hker : Odd (Nat.card ρ.ker) := by
    rw [hρ, EPilot.card_ker_normalizerQuotMulAut]
    exact hC
  obtain ⟨Θ, hΘ⟩ := exists_fieldGraphCoordinate_E6 K₂
  set χ : MulAut (adjointGroup .E6 K₂) →* (K₂ ≃+* K₂) := (MonoidHom.fst _ _).comp Θ with hχdef
  have hχ : ∀ (g : adjointGroup .E6 K₂) (a : Fin Tag.E6.rank → K₂ˣ) (ρ' : K₂ ≃+* K₂) (ε : ℕ),
      χ (MulAut.conj g * exactNormalAut .E6 K₂ a ρ' ε) = ρ' := fun g a ρ' ε => by
    rw [hχdef, MonoidHom.comp_apply, hΘ]
    rfl
  have hχconj : ∀ α β : MulAut (adjointGroup .E6 K₂), χ (β * α * β⁻¹) = χ α := fun α β => by
    rw [map_mul, map_mul, map_inv, hcomm (χ β), mul_assoc, mul_inv_cancel, mul_one]
  have hχσ : χ (entrywiseAdjointAut .E6 σ) = σ := by
    rw [← FieldGraphFieldPointwise.exactNormalAut_one_zero_eq,
      show exactNormalAut .E6 K₂ 1 σ 0 = MulAut.conj 1 * exactNormalAut .E6 K₂ 1 σ 0 by
        rw [map_one, one_mul], hχ]
  have hχt : χ (ρ t₀) = σ := by
    have h1 := hχconj (ρ t₀) φ
    rw [hφ, hχσ] at h1
    exact h1.symm
  have hout : ρ t₀ ∉ (MulAut.conj : adjointGroup .E6 K₂ →* MulAut (adjointGroup .E6 K₂)).range := by
    rintro ⟨x, hx⟩
    apply hσ1
    rw [← hχt, ← hx, show MulAut.conj x = MulAut.conj x * exactNormalAut .E6 K₂ 1 1 0 by
      rw [exactNormalAut_one_one_zero_E6, mul_one], hχ]
  set Φ : N →* (K₂ ≃+* K₂) := χ.comp ρ with hΦ
  have hΦt : Φ t₀ = σ := hχt
  have hσo : orderOf σ = 2 := orderOf_eq_prime hσ2 hσ1
  have hσP : σ ∈ Φ.range := ⟨t₀, hΦt⟩
  set c := (Nat.card Φ.range).factorization 2 with hc
  have h2P : 2 ∣ Nat.card Φ.range := by
    have h := orderOf_dvd_natCard (⟨σ, hσP⟩ : Φ.range)
    rwa [Subgroup.orderOf_mk, hσo] at h
  have hc1 : 1 ≤ c := Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2P
  have hQ : ¬ 2 ^ (c + 1) ∣ Nat.card (N ⧸ Φ.ker) := by
    rw [card_quotient_ker]
    exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' Nat.prime_two
  suffices hx : ∃ x : N, orderOf x = 2 ^ c ∧ orderOf (Φ x) = 2 ^ c ∧
      IsConj t ((x : G) ^ 2 ^ (c - 1)) by
    obtain ⟨x, hxo, hxΦ, hpow⟩ := hx
    exact EPilot.exists_normal_index_two_of_unique_of_quotientSub Φ.ker huniq x.2 hc1
      (by rw [Subgroup.orderOf_coe]; exact hxo) (by rw [Subtype.coe_eta, orderOf_mk_ker]; exact hxΦ)
      hQ hpow
  rcases (show c = 1 ∨ 2 ≤ c by omega) with hc1' | hc2
  ·
    refine ⟨t₀, ?_, ?_, ?_⟩
    · rw [Subgroup.orderOf_mk, ht, hc1', pow_one]
    · rw [hΦt, hσo, hc1', pow_one]
    · rw [hc1', Nat.sub_self, pow_zero, pow_one]
  ·
    obtain ⟨T⟩ : Nonempty (Sylow 2 N) := inferInstance
    have hfs : Function.Surjective Φ.rangeRestrict := Φ.rangeRestrict_surjective
    set TP := T.mapSurjective hfs with hTP
    have hTPcard : Nat.card TP = 2 ^ c := Sylow.card_eq_multiplicity TP
    obtain ⟨z, hz⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (TP : Subgroup Φ.range))
    have hzT : (z : Φ.range) ∈ (T : Subgroup N).map Φ.rangeRestrict := z.2
    obtain ⟨y, hyT, hyz⟩ := hzT
    have hyo : orderOf (Φ y) = 2 ^ c := by
      have h1 : orderOf (Φ.rangeRestrict y) = orderOf (Φ y) := by
        rw [← Subgroup.orderOf_coe, MonoidHom.coe_rangeRestrict]
      rw [← h1, hyz, Subgroup.orderOf_coe, hz, hTPcard]
    have hw2 : IsPGroup 2 (zpowers (ρ y)) := by
      have h1 : IsPGroup 2 (zpowers y) := T.isPGroup'.to_le (zpowers_le.2 hyT)
      have h2 := h1.map ρ
      rwa [MonoidHom.map_zpowers] at h2
    have hI : (MulAut.conj : adjointGroup .E6 K₂ →* MulAut (adjointGroup .E6 K₂)).range ≤
        ρ.range := by
      rintro _ ⟨u, rfl⟩
      obtain ⟨m, hm⟩ := EPilot.exists_normalizerQuotMulAut_eq_conj e₀ u
      exact ⟨m, hm⟩
    obtain ⟨ξ, hξA, hξo, hξχ, ψ, hψ⟩ :=
      exists_exact_lift_E6 hK₂ hΘ hσ2 hσ1 hI ⟨y, rfl⟩ hw2 hc2 hyo
    obtain ⟨x, hxρ, hxo⟩ := exists_orderOf_eq_two_pow_of_odd_ker ρ hker hξA hξo
    refine ⟨x, hxo, ?_, ?_⟩
    · change orderOf (Θ (ρ x)).1 = 2 ^ c
      rw [hxρ, hξχ]
      exact hyo
    ·
      obtain ⟨u₁, hu₁⟩ := exists_conj_eq_conj_entrywise_E6 hfe hK₂ hσσ hσq ψ
      obtain ⟨u₂, hu₂⟩ := exists_conj_eq_conj_entrywise_E6 hfe hK₂ hσσ hσq φ⁻¹
      obtain ⟨m, hm⟩ := EPilot.exists_normalizerQuotMulAut_eq_conj e₀ (u₁ * u₂⁻¹)
      have hρt : ρ t₀ = φ⁻¹ * entrywiseAdjointAut .E6 σ * φ⁻¹⁻¹ := by
        rw [← hφ]
        group
      have key : ρ (m * t₀ * m⁻¹) = ρ (x ^ 2 ^ (c - 1)) := by
        rw [map_mul, map_mul, map_inv, hm, map_pow, hxρ, hψ, hu₁, hρt, hu₂, map_mul, map_inv]
        group
      have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
      have hs2 : ((m * t₀ * m⁻¹ : N) : G) ^ 2 = 1 := by
        have e2 : ((m : G) * t * (m : G)⁻¹) ^ 2 = (m : G) * t ^ 2 * (m : G)⁻¹ := by
          rw [sq, sq]
          group
        simp only [coe_mul, coe_inv, ht₀, e2, ht2, mul_one, mul_inv_cancel]
      have hy2 : ((x ^ 2 ^ (c - 1) : N) : G) ^ 2 = 1 := by
        rw [← SubgroupClass.coe_pow, ← pow_mul, ← pow_succ, show c - 1 + 1 = c by omega, ← hxo,
          pow_orderOf_eq_one, OneMemClass.coe_one]
      have h1 := EPilot.isConj_of_action_eq ρ hker (m * t₀ * m⁻¹).2 (x ^ 2 ^ (c - 1)).2 hs2 hy2
        (by rw [Subtype.coe_eta, Subtype.coe_eta]; exact key)
      have h2 : IsConj t ((m * t₀ * m⁻¹ : N) : G) := by
        refine isConj_iff.2 ⟨(m : G), ?_⟩
        simp only [coe_mul, coe_inv, ht₀]
      have h3 := h2.trans h1
      rwa [SubgroupClass.coe_pow] at h3

theorem false_of_simple_of_E6_field_even [IsSimpleGroup G] {f : ℕ} (hfe : Even f) (hf : 1 ≤ f)
    (K₂ : Type) [Field K₂] [Finite K₂] (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (hperf : ⁅G₀, G₀⁆ = G₀)
    (hC : Odd (Nat.card (centralizer (G₀ : Set G))))
    (e₀ : G₀ ⧸ center G₀ ≃* adjointGroup .E6 K₂) {t : G} (htN : t ∈ normalizer (G₀ : Set G))
    (ht : orderOf t = 2)
    (hfield : ∃ (σ : K₂ ≃+* K₂) (φ : MulAut (adjointGroup .E6 K₂)), σ ^ 2 = 1 ∧ σ ≠ 1 ∧
      φ * normalizerQuotMulAut e₀ ⟨t, htN⟩ * φ⁻¹ = entrywiseAdjointAut .E6 σ)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) :
    False := by
  have hout : normalizerQuotMulAut e₀ ⟨t, htN⟩ ∉
      (MulAut.conj : adjointGroup .E6 K₂ →* MulAut (adjointGroup .E6 K₂)).range := by
    obtain ⟨σ, φ, -, hσ1, hφ⟩ := hfield
    obtain ⟨Θ, hΘ⟩ := exists_fieldGraphCoordinate_E6 K₂
    rintro ⟨x, hx⟩
    apply hσ1
    have h1 : (Θ (entrywiseAdjointAut .E6 σ)).1 = σ := by
      rw [← FieldGraphFieldPointwise.exactNormalAut_one_zero_eq,
        show exactNormalAut .E6 K₂ 1 σ 0 = MulAut.conj 1 * exactNormalAut .E6 K₂ 1 σ 0 by
          rw [map_one, one_mul], hΘ]
    have h2 : (Θ (MulAut.conj x)).1 = 1 := by
      rw [show MulAut.conj x = MulAut.conj x * exactNormalAut .E6 K₂ 1 1 0 by
        rw [exactNormalAut_one_one_zero_E6, mul_one], hΘ]
    rw [← h1, ← hφ, ← hx, map_mul, map_mul, map_inv, Prod.fst_mul, Prod.fst_mul, Prod.fst_inv, h2,
      mul_one, mul_inv_cancel]
  exact CFSG.SeitzReduction.not_exists_normal_index_two_of_simple
    (EPilot.two_lt_card_of_normalizerQuotMulAut_not_mem_range e₀ htN hout)
    (exists_normal_index_two_of_E6_field_even hfe hf K₂ hK₂ hperf hC e₀ htN ht hfield huniq)

theorem e6FieldEndgameEvenInput_holds : E6FieldEndgameEvenInput := by
  intro G _ _ _ G₀ f hf hfe K₂ _ _ hK₂ hperf _ hC e₀ t htN ht hfield huniq
  exact false_of_simple_of_E6_field_even hfe hf K₂ hK₂ hperf hC e₀ htN ht hfield huniq

end Endgame

end CFSG.SeitzReduction.E6Pilot
