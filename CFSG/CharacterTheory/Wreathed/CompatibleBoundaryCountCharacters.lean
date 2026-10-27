module

public import CFSG.CharacterTheory.Wreathed.CompatibleBoundaryCountKernel
public import CFSG.CharacterTheory.Wreathed.CompatibleCentralizerFamilies

public noncomputable section

namespace CFSG.Wreathed.CompatibleFamilies

open CFSG.Wreathed CFSG.Wreathed.BrauerWong CFSG.Wreathed.BaseFourCentralizerStructure
open scoped Classical Pointwise

universe u

variable {G : Type u} [Group G] {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))

theorem closure_half_eq (hn : 1 ≤ n) :
    Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
      wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)} =
      Subgroup.closure {wreathModelHom S e (Original.x (2 ^ n)),
        wreathModelHom S e (Original.x2 (2 ^ n))} := by
  rw [← modelT_eq_actual_generated, modelT_eq_closure S e hn]

theorem boundaryProduct_eq (η : G) :
    boundaryProduct S e η = boundaryCommutator S e η ⊔
      (commutator (Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))})).map
        (Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))}).subtype := by
  unfold boundaryProduct
  rw [x_eq_modelHom]

variable [Finite G]

theorem exists_family_of_extension [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x)
    (hn : 2 ≤ n) {η : G} (hη : η ∈ Subgroup.normalizer (modelBase S e : Set G))
    (hord : orderOf ((modelBase S e).normalizerMonoidHom ⟨η, hη⟩) = 3)
    (χ : ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)) → ℂ)
    {lam : Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))} →* ℂˣ}
    (h1 : ∀ (v : Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))})
      (y : ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G))),
        (v : G) = y → (lam v : ℂ) = χ y)
    (h2 : ∀ v : Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))},
      (v : G) ∈ (S : Subgroup G) → lam v = 1)
    (h3 : ∀ c c' : Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))},
      (c : G) ∈ Subgroup.centralizer (Subgroup.closure {wreathModelHom S e (Original.x (2 ^ n)),
        wreathModelHom S e (Original.x2 (2 ^ n))} : Set G) →
      (c' : G) = η⁻¹ * c * η → lam c' = lam c)
    (θt : Subgroup.centralizer ((S : Subgroup G) : Set G) → ℂ)
    (hθt : ∀ (c : Subgroup.centralizer ((S : Subgroup G) : Set G)) (z : G)
      (y : ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G))),
        z ∈ modelCenter S e → (c : G) = z * y → θt c = χ y) :
    ∃ ψ, CompatibleCentralizerFamily 2 (S : Subgroup G) θt ψ := by
  have cfg := localConfig S e hnonab hn hη hord
  have hlam := isInvariant S e hn hη hord h2 h3
  obtain ⟨ψ, hψ⟩ := cfg.exists_isSpecialFamily (lam := lam)
  exact ⟨ψ, compatible_of_isSpecialFamily S e hn cfg hlam hψ (isSpecial_sylow S e hn)
    (sylow_le_centralizer_x S e hn) χ h1 h2 θt hθt⟩

theorem exists_hom_of_family [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x)
    (hn : 2 ≤ n) {η : G} (hη : η ∈ Subgroup.normalizer (modelBase S e : Set G))
    (hord : orderOf ((modelBase S e).normalizerMonoidHom ⟨η, hη⟩) = 3)
    (χ : ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)) → ℂ)
    (θt : Subgroup.centralizer ((S : Subgroup G) : Set G) → ℂ)
    (hθt : ∀ (c : Subgroup.centralizer ((S : Subgroup G) : Set G))
      (y : ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G))),
        (c : G) = y → θt c = χ y)
    {ψ : ∀ Q : Subgroup G, Subgroup.centralizer (Q : Set G) →* ℂˣ}
    (hψ : CompatibleCentralizerFamily 2 (S : Subgroup G) θt ψ) :
    ∃ μ : ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)) →* ℂˣ,
      (∀ y, (μ y : ℂ) = χ y) ∧ boundaryKernel S e η ≤ μ.ker := by
  set J := wreathModelHom S e (Original.x (2 ^ n))
  set J₁ := wreathModelHom S e (Original.x2 (2 ^ n))
  have hEN : ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)) ≤
      Subgroup.centralizer {J} := by
    have h := oddCore_sylow_le_centralizer S e
    rwa [x_eq_modelHom] at h
  obtain ⟨lam, h1, -, h3⟩ := exists_extension_of_family hnonab S e hn hη
    (ambientOddCore_le _) χ θt hθt hψ
  have hηT : η ∈ Subgroup.normalizer (Subgroup.closure {J, J₁} : Set G) :=
    (eta_properties S e hn hη hord).1
  have hCN : Subgroup.centralizer (Subgroup.closure {J, J₁} : Set G) ≤
      Subgroup.centralizer {J} := LocalConfig.centralizer_le
  have hD : boundaryProduct S e η ≤ (lam.ker).map (Subgroup.centralizer {J}).subtype := by
    rw [boundaryProduct_eq]
    apply sup_le
    · rw [boundaryCommutator, Subgroup.closure_le]
      rintro _ ⟨c, hc, rfl⟩
      rw [closure_half_eq S e (by omega)] at hc
      have hcC : c ∈ Subgroup.centralizer (Subgroup.closure {J, J₁} : Set G) :=
        ambientOddCore_le _ hc
      have hc'C : η⁻¹ * c * η ∈ Subgroup.centralizer (Subgroup.closure {J, J₁} : Set G) :=
        LocalConfig.conj_mem_centralizer hηT hcC
      have hval := h3 ⟨c, hCN hcC⟩ ⟨_, hCN hc'C⟩ hcC rfl
      refine ⟨⟨c, hCN hcC⟩⁻¹ * ⟨_, hCN hc'C⟩, ?_, rfl⟩
      change _ ∈ lam.ker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hval, inv_mul_cancel]
    · apply Subgroup.map_mono
      exact Abelianization.commutator_subset_ker lam
  refine ⟨lam.comp (Subgroup.inclusion hEN), fun y => h1 _ y rfl, ?_⟩
  intro y hy
  obtain ⟨v, hv, hvy⟩ := hD hy.2
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
  have hveq : Subgroup.inclusion hEN y = v := Subtype.ext hvy.symm
  rw [hveq]
  exact hv

theorem exists_family_of_hom [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x)
    (hn : 2 ≤ n) {η : G} (hη : η ∈ Subgroup.normalizer (modelBase S e : Set G))
    (hord : orderOf ((modelBase S e).normalizerMonoidHom ⟨η, hη⟩) = 3)
    (μ : ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)) →* ℂˣ)
    (hμ : boundaryKernel S e η ≤ μ.ker)
    (χ : ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)) → ℂ)
    (hχ : ∀ y, (μ y : ℂ) = χ y)
    (θt : Subgroup.centralizer ((S : Subgroup G) : Set G) → ℂ)
    (hθt : ∀ (c : Subgroup.centralizer ((S : Subgroup G) : Set G)) (z : G)
      (y : ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G))),
        z ∈ modelCenter S e → (c : G) = z * y → θt c = χ y) :
    ∃ ψ, CompatibleCentralizerFamily 2 (S : Subgroup G) θt ψ := by
  set J := wreathModelHom S e (Original.x (2 ^ n))
  set J₁ := wreathModelHom S e (Original.x2 (2 ^ n))
  have hEN : ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)) ≤
      Subgroup.centralizer {J} := by
    have h := oddCore_sylow_le_centralizer S e
    rwa [x_eq_modelHom] at h
  have hDN : boundaryProduct S e η ≤ Subgroup.centralizer {J} := by
    have h := boundaryProduct_le S e hn hη hord
    rwa [x_eq_modelHom] at h
  have hcomm : commutator (Subgroup.centralizer {J}) ≤
      (boundaryProduct S e η).subgroupOf (Subgroup.centralizer {J}) := by
    intro g hg
    rw [Subgroup.mem_subgroupOf, boundaryProduct_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ hg)
  have : ((boundaryProduct S e η).subgroupOf (Subgroup.centralizer {J})).Normal :=
    normal_of_commutator_le hcomm
  have : IsMulCommutative (Subgroup.centralizer {J} ⧸
      (boundaryProduct S e η).subgroupOf (Subgroup.centralizer {J})) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).mpr hcomm
  let f : ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)) →*
      Subgroup.centralizer {J} ⧸ (boundaryProduct S e η).subgroupOf (Subgroup.centralizer {J}) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hEN)
  have hker : f.ker ≤ μ.ker := by
    intro y hy
    apply hμ
    refine ⟨y.2, ?_⟩
    have hy' := (QuotientGroup.eq_one_iff _).mp hy
    rw [Subgroup.mem_subgroupOf] at hy'
    exact hy'
  obtain ⟨ν, hν⟩ := exists_hom_comp_eq f μ hker
  let ν' : Subgroup.centralizer {J} →* ℂˣ := ν.comp (QuotientGroup.mk' _)
  have hν'D : ∀ v : Subgroup.centralizer {J}, (v : G) ∈ boundaryProduct S e η → ν' v = 1 := by
    intro v hv
    have hq : (QuotientGroup.mk' ((boundaryProduct S e η).subgroupOf
        (Subgroup.centralizer {J}))) v = 1 :=
      (QuotientGroup.eq_one_iff v).mpr ((Subgroup.mem_subgroupOf).mpr hv)
    change ν (QuotientGroup.mk' _ v) = 1
    rw [hq, map_one]
  have hν'E : ∀ y : ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)),
      ν' (Subgroup.inclusion hEN y) = μ y := by
    intro y
    rw [← hν]
    rfl
  have hEodd : Odd (Nat.card (ambientOddCore (Subgroup.centralizer
      ((S : Subgroup G) : Set G)))) := by
    rw [show Nat.card (ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G))) =
      Nat.card (CFSG.oddCore (Subgroup.centralizer
      ((S : Subgroup G) : Set G))) from Subgroup.card_map_of_injective Subtype.coe_injective]
    exact weakClosure_oddCore_card _
  obtain ⟨a, ha⟩ := S.isPGroup'.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (ambientOddCore (Subgroup.centralizer
      ((S : Subgroup G) : Set G)))) (Nat.card (S : Subgroup G)) := by
    rw [ha]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hEodd)
  obtain ⟨k, hk1, hk0⟩ := Nat.chineseRemainder hcop 1 0
  have hEk : ∀ y : ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)),
      y ^ k = y := by
    intro y
    rw [pow_eq_pow_mod k pow_card_eq_one', hk1, ← pow_eq_pow_mod 1 pow_card_eq_one', pow_one]
  have hSk : ∀ y : (S : Subgroup G), y ^ k = 1 := by
    intro y
    obtain ⟨q, hq⟩ := (Nat.modEq_zero_iff_dvd.mp hk0)
    rw [hq, pow_mul, pow_card_eq_one', one_pow]
  let lam : Subgroup.centralizer {J} →* ℂˣ := ν' ^ k
  have hlam_apply : ∀ v : Subgroup.centralizer {J}, lam v = ν' (v ^ k) := by
    intro v
    rw [map_pow]
    rfl
  have hlamD : ∀ v : Subgroup.centralizer {J}, (v : G) ∈ boundaryProduct S e η →
      lam v = 1 := by
    intro v hv
    rw [hlam_apply, map_pow, hν'D v hv, one_pow]
  have h1 : ∀ (v : Subgroup.centralizer {J})
      (y : ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G))),
        (v : G) = y → (lam v : ℂ) = χ y := by
    intro v y hvy
    have hv : v = Subgroup.inclusion hEN y := Subtype.ext hvy
    rw [hlam_apply, hv, ← map_pow, hEk, hν'E, hχ]
  have h2 : ∀ v : Subgroup.centralizer {J}, (v : G) ∈ (S : Subgroup G) → lam v = 1 := by
    intro v hv
    have hvk : v ^ k = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val (hSk ⟨v, hv⟩)
      simpa using this
    rw [hlam_apply, hvk, map_one]
  have hηT : η ∈ Subgroup.normalizer (Subgroup.closure {J, J₁} : Set G) :=
    (eta_properties S e hn hη hord).1
  have hCN : Subgroup.centralizer (Subgroup.closure {J, J₁} : Set G) ≤
      Subgroup.centralizer {J} := LocalConfig.centralizer_le
  have hstr := sylow_and_base_four_group_centralizer_structure n hn S e
  have hprod := hstr.base_set_product
  rw [modelT_eq_closure S e (by omega)] at hprod
  have h3 : ∀ c c' : Subgroup.centralizer {J},
      (c : G) ∈ Subgroup.centralizer (Subgroup.closure {J, J₁} : Set G) →
      (c' : G) = η⁻¹ * c * η → lam c' = lam c := by
    intro c c' hc hc'
    have hcset : (c : G) ∈ ((Subgroup.centralizer (Subgroup.closure {J, J₁} : Set G) :
        Subgroup G) : Set G) := hc
    rw [hprod] at hcset
    obtain ⟨c₀, hc₀, u, hu, hcu⟩ := hcset
    have hc₀C : c₀ ∈ Subgroup.centralizer (Subgroup.closure {J, J₁} : Set G) :=
      ambientOddCore_le _ hc₀
    have huS : u ∈ (S : Subgroup G) := modelBase_le_sylow S e hu
    have huN : u ∈ Subgroup.centralizer {J} := sylow_le_centralizer_x S e hn huS
    have hu' : η⁻¹ * u * η ∈ modelBase S e := (Subgroup.mem_normalizer_iff''.mp hη u).mp hu
    have hu'N : η⁻¹ * u * η ∈ Subgroup.centralizer {J} :=
      sylow_le_centralizer_x S e hn (modelBase_le_sylow S e hu')
    have hc₀' : η⁻¹ * c₀ * η ∈ Subgroup.centralizer (Subgroup.closure {J, J₁} : Set G) :=
      LocalConfig.conj_mem_centralizer hηT hc₀C
    have hgen : c₀⁻¹ * (η⁻¹ * c₀ * η) ∈ boundaryProduct S e η := by
      rw [boundaryProduct_eq]
      apply Subgroup.mem_sup_left
      apply Subgroup.subset_closure
      refine ⟨c₀, ?_, rfl⟩
      rw [closure_half_eq S e (by omega)]
      exact hc₀
    have hlamext : ∀ v : Subgroup.centralizer {J}, lam v = extend _ lam v :=
      fun v => (extend_coe v).symm
    rw [hlamext c, hlamext c', hc', ← hcu]
    have hmul : η⁻¹ * (c₀ * u) * η = (η⁻¹ * c₀ * η) * (η⁻¹ * u * η) := by group
    rw [hmul, extend_mul (hCN hc₀') hu'N, extend_mul (hCN hc₀C) huN]
    have hext2 : ∀ y : G, ∀ hy : y ∈ Subgroup.centralizer {J}, y ∈ (S : Subgroup G) →
        extend _ lam y = 1 := by
      intro y hy hyS
      rw [extend_of_mem hy]
      exact h2 ⟨y, hy⟩ hyS
    rw [hext2 _ hu'N (modelBase_le_sylow S e hu'), hext2 _ huN huS, mul_one, mul_one]
    have hsplit : η⁻¹ * c₀ * η = c₀ * (c₀⁻¹ * (η⁻¹ * c₀ * η)) := by group
    rw [hsplit, extend_mul (hCN hc₀C) (hDN hgen), extend_of_mem (hDN hgen),
      hlamD _ hgen, mul_one]
  exact exists_family_of_extension S e hnonab hn hη hord χ h1 h2 h3 θt hθt

end CFSG.Wreathed.CompatibleFamilies
