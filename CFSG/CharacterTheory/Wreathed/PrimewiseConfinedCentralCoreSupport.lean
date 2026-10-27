module

public import CFSG.CharacterTheory.Wreathed.PrimewiseLayerFieldEliminationSupport
public import CFSG.CharacterTheory.Wreathed.ConfinedOddCoreStructure

public section

open scoped Classical Pointwise commutatorElement

namespace CFSG.Wreathed.ConfinedOddCore

open CFSG.Wreathed.BaseFourCentralizerStructure CFSG.Wreathed.TorusSplitting
  CFSG.Wreathed.CyclicCentralSL2Extension

variable {G : Type} [Group G]

theorem torusCore_le_oddCore_of_nine [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (h9 : p ^ f = 9) (F : Type) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
    (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
    (ρ : centralizerFullQuotient n hn S e →*
      ComponentClassification.CatalogueSchreierLinearTwo.coordinateE F)
    (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma ≃* centralizerOddCoreQuotient n S e)
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) :
    torusCore n S e ≤ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype := by
  let : Fintype F := Fintype.ofFinite F
  have hd1 : Nat.card Sigma = 1 :=
    PrimewiseLayerFieldElimination.sigma_card_eq_one_of_nine n hn S e p f hp h9 F Sigma b
      hSigma ρ Ψ hdata
  have h4 : 4 ∣ 2 ^ n := by
    have : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [this]
    exact Nat.pow_dvd_pow 2 hn
  obtain ⟨-, -, -, -, -, -, -, -, hcardC, -⟩ :=
    CentralSL2.semilinear_involution_classes_and_augmentation_values hp
      (hp.odd_of_ne_two hpodd) hf hdata.card b hdata.nonsquare (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) h4 Sigma hSigma hdata.sigma_odd
  set Y0 : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma := SemidirectProduct.inl ((cyclicGenerator F b (2 ^ n) (wreathModulus_pos n)
        (wreathModulus_even hn) ^ 2) ^ (2 ^ n / 4) * specialInclusion F b (2 ^ n)
          (wreathModulus_pos n) (wreathModulus_even hn) (CentralSL2Abelianization.weyl F))
    with hY0
  have hFcard : Nat.card F = 9 := hdata.card.trans h9
  have hcardC' : Nat.card (Subgroup.centralizer {Y0}) = 2 ^ (n + 3) := by
    rw [hFcard, hd1] at hcardC
    have h1 : (Nat.card (Subgroup.centralizer {Y0}) : ℤ) = ((2 ^ (n + 3) : ℕ) : ℤ) := by
      rw [hcardC]
      push_cast
      norm_num
      ring
    exact_mod_cast h1
  set yN : involutionCentralizer n S e :=
    ⟨wreathModelHom S e (Original.x2 (2 ^ n)), y_mem_involutionCentralizer n hn S e⟩ with hyN
  have hyN2 : orderOf yN = 2 := by
    rw [hyN, Subgroup.orderOf_mk]
    exact orderOf_y n hn S e
  have hyNx : yN ≠ centralInvolution n S e := by
    intro h
    exact BrauerWong.modelHom_x_ne_x2 S e (by omega) (congrArg Subtype.val h).symm
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (model_isConj_of_involution n hn S e p f hp hpodd hf F Sigma b hSigma ρ Ψ hdata yN hyN2 hyNx)
  intro k hk
  have hkC : k ∈ Subgroup.centralizer (fourGroup n S e : Set G) := ambientOddCore_le _ hk
  obtain ⟨hkN, hky⟩ := (mem_centralizer_four_iff n S e k).mp hkC
  set kN : involutionCentralizer n S e := ⟨k, hkN⟩ with hkNdef
  have hkodd : Odd (orderOf k) := by
    have hstruct := sylow_and_base_four_group_centralizer_structure n hn S e
    have hodd := hstruct.oddCore_odd
    rw [hstruct.four_coordinates] at hodd
    exact odd_orderOf_of_mem hodd hk
  have hcomm : Ψ.symm (centralizerOddCoreMap n S e kN) *
      Ψ.symm (centralizerOddCoreMap n S e yN) =
        Ψ.symm (centralizerOddCoreMap n S e yN) * Ψ.symm (centralizerOddCoreMap n S e kN) := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    exact Subtype.ext hky
  rw [← hc] at hcomm
  set k' := c⁻¹ * Ψ.symm (centralizerOddCoreMap n S e kN) * c with hk'
  have hk'C : k' ∈ Subgroup.centralizer {Y0} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc k' * Y0 = c⁻¹ * (Ψ.symm (centralizerOddCoreMap n S e kN) * (c * Y0 * c⁻¹)) * c := by
          rw [hk']; group
      _ = c⁻¹ * ((c * Y0 * c⁻¹) * Ψ.symm (centralizerOddCoreMap n S e kN)) * c := by rw [hcomm]
      _ = Y0 * k' := by rw [hk']; group
  have hd2 : orderOf k' ∣ 2 ^ (n + 3) := by
    rw [← hcardC', ← Subgroup.orderOf_mk k' hk'C]
    exact orderOf_dvd_natCard _
  have hord : orderOf k' = orderOf (centralizerOddCoreMap n S e kN) := by
    rw [hk', show c⁻¹ * Ψ.symm (centralizerOddCoreMap n S e kN) * c =
      MulAut.conj c⁻¹ (Ψ.symm (centralizerOddCoreMap n S e kN)) by
        rw [MulAut.conj_apply, inv_inv], MulEquiv.orderOf_eq, MulEquiv.orderOf_eq]
  have hd3 : orderOf k' ∣ orderOf k := by
    rw [hord, ← Subgroup.orderOf_mk k hkN]
    exact orderOf_map_dvd _ _
  have hcop : Nat.Coprime (orderOf k') (2 ^ (n + 3)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr (hkodd.of_dvd_nat hd3))
  have h1 : orderOf (centralizerOddCoreMap n S e kN) = 1 := by
    rw [← hord]
    exact Nat.Coprime.eq_one_of_dvd hcop hd2
  have h2 : kN ∈ centralizerOddCore n S e :=
    (QuotientGroup.eq_one_iff (N := centralizerOddCore n S e) kN).mp (orderOf_eq_one_iff.mp h1)
  exact ⟨kN, h2, rfl⟩

theorem swap_centralizes_fixed_core
    [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (J : Subgroup (involutionCentralizer n S e)) (hJR : ⁅J, centralizerOddCore n S e⁆ = ⊥)
    (hY : (((CFSG.layer (centralizerOddCoreQuotient n S e)).comap (centralizerOddCoreMap n S e) :
      Subgroup (involutionCentralizer n S e)) : Set (involutionCentralizer n S e)) =
        (J : Set (involutionCentralizer n S e)) * (centralizerOddCore n S e : Set _))
    (hER : (J ⊓ centralizerOddCore n S e).subgroupOf (centralizerOddCore n S e) ≤
      Subgroup.center (centralizerOddCore n S e)) :
    ∀ z ∈ torusFixedCore n S e, wreathModelHom S e (Original.z (2 ^ n)) * z =
      z * wreathModelHom S e (Original.z (2 ^ n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := centralizerOddCore n S e with hRdef
  have hJcent : J ≤ Subgroup.centralizer (R : Set (involutionCentralizer n S e)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJR
  set d : involutionCentralizer n S e :=
    wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
      (Original.d (2 ^ n)) with hd
  have hdG : (d : G) = wreathModelHom S e (Original.x2 (2 ^ n)) *
      wreathModelHom S e (Original.z (2 ^ n)) := by
    rw [hd, centralizerModelHom_coe, Original.d, map_mul]
  have hdM : d ∈ (CFSG.layer (centralizerOddCoreQuotient n S e)).comap
      (centralizerOddCoreMap n S e) := by
    have h1 : wreathModelHom (centralizerOddCoreSylow n hn S e)
        (centralizerOddCoreCoordinates n hn S e) (Original.d (2 ^ n)) ∈
          modelY (centralizerOddCoreSylow n hn S e) (centralizerOddCoreCoordinates n hn S e) :=
      Subgroup.mem_map_of_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    rw [← ActualCentralizerSemilinear.actual_quotient_sylow_inter_layer hnonab n hn S e hfour,
      ActualCentralizerSemilinear.actual_quotient_wreath_value] at h1
    exact h1.2
  have hd' : d ∈ ((((CFSG.layer (centralizerOddCoreQuotient n S e)).comap
      (centralizerOddCoreMap n S e) : Subgroup (involutionCentralizer n S e)) :
        Set (involutionCentralizer n S e))) := hdM
  rw [hY] at hd'
  obtain ⟨j, hj, r, hr, hjr⟩ := Set.mem_mul.mp hd'
  have hjrc : Commute j r := (Subgroup.mem_centralizer_iff.mp (hJcent hj) r hr).symm
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨(d : G), by
    rw [hdG]
    exact (S : Subgroup G).mul_mem (BrauerWong.wreathModelHom_mem S e _)
      (BrauerWong.wreathModelHom_mem S e _)⟩
  have hk' : d ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  have hpow : j ^ 2 ^ k * r ^ 2 ^ k = 1 := by rw [← hjrc.mul_pow, hjr, hk']
  have hrE : r ^ 2 ^ k ∈ J ⊓ R := by
    refine ⟨?_, R.pow_mem hr _⟩
    rw [eq_inv_of_mul_eq_one_right hpow]
    exact J.inv_mem (J.pow_mem hj _)
  have hrcomm : ∀ r₀ ∈ R, r * r₀ = r₀ * r := by
    intro r₀ hr₀
    have h1 : (⟨r ^ 2 ^ k, R.pow_mem hr _⟩ : R) ∈ Subgroup.center R := hER hrE
    have h2 : Commute (r ^ 2 ^ k) r₀ :=
      (congrArg Subtype.val ((Subgroup.mem_center_iff.mp h1) ⟨r₀, hr₀⟩)).symm
    have hodd := odd_orderOf_of_mem (centralizerOddCore_card_odd n S e) hr
    obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd) : Nat.Coprime (2 ^ k) (orderOf r))
    rw [← hu]
    exact (h2.pow_left u).eq
  intro z hz
  have hzR : z ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype := hz.1
  obtain ⟨zN, hzN, rfl⟩ := hzR
  have hdz : d * zN = zN * d := by
    rw [← hjr]
    calc j * r * zN = j * (zN * r) := by rw [mul_assoc, hrcomm zN hzN]
      _ = (j * zN) * r := by group
      _ = (zN * j) * r := by rw [(Subgroup.mem_centralizer_iff.mp (hJcent hj) zN hzN).symm]
      _ = zN * (j * r) := by group
  have hdz' : (d : G) * zN = zN * d := congrArg Subtype.val hdz
  rw [hdG] at hdz'
  have hyz : (zN : G) * wreathModelHom S e (Original.x2 (2 ^ n)) =
      wreathModelHom S e (Original.x2 (2 ^ n)) * zN :=
    ((mem_centralizer_four_iff n S e _).mp hz.2).2
  set y := wreathModelHom S e (Original.x2 (2 ^ n)) with hy
  set w := wreathModelHom S e (Original.z (2 ^ n)) with hw
  change w * (zN : G) = zN * w
  calc w * (zN : G) = y⁻¹ * ((y * w) * zN) := by group
    _ = y⁻¹ * (zN * (y * w)) := by rw [hdz']
    _ = (y⁻¹ * zN) * (y * w) := by group
    _ = (zN * y⁻¹) * (y * w) := by
        rw [show y⁻¹ * (zN : G) = zN * y⁻¹ by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hyz, mul_inv_cancel_right]]
    _ = zN * w := by group

theorem three_dvd_sq_sub_one {k : ℤ} (h : ¬ (3 : ℤ) ∣ k) : (3 : ℤ) ∣ k ^ 2 - 1 := by
  have h1 : k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h1 with h1 | h1
  · have h2 : (k ^ 2 - 1) % 3 = 0 := by
      rw [Int.sub_emod, pow_two, Int.mul_emod, h1]
      norm_num
    omega
  · have h2 : (k ^ 2 - 1) % 3 = 0 := by
      rw [Int.sub_emod, pow_two, Int.mul_emod, h1]
      norm_num
    omega

theorem lift_inter_oddCore_eq_bot_of_nine
    [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : ActualProjectiveLayer.PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    (h9 : p ^ f = 9)
    (hconf : ∀ r ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype, r ≠ 1 →
      Subgroup.normalizer (Subgroup.zpowers r : Set G) ≤ involutionCentralizer n S e)
    (J : Subgroup (involutionCentralizer n S e)) [J.Normal]
    (hJR : ⁅J, centralizerOddCore n S e⁆ = ⊥)
    (hY : (((CFSG.layer (centralizerOddCoreQuotient n S e)).comap (centralizerOddCoreMap n S e) :
      Subgroup (involutionCentralizer n S e)) : Set (involutionCentralizer n S e)) =
        (J : Set (involutionCentralizer n S e)) * (centralizerOddCore n S e : Set _))
    (hER : (J ⊓ centralizerOddCore n S e).subgroupOf (centralizerOddCore n S e) ≤
      Subgroup.center (centralizerOddCore n S e))
    (hE : Nat.card ↥(J ⊓ centralizerOddCore n S e) = 1 ∨
      Nat.card ↥(J ⊓ centralizerOddCore n S e) = 3) :
    J ⊓ centralizerOddCore n S e = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F, hF, hFfin, Sigma, b, hSigma, ρ, Ψ, hdata⟩ :=
    exists_conditionalCompatibleModelData hnonab n hn S e hfour p f hp hpodd hf hmodel
  let : Field F := hF
  let : Finite F := hFfin
  set A₀ := torusFixedCore n S e with hA₀def
  have hC₀R := torusCore_le_oddCore_of_nine n hn S e p f hp hpodd hf h9 F Sigma b hSigma ρ Ψ hdata
  have hwA := swap_centralizes_fixed_core hnonab n hn S e hfour J hJR hY hER
  obtain ⟨a, haT, haodd, hwa, hacyc⟩ := exists_inverted_cycling_element hnonab n hn S e
  have hx1 : wreathModelHom S e (Original.x (2 ^ n)) ≠ 1 := by
    intro h
    have h1 := orderOf_x n hn S e
    rw [h, orderOf_one] at h1
    omega
  have haN : a ∉ involutionCentralizer n S e := by
    intro haN
    apply hacyc _ (x_mem_four n S e) hx1
    have h1 := (mem_involutionCentralizer_iff n S e a).mp haN
    rw [h1, mul_inv_cancel_right]
  have hA₀bot : ∀ u ∈ A₀, u = 1 := by
    intro u hu
    have hau : a * u * a⁻¹ ∈ torusCore n S e :=
      ambientOddCore_conj_mem _ (normalizer_le_normalizer_centralizer _ haT)
        (torusFixedCore_le_torusCore n S e hu)
    exact fixed_core_malnormal n S e hconf hwA haodd hwa haN hu ⟨hC₀R hau, ambientOddCore_le _ hau⟩
  set E := J ⊓ centralizerOddCore n S e with hEdef
  rcases hE with hE1 | hE3
  · exact Subgroup.card_eq_one.mp hE1
  exfalso
  have hEne : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE3
    omega
  obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEne
  have hg1' : g ≠ 1 := fun h => hg1 (Subtype.ext h)
  have hgord : orderOf g = 3 := by
    have h1 : orderOf (⟨g, hg⟩ : E) ∣ 3 := hE3 ▸ orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hg1'
    · exact h
  have hEg : E = Subgroup.zpowers g := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg)
    rw [hE3, Nat.card_zpowers, hgord]
  have hEnormal : E.Normal := Subgroup.normal_inf_normal J (centralizerOddCore n S e)
  set sN : involutionCentralizer n S e :=
    wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
      (Original.s (2 ^ n)) with hsN
  have hsg : sN * g * sN⁻¹ ∈ Subgroup.zpowers g := hEg ▸ hEnormal.conj_mem g hg sN
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsg
  have hk3 : ¬ (3 : ℤ) ∣ k := by
    intro h3
    have h1 : g ^ k = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hgord]
      exact_mod_cast h3
    rw [h1] at hk
    apply hg1'
    have h2 : sN * g * sN⁻¹ = 1 := hk.symm
    calc g = sN⁻¹ * (sN * g * sN⁻¹) * sN := by group
      _ = 1 := by rw [h2]; group
  have hs2 : sN ^ 2 * g * (sN ^ 2)⁻¹ = g := by
    have h1 : sN ^ 2 * g * (sN ^ 2)⁻¹ = (sN * g * sN⁻¹) ^ k := by
      rw [sq, show sN * sN * g * (sN * sN)⁻¹ = sN * (sN * g * sN⁻¹) * sN⁻¹ by group, ← hk,
        ← conj_zpow, hk]
    rw [h1, ← hk, ← zpow_mul]
    have h2 : (3 : ℤ) ∣ k * k - 1 := by
      have := three_dvd_sq_sub_one hk3
      rwa [sq] at this
    obtain ⟨c, hc⟩ := h2
    rw [show k * k = 3 * c + 1 by omega, zpow_add, zpow_mul,
      show g ^ (3 : ℤ) = 1 by rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast,
        ← hgord, pow_orderOf_eq_one], one_zpow, one_mul, zpow_one]
  have hyN : (⟨wreathModelHom S e (Original.x2 (2 ^ n)), y_mem_involutionCentralizer n hn S e⟩ :
      involutionCentralizer n S e) = (sN ^ 2) ^ (2 ^ (n - 2)) := by
    apply Subtype.ext
    show wreathModelHom S e (Original.x2 (2 ^ n)) =
      (((sN ^ 2) ^ (2 ^ (n - 2)) : involutionCentralizer n S e) : G)
    rw [SubgroupClass.coe_pow, SubgroupClass.coe_pow, hsN, centralizerModelHom_coe, y_eq, ← pow_mul,
      show 2 * 2 ^ (n - 2) = 2 ^ n / 2 by
        rw [← pow_succ', show n - 2 + 1 = n - 1 by omega, wreathed_two_pow_div_two n (by omega)]]
  have hgy : g * (⟨wreathModelHom S e (Original.x2 (2 ^ n)), y_mem_involutionCentralizer n hn S e⟩ :
      involutionCentralizer n S e) =
        (⟨wreathModelHom S e (Original.x2 (2 ^ n)), y_mem_involutionCentralizer n hn S e⟩ :
          involutionCentralizer n S e) * g := by
    rw [hyN]
    have h1 : Commute (sN ^ 2) g := by
      change sN ^ 2 * g = g * sN ^ 2
      calc sN ^ 2 * g = sN ^ 2 * g * (sN ^ 2)⁻¹ * sN ^ 2 := by group
        _ = g * sN ^ 2 := by rw [hs2]
    exact ((h1.pow_left _).eq).symm
  have hgA : (g : G) ∈ A₀ := by
    refine ⟨⟨g, hg.2, rfl⟩, (mem_centralizer_four_iff n S e _).mpr ⟨g.2, ?_⟩⟩
    exact congrArg Subtype.val hgy
  exact hg1' (Subtype.ext (hA₀bot _ hgA))

end CFSG.Wreathed.ConfinedOddCore
