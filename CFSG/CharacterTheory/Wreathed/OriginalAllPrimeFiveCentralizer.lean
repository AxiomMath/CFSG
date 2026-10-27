module

public import CFSG.CharacterTheory.Wreathed.NormalComponentLiftModel
public import CFSG.CharacterTheory.Wreathed.OriginalScalarSylowCoverage

public section

namespace CFSG.Wreathed.OriginalAllPrime.Five

open CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2
  CFSG.Wreathed.OddNormalQuotientInvolutions CFSG.Wreathed.InvolutionInducedCharacters
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem eq_five_and_eq_one_of_pow_eq_five {p f : ℕ} (hq5 : p ^ f = 5) : p = 5 ∧ f = 1 :=
  Nat.prime_five.pow_eq_iff.mp hq5

variable {G : Type} [Group G] [Finite G]

theorem wreath_exponent_eq_two
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {n : ℕ} {hn : 2 ≤ n} {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)}
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (hmodel : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 5 1) : n = 2 := by
  have h := NormalComponentLift.two_pow_eq_two_part hnonab hfour Nat.prime_five (by norm_num)
    le_rfl hmodel
  have h4 : (((5 ^ 1 : ℕ) : ℤ) - if 5 ^ 1 % 4 = 1 then (1 : ℤ) else -1) = ((2 ^ 2 : ℕ) : ℤ) := by
    norm_num
  rw [h4, padicValInt.of_nat, padicValNat.prime_pow] at h
  exact Nat.pow_right_injective le_rfl h

theorem compatible_model_central_involution {n : ℕ} {hn : 2 ≤ n} {S : Sylow 2 G}
    {e : S ≃* Wreath (2 ^ n)} {p f : ℕ} {F : Type} [Field F] [Finite F]
    {Sigma : Subgroup (F ≃+* F)} {b : Fˣ} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}
    {ρ : centralizerFullQuotient n hn S e →* coordinateE F}
    {Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma ≃* centralizerOddCoreQuotient n S e}
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) :
    Ψ (SemidirectProduct.inl (cyclicGenerator F b (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) ^ (2 ^ n))) =
      centralizerOddCoreMap n S e (centralInvolution n S e) := by
  set x₀ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
    hSigma := SemidirectProduct.inl (cyclicGenerator F b (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) ^ (2 ^ n))
  have horder : orderOf (Ψ x₀) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_inl_cyclicGenerator_pow_m F b (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) Sigma hSigma (two_ne_zero_of_not_isSquare hdata.nonsquare)
  have hcenter : Ψ x₀ ∈ Subgroup.center (centralizerOddCoreQuotient n S e) := by
    refine Subgroup.mem_center_iff.mpr fun h => ?_
    obtain ⟨g, rfl⟩ := Ψ.surjective h
    rw [← map_mul, ← map_mul]
    exact congrArg Ψ (inl_cyclicGenerator_pow_m_comm g)
  exact OriginalScalarSylowCoverage.original_quotient_center_unique_involution
    n hn S e (Ψ x₀) horder hcenter

theorem card_centralizer_image_involution_eq_sixteen
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (hmodel : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 5 1)
    (t : involutionCentralizer n S e) (ht : orderOf t = 2)
    (htx : t ≠ centralInvolution n S e) :
    Nat.card (Subgroup.centralizer {centralizerOddCoreMap n S e t}) = 16 := by
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨F, hF, hfinite, Sigma, b, hSigma, ρ, Ψ, hdata⟩ :=
    exists_conditionalCompatibleModelData hnonab n hn S e hfour 5 1 Nat.prime_five
      (by norm_num) le_rfl hmodel
  let : Field F := hF
  let : Finite F := hfinite
  let : Fintype F := Fintype.ofFinite F
  set R := centralizerOddCore n S e
  have hR : Odd (Nat.card R) := centralizerOddCore_card_odd n S e
  obtain ⟨⟨y, hy2, hyΨ⟩, hII⟩ :=
    actual_centralizer_involution_induced_characters_and_principal_order_identity
      hnonab n hn S e R hR Nat.prime_five (by decide) le_rfl hdata.card b hdata.nonsquare Sigma
      hSigma hdata.sigma_odd Ψ (compatible_model_central_involution hdata)
  obtain ⟨⟨hclasses, -, -, hcent, -, -⟩, -, -⟩ := hII y hy2 hyΨ
  have hq : Nat.card F = 5 := by rw [hdata.card, pow_one]
  have hd : Nat.card Sigma = 1 := Nat.dvd_one.mp hdata.sigma_dvd
  have hm : (2 : ℕ) ^ n = 4 := by rw [wreath_exponent_eq_two hnonab hfour hmodel]; norm_num
  rw [hq, hd, hm] at hcent
  have hy : Nat.card (Subgroup.centralizer {y}) = Nat.card (kernelCentralizer R y) * 16 := by
    have h : (Nat.card (Subgroup.centralizer {y}) : ℤ) = Nat.card (kernelCentralizer R y) * 16 := by
      rw [hcent]
      norm_num
      ring
    exact_mod_cast h
  rw [((odd_normal_quotient_involution_classes_and_centralizers R hR).2.2 _ y hy2
    rfl).2.2.1] at hy
  have hyt : IsConj y t := ((hclasses t).mp ht).resolve_left htx
  rw [← Nat.eq_of_mul_eq_mul_left Nat.card_pos hy]
  exact (card_centralizer_of_isConj (MonoidHom.map_isConj (QuotientGroup.mk' R) hyt)).symm

theorem mem_centralizerOddCore_of_odd_of_mem_centralizer
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (hmodel : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 5 1)
    (t : involutionCentralizer n S e) (ht : orderOf t = 2)
    (htx : t ≠ centralInvolution n S e) {c : involutionCentralizer n S e}
    (hc : c ∈ Subgroup.centralizer {t}) (hodd : Odd (orderOf c)) :
    c ∈ centralizerOddCore n S e := by
  set π := centralizerOddCoreMap n S e
  have hπc : π c ∈ Subgroup.centralizer {π t} := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    rw [← map_mul, ← map_mul, hc]
  have h16 : orderOf (π c) ∣ 2 ^ 4 := by
    have h := Subgroup.orderOf_dvd_natCard _ hπc
    rwa [card_centralizer_image_involution_eq_sixteen hnonab n hn S e hfour hmodel t ht htx] at h
  have hcop : Nat.Coprime (orderOf (π c)) (2 ^ 4) :=
    (Nat.coprime_two_right.mpr (hodd.of_dvd_nat (orderOf_map_dvd π c))).pow_right 4
  exact (QuotientGroup.eq_one_iff c).mp
    (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop h16))

end CFSG.Wreathed.OriginalAllPrime.Five
