module

public import CFSG.CharacterTheory.Wreathed.TorusSplitting
public import CFSG.CharacterTheory.Wreathed.OriginalScalarSylowCoverage

public section

open scoped Classical Pointwise

namespace CFSG.Wreathed.ConfinedOddCore

open CFSG.Wreathed.BaseFourCentralizerStructure CFSG.Wreathed.TorusSplitting

variable {G : Type} [Group G]

abbrev fourGroup (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) : Subgroup G :=
  Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
    wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)}

theorem y_eq (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    wreathModelHom S e (Original.x2 (2 ^ n)) =
      wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2) := by
  rw [Original.x2, map_pow]

theorem x_eq_y_mul (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    wreathModelHom S e (Original.x (2 ^ n)) =
      wreathModelHom S e (Original.x2 (2 ^ n)) *
        wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2) := by
  rw [← map_pow, BrauerWong.modelHom_x2_mul_t_half]

theorem orderOf_y (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    orderOf (wreathModelHom S e (Original.x2 (2 ^ n))) = 2 := by
  rw [orderOf_injective _ (wreathModelHom_injective S e)]
  exact (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.2.1

theorem orderOf_x (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    orderOf (wreathModelHom S e (Original.x (2 ^ n))) = 2 := by
  rw [orderOf_injective _ (wreathModelHom_injective S e)]
  exact (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.1

theorem y_mem_involutionCentralizer (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    wreathModelHom S e (Original.x2 (2 ^ n)) ∈ involutionCentralizer n S e :=
  sylow_le_involutionCentralizer n hn S e (BrauerWong.wreathModelHom_mem S e _)

theorem mem_involutionCentralizer_iff (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g : G) :
    g ∈ involutionCentralizer n S e ↔
      g * wreathModelHom S e (Original.x (2 ^ n)) = wreathModelHom S e (Original.x (2 ^ n)) * g :=
  Subgroup.mem_centralizer_singleton_iff

theorem mem_centralizer_four_iff (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g : G) :
    g ∈ Subgroup.centralizer (fourGroup n S e : Set G) ↔
      g ∈ involutionCentralizer n S e ∧
        g * wreathModelHom S e (Original.x2 (2 ^ n)) =
          wreathModelHom S e (Original.x2 (2 ^ n)) * g := by
  set y := wreathModelHom S e (Original.x2 (2 ^ n)) with hy
  set u := wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2) with hu
  have hx : wreathModelHom S e (Original.x (2 ^ n)) = y * u := x_eq_y_mul n S e
  have hcl : (fourGroup n S e : Set G) = (Subgroup.closure {y, u} : Subgroup G) := by
    rw [fourGroup, ← y_eq]
  rw [hcl, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  have hN : g ∈ involutionCentralizer n S e ↔ wreathModelHom S e (Original.x (2 ^ n)) * g =
      g * wreathModelHom S e (Original.x (2 ^ n)) := by
    rw [mem_involutionCentralizer_iff]
    exact eq_comm
  rw [hN, hx]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1.symm⟩
    rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
  · rintro ⟨h1, h2⟩
    refine ⟨h2.symm, ?_⟩
    have hyg : y⁻¹ * g = g * y⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h2, mul_inv_cancel_right]
    calc u * g = y⁻¹ * (y * u * g) := by group
      _ = y⁻¹ * (g * (y * u)) := by rw [h1]
      _ = (y⁻¹ * g) * (y * u) := by group
      _ = (g * y⁻¹) * (y * u) := by rw [hyg]
      _ = g * u := by group

theorem mem_closure_pair_of_involutions {t s : G} (hts : t * s = s * t) (ht2 : t * t = 1)
    (hs2 : s * s = 1) {v : G} (hv : v ∈ Subgroup.closure ({t, s} : Set G)) :
    v = 1 ∨ v = t ∨ v = s ∨ v = t * s := by
  induction hv using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul a b _ _ ha hb =>
    have h1 : t * (t * s) = s := by rw [← mul_assoc, ht2, one_mul]
    have h2 : s * (t * s) = t := by rw [← mul_assoc, ← hts, mul_assoc, hs2, mul_one]
    have h3 : t * s * t = s := by rw [mul_assoc, ← hts, ← mul_assoc, ht2, one_mul]
    have h4 : t * s * s = t := by rw [mul_assoc, hs2, mul_one]
    have h5 : t * s * (t * s) = 1 := by rw [mul_assoc, h2, ht2]
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      simp only [one_mul, mul_one, ht2, hs2, h1, h2, h3, h4, h5, ← hts, true_or, or_true]
  | inv a _ ha =>
    have hinv : ∀ z : G, z * z = 1 → z⁻¹ = z := fun z hz => inv_eq_of_mul_eq_one_left hz
    have h5 : t * s * (t * s) = 1 := by
      rw [mul_assoc, ← mul_assoc s, ← hts, mul_assoc, hs2, mul_one, ht2]
    rcases ha with rfl | rfl | rfl | rfl
    · exact Or.inl inv_one
    · exact Or.inr (Or.inl (hinv _ ht2))
    · exact Or.inr (Or.inr (Or.inl (hinv _ hs2)))
    · exact Or.inr (Or.inr (Or.inr (hinv _ h5)))

theorem x_mul_y (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (hn : 2 ≤ n) :
    wreathModelHom S e (Original.x (2 ^ n)) * wreathModelHom S e (Original.x2 (2 ^ n)) =
      wreathModelHom S e (Original.x2 (2 ^ n)) * wreathModelHom S e (Original.x (2 ^ n)) :=
  ((mem_involutionCentralizer_iff n S e _).mp (y_mem_involutionCentralizer n hn S e)).symm

theorem eq_of_mem_four (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) {v : G}
    (hv : v ∈ fourGroup n S e) :
    v = 1 ∨ v = wreathModelHom S e (Original.x (2 ^ n)) ∨
      v = wreathModelHom S e (Original.x2 (2 ^ n)) ∨
      v = wreathModelHom S e (Original.x2 (2 ^ n)) * wreathModelHom S e (Original.x (2 ^ n)) := by
  set y := wreathModelHom S e (Original.x2 (2 ^ n)) with hy
  set x := wreathModelHom S e (Original.x (2 ^ n)) with hxdef
  set u := wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2) with hu
  have hx : x = y * u := x_eq_y_mul n S e
  have hy2 : y * y = 1 := by
    rw [← sq, ← orderOf_y n hn S e, pow_orderOf_eq_one]
  have hx2 : x * x = 1 := by
    rw [← sq, ← orderOf_x n hn S e, pow_orderOf_eq_one]
  have hxy : x * y = y * x := x_mul_y n S e hn
  have hux : u = y * x := by
    rw [hx, ← mul_assoc, hy2, one_mul]
  have hyu : y * u = u * y := by
    rw [hux]
    calc y * (y * x) = x := by rw [← mul_assoc, hy2, one_mul]
      _ = y * x * y := by rw [mul_assoc, hxy, ← mul_assoc, hy2, one_mul]
  have hu2 : u * u = 1 := by
    rw [hux, show y * x * (y * x) = y * (x * y) * x by group, hxy,
      show y * (y * x) * x = (y * y) * (x * x) by group, hy2, hx2, one_mul]
  have hcl : fourGroup n S e = Subgroup.closure {y, u} := by
    rw [fourGroup, ← y_eq]
  rw [hcl] at hv
  rcases mem_closure_pair_of_involutions hyu hy2 hu2 hv with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · right; right; right
    rw [h, hux]
  · right; left
    rw [h, hx]

theorem centralizer_singleton_le_normalizer_zpowers (r : G) :
    Subgroup.centralizer {r} ≤ Subgroup.normalizer (Subgroup.zpowers r : Set G) := by
  intro g hg
  have hgr : Commute g r := Subgroup.mem_centralizer_singleton_iff.mp hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨k, rfl⟩
    have h1 : g * r ^ k * g⁻¹ = r ^ k := by rw [(hgr.zpow_right k).eq, mul_inv_cancel_right]
    rw [h1]
    exact ⟨k, rfl⟩
  · rintro ⟨k, hk⟩
    have h1 : h = r ^ k := by
      calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
        _ = g⁻¹ * r ^ k * g := by rw [← hk]
        _ = r ^ k := by
          rw [mul_assoc, ← (hgr.zpow_right k).eq, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h1]
    exact ⟨k, rfl⟩

theorem exists_inverted_cycling_element [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    ∃ a ∈ Subgroup.normalizer (fourGroup n S e : Set G), Odd (orderOf a) ∧
      (wreathModelHom S e (Original.z (2 ^ n)))⁻¹ * a * wreathModelHom S e (Original.z (2 ^ n)) =
        a⁻¹ ∧ ∀ v ∈ fourGroup n S e, v ≠ 1 → a * v * a⁻¹ ≠ v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstruct := sylow_and_base_four_group_centralizer_structure n hn S e
  have hT : modelT n S e = fourGroup n S e := hstruct.four_coordinates
  have hNT_C₀ : ∀ g ∈ Subgroup.normalizer (fourGroup n S e : Set G), ∀ k ∈ torusCore n S e,
      g * k * g⁻¹ ∈ torusCore n S e :=
    fun g hg k hk => ambientOddCore_conj_mem _ (normalizer_le_normalizer_centralizer _ hg) hk
  have hKodd : Odd (Nat.card (torusCore n S e)) := by
    have h := hstruct.oddCore_odd
    rw [hT] at h
    exact h
  have hV4 : IsKleinFour (fourGroup n S e) := by
    have h := hstruct.kleinFour
    rw [hT] at h
    exact h
  have hCV : Subgroup.centralizer (fourGroup n S e : Set G) =
      torusCore n S e ⊔ modelBase S e := by
    have h := hstruct.base_split
    rw [hT] at h
    exact h
  have hUeq : modelBase S e = Subgroup.zpowers (wreathModelHom S e (Original.s (2 ^ n))) ⊔
      Subgroup.zpowers (wreathModelHom S e (Original.t (2 ^ n))) :=
    hstruct.base_coordinates.trans (closure_pair_eq_sup _ _)
  obtain ⟨b, -, a, haM, haord, hacyc, -, hwa, -⟩ := cycling_lift_in_normalizer n hn (2 ^ n) rfl _ _
    (actual_orderOf_s S e) (actual_orderOf_t S e) (actual_s_t_commute S e) (zpowers_disjoint S e)
    (modelBase S e) (fourGroup n S e) (torusCore n S e) hUeq rfl hV4 hNT_C₀ hKodd hCV
    (card_four_normalizer_quotient hnonab hn S e) _ (swap_mem_normalizer_four S e)
    (actual_orderOf_swap S e) (actual_swap_conj_s S e) (actual_swap_conj_t S e)
  refine ⟨a, haM, ?_, hwa, hacyc⟩
  rw [haord]
  exact Odd.pow (by decide)

theorem model_isConj_of_involution [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (F : Type) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
    (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
    (ρ : centralizerFullQuotient n hn S e →*
      ComponentClassification.CatalogueSchreierLinearTwo.coordinateE F)
    (Ψ : CyclicCentralSL2Extension.SemilinearExtension F b (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) Sigma hSigma ≃* centralizerOddCoreQuotient n S e)
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    (v : involutionCentralizer n S e) (hv : orderOf v = 2) (hvx : v ≠ centralInvolution n S e) :
    IsConj (SemidirectProduct.inl ((CyclicCentralSL2Extension.cyclicGenerator F b (2 ^ n)
        (wreathModulus_pos n) (wreathModulus_even hn) ^ 2) ^ (2 ^ n / 4) *
          CyclicCentralSL2Extension.specialInclusion F b (2 ^ n) (wreathModulus_pos n)
            (wreathModulus_even hn) (CentralSL2Abelianization.weyl F)))
      (Ψ.symm (centralizerOddCoreMap n S e v)) := by
  let : Fintype F := Fintype.ofFinite F
  have h4 : 4 ∣ 2 ^ n := by
    have : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [this]
    exact Nat.pow_dvd_pow 2 hn
  obtain ⟨-, -, -, -, hinv, hxcent, -⟩ :=
    CentralSL2.semilinear_involution_classes_and_augmentation_values hp
      (hp.odd_of_ne_two hpodd) hf hdata.card b hdata.nonsquare (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) h4 Sigma hSigma hdata.sigma_odd
  have hπv := OriginalScalarSylowCoverage.original_involution_image_order n S e v hv
  have hnc := OriginalScalarSylowCoverage.original_second_involution_noncentral n hn S e v hv hvx
  have hord : orderOf (Ψ.symm (centralizerOddCoreMap n S e v)) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hπv
  rcases (hinv _).mp hord with h | h
  · exfalso
    apply hnc
    rw [Subgroup.mem_center_iff]
    intro z
    have hz := (hxcent (Ψ.symm z * Ψ.symm (centralizerOddCoreMap n S e v) * (Ψ.symm z)⁻¹)).mp
      (by rw [h]; exact isConj_iff.mpr ⟨Ψ.symm z, rfl⟩)
    rw [← h] at hz
    have hz' := congrArg Ψ hz
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply] at hz'
    calc z * centralizerOddCoreMap n S e v =
        z * centralizerOddCoreMap n S e v * z⁻¹ * z := by group
      _ = centralizerOddCoreMap n S e v * z := by rw [hz']
  · exact h

theorem involution_isConj_y [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (F : Type) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
    (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
    (ρ : centralizerFullQuotient n hn S e →*
      ComponentClassification.CatalogueSchreierLinearTwo.coordinateE F)
    (Ψ : CyclicCentralSL2Extension.SemilinearExtension F b (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) Sigma hSigma ≃* centralizerOddCoreQuotient n S e)
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    (g : involutionCentralizer n S e) (hg : orderOf g = 2) (hgx : g ≠ centralInvolution n S e) :
    ∃ k : involutionCentralizer n S e,
      k * ⟨wreathModelHom S e (Original.x2 (2 ^ n)), y_mem_involutionCentralizer n hn S e⟩ * k⁻¹ =
        g := by
  set yN : involutionCentralizer n S e :=
    ⟨wreathModelHom S e (Original.x2 (2 ^ n)), y_mem_involutionCentralizer n hn S e⟩ with hyN
  have hyN2 : orderOf yN = 2 := by
    rw [hyN, Subgroup.orderOf_mk]
    exact orderOf_y n hn S e
  have hyNx : yN ≠ centralInvolution n S e := by
    intro h
    exact BrauerWong.modelHom_x_ne_x2 S e (by omega) (congrArg Subtype.val h).symm
  have hconj := model_isConj_of_involution n hn S e p f hp hpodd hf F Sigma b hSigma ρ Ψ hdata
  have hc := ((hconj yN hyN2 hyNx).symm.trans (hconj g hg hgx))
  have hc' := (Ψ.toMonoidHom.map_isConj hc)
  simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at hc'
  have hNc := (OddNormalQuotientInvolutions.quotient_involutions_isConj_iff
    (centralizerOddCore n S e) (centralizerOddCore_card_odd n S e) hyN2 hg).mp hc'
  obtain ⟨k, hk⟩ := isConj_iff.mp hNc
  exact ⟨k, hk⟩

end CFSG.Wreathed.ConfinedOddCore
