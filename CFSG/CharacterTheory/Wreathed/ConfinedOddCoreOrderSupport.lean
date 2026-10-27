module

public import CFSG.CharacterTheory.Wreathed.ConfinedOddCoreStructure
public import CFSG.CharacterTheory.Semidihedral.Principal.RegularityInvertedOddFactorSupport
public import CFSG.CharacterTheory.Wreathed.ReducedNoncentralInvolutionTorus

public section

open scoped Classical Pointwise commutatorElement

namespace CFSG.Wreathed.ConfinedOddCore

open CFSG.Wreathed.BaseFourCentralizerStructure CFSG.Wreathed.TorusSplitting
  CFSG.Wreathed.CyclicCentralSL2Extension

theorem model_y0_not_mem_center {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hpodd : p ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f) (b : Fˣ) (hb : ¬ IsSquare b)
    (m : ℕ) (hm : 0 < m) (heven : Even m) (h4 : 4 ∣ m) (Sigma : Subgroup (F ≃+* F))
    (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b) (hd : Odd (Nat.card Sigma)) :
    (SemidirectProduct.inl ((cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) *
      specialInclusion F b m hm heven (CentralSL2Abelianization.weyl F)) :
        SemilinearExtension F b m hm heven Sigma hSigma) ∉
      Subgroup.center (SemilinearExtension F b m hm heven Sigma hSigma) := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨-, -, -, -, -, -, -, hcardH, hcardC, -⟩ :=
    CentralSL2.semilinear_involution_classes_and_augmentation_values hp
      (hp.odd_of_ne_two hpodd) hf hcard b hb m hm heven h4 Sigma hSigma hd
  intro hcen
  have htop : Subgroup.centralizer {(SemidirectProduct.inl ((cyclicGenerator F b m hm heven ^ 2) ^
      (m / 4) * specialInclusion F b m hm heven (CentralSL2Abelianization.weyl F)) :
        SemilinearExtension F b m hm heven Sigma hSigma)} = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro g
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_center_iff.mp hcen) g)
  rw [htop, Subgroup.card_top, hcardH] at hcardC
  have hq3 : 3 ≤ Nat.card F := by
    rw [hcard]
    exact ConditionalGlobalDegrees.three_le_prime_pow hp hpodd hf
  have hd0 : 0 < Nat.card Sigma := Nat.card_pos
  set q := Nat.card F with hq
  set d := Nat.card Sigma with hdd
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  push_cast [Nat.cast_sub hq2] at hcardC
  have hmd : (0 : ℤ) < m * d := by positivity
  have hq3' : (3 : ℤ) ≤ q := by exact_mod_cast hq3
  have h1 : (q : ℤ) * ((q : ℤ) ^ 2 - 1) = (q : ℤ) - (if q % 4 = 1 then 1 else -1) := by
    have h2 : (m : ℤ) * d * (q * (q ^ 2 - 1)) = m * d * (q - if q % 4 = 1 then 1 else -1) := by
      rw [← hcardC]
      ring
    exact mul_left_cancel₀ hmd.ne' h2
  rcases (show (if q % 4 = 1 then (1 : ℤ) else -1) = 1 ∨
      (if q % 4 = 1 then (1 : ℤ) else -1) = -1 by split_ifs <;> simp) with h | h <;>
    rw [h] at h1 <;> nlinarith

theorem model_centralizer_comm {F : Type} [Field F] [Finite F] {b : Fˣ} (hb : ¬ IsSquare b)
    {m : ℕ} {hm : 0 < m} {heven : Even m} {Sigma : Subgroup (F ≃+* F)}
    {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b} (hd : Nat.card Sigma = 1)
    {g g' : SemilinearExtension F b m hm heven Sigma hSigma}
    (hg : g * SemidirectProduct.inl ((cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) *
      specialInclusion F b m hm heven (CentralSL2Abelianization.weyl F)) =
        SemidirectProduct.inl ((cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) *
          specialInclusion F b m hm heven (CentralSL2Abelianization.weyl F)) * g)
    (hg' : g' * SemidirectProduct.inl ((cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) *
      specialInclusion F b m hm heven (CentralSL2Abelianization.weyl F)) =
        SemidirectProduct.inl ((cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) *
          specialInclusion F b m hm heven (CentralSL2Abelianization.weyl F)) * g') :
    g * g' = g' * g := by
  let : Fintype F := Fintype.ofFinite F
  have hsub : Subsingleton Sigma := (Nat.card_eq_one_iff_unique.mp hd).1
  have hinl : ∀ h : SemilinearExtension F b m hm heven Sigma hSigma,
      h = SemidirectProduct.inl h.left := by
    intro h
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right h]
    rw [Subsingleton.elim h.right 1, map_one, mul_one]
  have hcent : ∀ h : SemilinearExtension F b m hm heven Sigma hSigma,
      h * SemidirectProduct.inl (CentralSL2.involutionY F b m hm heven) =
        SemidirectProduct.inl (CentralSL2.involutionY F b m hm heven) * h →
      h.left ∈ Subgroup.centralizer {CentralSL2.involutionY F b m hm heven} := by
    intro h hh
    rw [hinl h, ← map_mul, ← map_mul] at hh
    exact Subgroup.mem_centralizer_singleton_iff.mpr (SemidirectProduct.inl_injective hh)
  have h1 := hcent g hg
  have h2 := hcent g' hg'
  rw [hinl g, hinl g', ← map_mul, ← map_mul,
    ReducedInvolution.centralizer_involutionY_comm hb h1 h2]

theorem reduced_centralizer_comm {G : Type} [Group G] [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2)
    (hf : 1 ≤ f) (F : Type) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
    (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
    (ρ : centralizerFullQuotient n hn S e →*
      ComponentClassification.CatalogueSchreierLinearTwo.coordinateE F)
    (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma ≃* centralizerOddCoreQuotient n S e)
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    (hd : Nat.card Sigma = 1) {α β : centralizerOddCoreQuotient n S e}
    (hα : α * centralizerOddCoreMap n S e
      ⟨wreathModelHom S e (Original.x2 (2 ^ n)), y_mem_involutionCentralizer n hn S e⟩ =
        centralizerOddCoreMap n S e
          ⟨wreathModelHom S e (Original.x2 (2 ^ n)), y_mem_involutionCentralizer n hn S e⟩ * α)
    (hβ : β * centralizerOddCoreMap n S e
      ⟨wreathModelHom S e (Original.x2 (2 ^ n)), y_mem_involutionCentralizer n hn S e⟩ =
        centralizerOddCoreMap n S e
          ⟨wreathModelHom S e (Original.x2 (2 ^ n)), y_mem_involutionCentralizer n hn S e⟩ * β) :
    α * β = β * α := by
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
  set Y0 : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma := SemidirectProduct.inl ((cyclicGenerator F b (2 ^ n) (wreathModulus_pos n)
        (wreathModulus_even hn) ^ 2) ^ (2 ^ n / 4) * specialInclusion F b (2 ^ n)
          (wreathModulus_pos n) (wreathModulus_even hn) (CentralSL2Abelianization.weyl F))
    with hY0
  have hcomm : ∀ γ : centralizerOddCoreQuotient n S e,
      γ * centralizerOddCoreMap n S e yN = centralizerOddCoreMap n S e yN * γ →
      (c⁻¹ * Ψ.symm γ * c) * Y0 = Y0 * (c⁻¹ * Ψ.symm γ * c) := by
    intro γ hγ
    have h1 : Ψ.symm γ * Ψ.symm (centralizerOddCoreMap n S e yN) =
        Ψ.symm (centralizerOddCoreMap n S e yN) * Ψ.symm γ := by
      rw [← map_mul, ← map_mul, hγ]
    rw [← hc] at h1
    calc c⁻¹ * Ψ.symm γ * c * Y0 = c⁻¹ * (Ψ.symm γ * (c * Y0 * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * Y0 * c⁻¹) * Ψ.symm γ) * c := by rw [h1]
      _ = Y0 * (c⁻¹ * Ψ.symm γ * c) := by group
  have h2 := model_centralizer_comm hdata.nonsquare hd (hcomm α hα) (hcomm β hβ)
  have h3 : Ψ.symm α * Ψ.symm β = Ψ.symm β * Ψ.symm α := by
    calc Ψ.symm α * Ψ.symm β = c * ((c⁻¹ * Ψ.symm α * c) * (c⁻¹ * Ψ.symm β * c)) * c⁻¹ := by
          group
      _ = c * ((c⁻¹ * Ψ.symm β * c) * (c⁻¹ * Ψ.symm α * c)) * c⁻¹ := by rw [h2]
      _ = Ψ.symm β * Ψ.symm α := by group
  rw [← map_mul, ← map_mul] at h3
  exact Ψ.symm.injective h3

theorem card_dvd_index_of_inf_eq_bot {K : Type*} [Group K] [Finite K] (B C : Subgroup K)
    [B.Normal] (h : C ⊓ B = ⊥) : Nat.card B ∣ C.index := by
  let φ : C →* K ⧸ B := (QuotientGroup.mk' B).comp C.subtype
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro c hc
    have h1 : (c : K) ∈ B := (QuotientGroup.eq_one_iff _).mp hc
    have h2 : (c : K) ∈ C ⊓ B := ⟨c.2, h1⟩
    rw [h, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_injective φ hφ
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup B
  have h3 := (Subgroup.card_mul_index C).symm
  refine ⟨k, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := C))
  rw [← h3, h2, hk]
  ring

variable {G : Type} [Group G]

theorem card_dvd_kernelCentralizer_index [Finite G] (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) {B : Subgroup G}
    (hBR : B ≤ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype)
    (hBN : ∀ k ∈ involutionCentralizer n S e, ∀ v ∈ B, k * v * k⁻¹ ∈ B)
    (y₁ : involutionCentralizer n S e) (hy₁B : ∀ v ∈ B, (y₁ : G) * v * (y₁ : G)⁻¹ = v⁻¹) :
    Nat.card B ∣
      (OddNormalQuotientInvolutions.kernelCentralizer (centralizerOddCore n S e) y₁).index := by
  set R := centralizerOddCore n S e with hRdef
  set ι : R →* G := (involutionCentralizer n S e).subtype.comp R.subtype with hι
  have hιinj : Function.Injective ι :=
    (involutionCentralizer n S e).subtype_injective.comp R.subtype_injective
  set BR : Subgroup R := B.comap ι with hBRdef
  have hBRnormal : BR.Normal := by
    refine ⟨fun v hv r => ?_⟩
    change ι (r * v * r⁻¹) ∈ B
    simp only [map_mul, map_inv]
    exact hBN _ (r : involutionCentralizer n S e).2 _ hv
  have hrange : B ≤ ι.range := by
    intro g hg
    obtain ⟨r, hr, rfl⟩ := hBR hg
    exact ⟨⟨r, hr⟩, rfl⟩
  have hcardBR : Nat.card BR = Nat.card B := by
    have h1 : BR.map ι = B := Subgroup.map_comap_eq_self hrange
    rw [← h1, Subgroup.card_map_of_injective hιinj]
  have hinf : OddNormalQuotientInvolutions.kernelCentralizer R y₁ ⊓ BR = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Subgroup.mem_bot]
    obtain ⟨hvC, hvB⟩ := hv
    have hvc : ((v : involutionCentralizer n S e) : G) * y₁ = y₁ * v := by
      have h1 : (v : involutionCentralizer n S e) * y₁ = y₁ * v :=
        Subgroup.mem_centralizer_singleton_iff.mp hvC
      exact congrArg Subtype.val h1
    have hvinv := hy₁B _ hvB
    have hv1 : ι v = 1 := by
      apply eq_one_of_inverted_of_fixed (oddCore_map_odd n S e) ⟨v, v.2, rfl⟩ hvinv
      exact hvc.symm
    exact hιinj (hv1.trans (map_one ι).symm)
  have h := card_dvd_index_of_inf_eq_bot BR _ hinf
  rwa [hcardBR] at h

theorem exists_prime_dvd_not_dvd_index [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hconf : ∀ r ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype, r ≠ 1 →
      Subgroup.normalizer (Subgroup.zpowers r : Set G) ≤ involutionCentralizer n S e)
    {B : Subgroup G}
    (hBR : B ≤ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype)
    (hB : B ≠ ⊥)
    (hinv : ∀ g ∈ involutionCentralizer n S e, orderOf g = 2 →
      g ≠ wreathModelHom S e (Original.x (2 ^ n)) → ∀ v ∈ B, g * v * g⁻¹ = v⁻¹) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ Nat.card B ∧ ¬ ℓ ∣ (involutionCentralizer n S e).index := by
  have hBodd : Odd (Nat.card B) :=
    (oddCore_map_odd n S e).of_dvd_nat (Subgroup.card_dvd_of_le hBR)
  have hB1 : Nat.card B ≠ 1 := fun h => hB (Subgroup.card_eq_one.mp h)
  obtain ⟨ℓ, hℓ, hℓB⟩ := Nat.exists_prime_and_dvd hB1
  refine ⟨ℓ, hℓ, hℓB, fun hℓI => ?_⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow ℓ B))
  set P' : Subgroup G := (P : Subgroup B).map B.subtype with hP'def
  have hP'B : P' ≤ B := Subgroup.map_subtype_le _
  have hP'1 : P' ≠ ⊥ := by
    rw [hP'def, Ne, Subgroup.map_eq_bot_iff_of_injective _ Subtype.val_injective]
    exact P.ne_bot_of_dvd_card hℓB
  have hP'N : P' ≤ involutionCentralizer n S e :=
    hP'B.trans (hBR.trans (Subgroup.map_subtype_le _))
  have hPp : IsPGroup ℓ (P'.comap (involutionCentralizer n S e).subtype) :=
    (P.isPGroup'.map B.subtype).comap_of_injective _ Subtype.val_injective
  obtain ⟨Q₀, hQ₀⟩ := hPp.exists_le_sylow
  have hPQ : P' ≤ (Q₀ : Subgroup (involutionCentralizer n S e)).map
      (involutionCentralizer n S e).subtype := fun g hg => ⟨⟨g, hP'N hg⟩, hQ₀ hg, rfl⟩
  have hNQ : Subgroup.normalizer (((Q₀ : Subgroup (involutionCentralizer n S e)).map
      (involutionCentralizer n S e).subtype : Subgroup G) : Set G) ≤
        involutionCentralizer n S e :=
    CFSG.Semidihedral.Principal.normalizer_le_centralizer_of_confined (orderOf_x n hn S e) hBodd
      hinv (fun u hu hu1 => centralizer_le_of_conf n S e hconf (hBR hu) hu1) hP'B hP'1 hPQ
      (Subgroup.map_subtype_le _)
  obtain ⟨T, hT⟩ := CFSG.Semidihedral.Principal.exists_sylow_eq_map_of_normalizer_le Q₀ hNQ
  have hTN : (T : Subgroup G) ≤ involutionCentralizer n S e := by
    rw [hT]
    exact Subgroup.map_subtype_le _
  exact T.not_dvd_index (hℓI.trans (Subgroup.index_dvd_of_le hTN))

theorem base_commute_lift_core [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (F : Type) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
    (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
    (ρ : centralizerFullQuotient n hn S e →*
      ComponentClassification.CatalogueSchreierLinearTwo.coordinateE F)
    (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma ≃* centralizerOddCoreQuotient n S e)
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    (hd : Nat.card Sigma = 1) (J : Subgroup (involutionCentralizer n S e)) [J.Normal]
    (hJR : J ⊓ centralizerOddCore n S e = ⊥) {u : G} (hu : u ∈ modelBase S e) {g : G}
    (hgJ : g ∈ J.map (involutionCentralizer n S e).subtype)
    (hgy : g * wreathModelHom S e (Original.x2 (2 ^ n)) =
      wreathModelHom S e (Original.x2 (2 ^ n)) * g) : u * g = g * u := by
  have huN : u ∈ involutionCentralizer n S e :=
    sylow_le_involutionCentralizer n hn S e (modelBase_le_sylow S e hu)
  obtain ⟨g', hg'J, rfl⟩ := hgJ
  set uN : involutionCentralizer n S e := ⟨u, huN⟩ with huNdef
  set yN : involutionCentralizer n S e :=
    ⟨wreathModelHom S e (Original.x2 (2 ^ n)), y_mem_involutionCentralizer n hn S e⟩ with hyN
  have huy : uN * yN = yN * uN := Subtype.ext
    (BrauerWong.modelBase_commute S e _ _ hu (BrauerWong.modelHom_x2_mem_modelBase S e))
  have hgy' : g' * yN = yN * g' := Subtype.ext hgy
  have hcomm := reduced_centralizer_comm n hn S e p f hp hpodd hf F Sigma b hSigma ρ Ψ hdata hd
    (α := centralizerOddCoreMap n S e uN) (β := centralizerOddCoreMap n S e g')
    (by rw [← map_mul, ← map_mul, huy]) (by rw [← map_mul, ← map_mul, hgy'])
  have hc : uN * g' * uN⁻¹ * g'⁻¹ ∈ J ⊓ centralizerOddCore n S e := by
    refine ⟨J.mul_mem ((inferInstance : J.Normal).conj_mem g' hg'J uN) (J.inv_mem hg'J), ?_⟩
    apply (QuotientGroup.eq_one_iff (N := centralizerOddCore n S e) _).mp
    change centralizerOddCoreMap n S e (uN * g' * uN⁻¹ * g'⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  rw [hJR, Subgroup.mem_bot] at hc
  have h1 : uN * g' = g' * uN := by
    calc uN * g' = (uN * g' * uN⁻¹ * g'⁻¹) * (g' * uN) := by group
      _ = g' * uN := by rw [hc, one_mul]
  exact congrArg Subtype.val h1

theorem fourCentralizer_centralizes_torusCore [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hconf : ∀ r ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype, r ≠ 1 →
      Subgroup.normalizer (Subgroup.zpowers r : Set G) ≤ involutionCentralizer n S e)
    (W₀ : Subgroup G) [IsCyclic W₀] [IsCyclic (torusFixedCore n S e)]
    (hRA : (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype =
      torusFixedCore n S e)
    (hsup : W₀ ⊔ torusFixedCore n S e = torusCore n S e)
    (hW₀A : W₀ ⊓ torusFixedCore n S e = ⊥)
    (hW₀Ac : ∀ g ∈ W₀, ∀ z ∈ torusFixedCore n S e, g * z = z * g)
    (hUW : ∀ u ∈ modelBase S e, ∀ g ∈ W₀, u * g = g * u) :
    Subgroup.centralizer (fourGroup n S e : Set G) ≤
      Subgroup.centralizer (torusCore n S e : Set G) := by
  set A₀ := torusFixedCore n S e with hA₀def
  set C₀ := torusCore n S e with hC₀def
  set CT := Subgroup.centralizer (fourGroup n S e : Set G) with hCT
  set RG := (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype with hRGdef
  have hstruct := sylow_and_base_four_group_centralizer_structure n hn S e
  have hT : modelT n S e = fourGroup n S e := hstruct.four_coordinates
  have hCV : CT = C₀ ⊔ modelBase S e := by
    have h := hstruct.base_split
    rw [hT] at h
    exact h
  have hWcomm : W₀ ≤ Subgroup.centralizer (W₀ : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val
      ((inferInstance : IsMulCommutative W₀).is_comm.comm ⟨h, hh⟩ ⟨g, hg⟩)
  have hAW : A₀ ≤ Subgroup.centralizer (W₀ : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact hW₀Ac g hg z hz
  have hC₀W : C₀ ≤ Subgroup.centralizer (W₀ : Set G) := by
    rw [← hsup]
    exact sup_le hWcomm hAW
  have hUW' : modelBase S e ≤ Subgroup.centralizer (W₀ : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact (hUW u hu g hg).symm
  have hCTW : CT ≤ Subgroup.centralizer (W₀ : Set G) := by
    rw [hCV]
    exact sup_le hC₀W hUW'
  have hCTN : CT ≤ involutionCentralizer n S e := centralizer_four_le n S e
  obtain ⟨μ, hμ⟩ := exists_prod_mulEquiv_of_commute W₀ A₀ C₀ hW₀Ac hW₀A hsup
  have hRA' : ∀ g, g ∈ RG ↔ g ∈ A₀ := fun g => by rw [hRA]
  have hKR : ⁅CT, C₀⁆ ≤ RG := by
    rw [Subgroup.commutator_le]
    intro g hg k hk
    set z := μ.symm ⟨k, hk⟩ with hzdef
    have hk' : k = (z.1 : G) * z.2 := by
      rw [← hμ z, hzdef, MulEquiv.apply_symm_apply]
    have hgw : g * z.1 = z.1 * g := (Subgroup.mem_centralizer_iff.mp (hCTW hg) _ z.1.2).symm
    have ha1 : (z.2 : G) ∈ RG := (hRA' _).mpr z.2.2
    have hga : g * z.2 * g⁻¹ ∈ RG := conj_mem_oddCore n S e (hCTN hg) ha1
    have hX : g * z.2 * g⁻¹ * (z.2 : G)⁻¹ ∈ A₀ := (hRA' _).mp (RG.mul_mem hga (RG.inv_mem ha1))
    have hw : (z.1 : G) * (g * z.2 * g⁻¹ * (z.2 : G)⁻¹) * (z.1 : G)⁻¹ =
        g * z.2 * g⁻¹ * (z.2 : G)⁻¹ := by
      rw [hW₀Ac _ z.1.2 _ hX, mul_inv_cancel_right]
    rw [commutatorElement_def, hk']
    have h1 : g * ((z.1 : G) * z.2) * g⁻¹ * ((z.1 : G) * z.2)⁻¹ =
        (z.1 : G) * (g * z.2 * g⁻¹ * (z.2 : G)⁻¹) * (z.1 : G)⁻¹ := by
      calc g * ((z.1 : G) * z.2) * g⁻¹ * ((z.1 : G) * z.2)⁻¹ =
          (g * z.1) * z.2 * g⁻¹ * (z.2 : G)⁻¹ * (z.1 : G)⁻¹ := by group
        _ = (z.1 * g) * z.2 * g⁻¹ * (z.2 : G)⁻¹ * (z.1 : G)⁻¹ := by rw [hgw]
        _ = (z.1 : G) * (g * z.2 * g⁻¹ * (z.2 : G)⁻¹) * (z.1 : G)⁻¹ := by group
    rw [h1, hw]
    exact RG.mul_mem hga (RG.inv_mem ha1)
  obtain ⟨a, haT, -, -, hacyc⟩ := exists_inverted_cycling_element hnonab n hn S e
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
  have haC₀ : a ∈ Subgroup.normalizer (C₀ : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact fun hh => ambientOddCore_conj_mem _ (normalizer_le_normalizer_centralizer _ haT) hh
    · intro hh
      have h1 := ambientOddCore_conj_mem _
        (normalizer_le_normalizer_centralizer _ (Subgroup.inv_mem _ haT)) hh
      rwa [show a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ = h by group] at h1
  have haCT : a ∈ Subgroup.normalizer (CT : Set G) :=
    normalizer_le_normalizer_centralizer _ haT
  set K : Subgroup G := ⁅CT, C₀⁆ with hKdef
  have haK : a ∈ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp haCT,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp haC₀]
  have hKbot : K = ⊥ := by
    by_contra hK
    have hRGcyc : IsCyclic RG := by
      rw [hRA]
      infer_instance
    have hKcyc : IsCyclic K :=
      isCyclic_of_injective (Subgroup.inclusion hKR) (Subgroup.inclusion_injective hKR)
    obtain ⟨r, hr⟩ := IsCyclic.exists_generator (α := K)
    have hKr : K = Subgroup.zpowers (r : G) := by
      ext g
      constructor
      · intro hg
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hr ⟨g, hg⟩)
        exact ⟨k, by change (r : G) ^ k = g; rw [← SubgroupClass.coe_zpow, hk]⟩
      · rintro ⟨k, rfl⟩
        exact Subgroup.zpow_mem _ r.2 k
    have hr1 : (r : G) ≠ 1 := by
      intro h1
      apply hK
      rw [hKr, h1, Subgroup.zpowers_one_eq_bot]
    apply haN
    exact hconf r (hKR r.2) hr1 (hKr ▸ haK)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKbot

theorem sylow_centralizes_oddCore [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hRA : (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype =
      torusFixedCore n S e)
    (hCT : Subgroup.centralizer (fourGroup n S e : Set G) ≤
      Subgroup.centralizer (torusCore n S e : Set G))
    (hwA : ∀ z ∈ torusFixedCore n S e, wreathModelHom S e (Original.z (2 ^ n)) * z =
      z * wreathModelHom S e (Original.z (2 ^ n))) :
    (S : Subgroup G) ≤ Subgroup.centralizer
      (((centralizerOddCore n S e).map (involutionCentralizer n S e).subtype : Subgroup G) :
        Set G) := by
  rw [hRA, ← wreathModelHom_range S e, MonoidHom.range_eq_map,
    ← wreath_eq_generated_s_swap, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨v, hv, rfl⟩
  rcases hv with rfl | hv
  ·
    have hsU : wreathModelHom S e (element (2 ^ n) 1 0 0) ∈ modelBase S e :=
      (BrauerWong.mem_modelBase_iff S e _).mpr (by simp)
    have hsT := modelBase_le_modelTCentralizer n (by omega) S e hsU
    rw [(sylow_and_base_four_group_centralizer_structure n hn S e).four_coordinates] at hsT
    intro z hz
    exact Subgroup.mem_centralizer_iff.mp (hCT hsT) z (torusFixedCore_le_torusCore n S e hz)
  · rw [Set.mem_singleton_iff] at hv
    subst hv
    intro z hz
    exact (hwA z hz).symm

theorem lift_inf_sylow
    [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (J : Subgroup (involutionCentralizer n S e)) [J.Normal]
    (hJM : J.map (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e))
    (hJR : J ⊓ centralizerOddCore n S e = ⊥) :
    J.map (involutionCentralizer n S e).subtype ⊓ (S : Subgroup G) =
      Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)) *
          (wreathModelHom S e (Original.t (2 ^ n)))⁻¹,
        wreathModelHom S e (Original.x2 (2 ^ n)) * wreathModelHom S e (Original.z (2 ^ n))} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := centralizerOddCore n S e with hRdef
  set π := centralizerOddCoreMap n S e with hπdef
  have hY : modelY S e = Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)) *
      (wreathModelHom S e (Original.t (2 ^ n)))⁻¹,
        wreathModelHom S e (Original.x2 (2 ^ n)) * wreathModelHom S e (Original.z (2 ^ n))} := by
    rw [modelY, Original.Y, MonoidHom.map_closure, Set.image_pair, Original.r, Original.d,
      map_mul, map_inv, map_mul]
  rw [← hY]
  have hSN : (S : Subgroup G) ≤ involutionCentralizer n S e :=
    sylow_le_involutionCentralizer n hn S e
  have hS2 : ∀ g ∈ (S : Subgroup G), ∃ k : ℕ, g ^ 2 ^ k = 1 := by
    intro g hg
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨g, hg⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hR1 : ∀ r : involutionCentralizer n S e, r ∈ R → ∀ k : ℕ, r ^ 2 ^ k = 1 → r = 1 := by
    intro r hr k hk
    have hodd := odd_orderOf_of_mem (centralizerOddCore_card_odd n S e) hr
    have hdvd : orderOf r ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have hcop : Nat.Coprime (orderOf r) (2 ^ k) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)
  have hπS : ∀ g g' : involutionCentralizer n S e, (g : G) ∈ (S : Subgroup G) →
      (g' : G) ∈ (S : Subgroup G) →
      π g = π g' → g = g' := by
    intro g g' hg hg' hgg'
    have hr : g⁻¹ * g' ∈ R := by
      apply (QuotientGroup.eq_one_iff (N := R) _).mp
      change π (g⁻¹ * g') = 1
      rw [map_mul, map_inv, hgg', inv_mul_cancel]
    have hS : ((g⁻¹ * g' : involutionCentralizer n S e) : G) ∈ (S : Subgroup G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hg) hg'
    obtain ⟨k, hk⟩ := hS2 _ hS
    have h1 : g⁻¹ * g' = 1 := hR1 _ hr k (Subtype.ext (by simpa using hk))
    exact inv_mul_eq_one.mp h1
  apply le_antisymm
  ·
    rintro g ⟨⟨gN, hgJ, rfl⟩, hgS⟩
    have hgM : π gN ∈ (centralizerOddCoreSylow n hn S e :
        Subgroup (centralizerOddCoreQuotient n S e)) ⊓
          CFSG.layer (centralizerOddCoreQuotient n S e) := by
      refine ⟨?_, hJM ▸ Subgroup.mem_map_of_mem π hgJ⟩
      rw [centralizerOddCoreSylow, Sylow.coe_mapSurjective, centralizerSylow_coe]
      exact ⟨gN, hgS, rfl⟩
    rw [ActualCentralizerSemilinear.actual_quotient_sylow_inter_layer hnonab n hn S e hfour]
      at hgM
    obtain ⟨v, hv, hve⟩ := hgM
    rw [ActualCentralizerSemilinear.actual_quotient_wreath_value] at hve
    have heq := hπS _ gN (by
      rw [centralizerModelHom_coe]
      exact BrauerWong.wreathModelHom_mem S e v) hgS hve
    refine ⟨v, hv, ?_⟩
    rw [← heq]
    rfl
  ·
    intro g hg
    have hgS : g ∈ (S : Subgroup G) := modelY_le_sylow S e hg
    refine ⟨?_, hgS⟩
    obtain ⟨v, hv, rfl⟩ := hg
    set gN : involutionCentralizer n S e :=
      wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) v with hgN
    have hgM : π gN ∈ CFSG.layer (centralizerOddCoreQuotient n S e) := by
      have h1 : wreathModelHom (centralizerOddCoreSylow n hn S e)
          (centralizerOddCoreCoordinates n hn S e) v ∈
            modelY (centralizerOddCoreSylow n hn S e) (centralizerOddCoreCoordinates n hn S e) :=
        Subgroup.mem_map_of_mem _ hv
      rw [← ActualCentralizerSemilinear.actual_quotient_sylow_inter_layer hnonab n hn S e hfour,
        ActualCentralizerSemilinear.actual_quotient_wreath_value] at h1
      exact h1.2
    rw [← hJM] at hgM
    obtain ⟨j, hjJ, hj⟩ := hgM
    set r : involutionCentralizer n S e := j⁻¹ * gN with hrdef
    have hr : r ∈ R := by
      apply (QuotientGroup.eq_one_iff (N := R) _).mp
      change π (j⁻¹ * gN) = 1
      rw [map_mul, map_inv, hj, inv_mul_cancel]
    have hjr : Commute j r :=
      Subtype.ext (lift_commute_oddCore n S e J hJR ⟨j, hjJ, rfl⟩ ⟨r, hr, rfl⟩)
    have hgjr : gN = j * r := by rw [hrdef, mul_inv_cancel_left]
    obtain ⟨k, hk⟩ := hS2 _ hgS
    have hk' : gN ^ 2 ^ k = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, hgN, centralizerModelHom_coe]
      exact hk)
    have hpow : j ^ 2 ^ k * r ^ 2 ^ k = 1 := by rw [← hjr.mul_pow, ← hgjr, hk']
    have hr2 : r ^ 2 ^ k ∈ J ⊓ R := by
      refine ⟨?_, R.pow_mem hr _⟩
      rw [eq_inv_of_mul_eq_one_right hpow]
      exact J.inv_mem (J.pow_mem hjJ _)
    rw [hJR, Subgroup.mem_bot] at hr2
    have hr1 : r = 1 := hR1 r hr k hr2
    refine ⟨gN, ?_, rfl⟩
    rw [hgjr, hr1, mul_one]
    exact hjJ

theorem lift_sylow_product
    [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : ActualProjectiveLayer.PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    (F : Type) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
    (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
    (ρ : centralizerFullQuotient n hn S e →*
      ComponentClassification.CatalogueSchreierLinearTwo.coordinateE F)
    (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma ≃* centralizerOddCoreQuotient n S e)
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    (hd : Nat.card Sigma = 1) (J : Subgroup (involutionCentralizer n S e)) [J.Normal]
    (hJM : J.map (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e))
    (g : involutionCentralizer n S e) :
    ∃ j ∈ J, ∃ s ∈ (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)),
      ∃ r ∈ centralizerOddCore n S e, g = j * s * r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype F := Fintype.ofFinite F
  set M := CFSG.layer (centralizerOddCoreQuotient n S e) with hMdef
  have : M.Normal := ActualCentralizerSemilinear.actual_layer_normal hnonab n hn S e hfour
  have h4 : 4 ∣ 2 ^ n := by
    have : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [this]
    exact Nat.pow_dvd_pow 2 hn
  obtain ⟨-, -, -, -, -, -, -, hcardH, -⟩ :=
    CentralSL2.semilinear_involution_classes_and_augmentation_values hp
      (hp.odd_of_ne_two hpodd) hf hdata.card b hdata.nonsquare (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) h4 Sigma hSigma hdata.sigma_odd
  obtain ⟨F', hF', hF'fin, hcard', -, -, -, -, eta, -⟩ :=
    FullCentralizerFromProjectiveModel.actual_projective_model_centralizer_data hnonab n hn S e
      hfour p f hp hpodd hf hmodel
  let : Field F' := hF'
  let : Finite F' := hF'fin
  have hMcard : Nat.card M = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [Nat.card_congr eta.toEquiv,
      CFSG.BenderSuzuki.External.huppert614_card_specialLinearGroup, hcard', hdata.card]
  have hHcard : Nat.card (centralizerOddCoreQuotient n S e) = 2 ^ n * Nat.card M := by
    rw [← Nat.card_congr Ψ.toEquiv, hcardH, hd, hMcard]
    ring
  have hindex : M.index = 2 ^ n := by
    have h1 := Subgroup.card_mul_index M
    rw [hHcard, mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hpg : IsPGroup 2 (centralizerOddCoreQuotient n S e ⧸ M) := IsPGroup.of_card hindex
  set Q := (centralizerOddCoreSylow n hn S e).mapSurjective (QuotientGroup.mk'_surjective M)
    with hQ
  have hQtop : (Q : Subgroup (centralizerOddCoreQuotient n S e ⧸ M)) = ⊤ :=
    (Q.is_maximal' (hpg.to_subgroup ⊤) le_top).symm
  have hmem : QuotientGroup.mk' M (centralizerOddCoreMap n S e g) ∈
      (Q : Subgroup (centralizerOddCoreQuotient n S e ⧸ M)) := by
    rw [hQtop]
    exact Subgroup.mem_top _
  rw [hQ, Sylow.coe_mapSurjective] at hmem
  obtain ⟨h, hh, hhg⟩ := hmem
  rw [centralizerOddCoreSylow, Sylow.coe_mapSurjective] at hh
  obtain ⟨s, hs, rfl⟩ := hh
  have hsM : (centralizerOddCoreMap n S e s)⁻¹ * centralizerOddCoreMap n S e g ∈ M :=
    QuotientGroup.eq.mp hhg
  rw [← hJM] at hsM
  obtain ⟨j, hj, hjeq⟩ := hsM
  have hr : (s * j)⁻¹ * g ∈ centralizerOddCore n S e := by
    apply (QuotientGroup.eq_one_iff (N := centralizerOddCore n S e) _).mp
    change centralizerOddCoreMap n S e ((s * j)⁻¹ * g) = 1
    rw [map_mul, map_inv, map_mul, hjeq]
    group
  refine ⟨s * j * s⁻¹, (inferInstance : J.Normal).conj_mem j hj s, s, hs, (s * j)⁻¹ * g, hr, ?_⟩
  group

theorem oddCore_le_center [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (J : Subgroup (involutionCentralizer n S e)) [J.Normal]
    (hJR : J ⊓ centralizerOddCore n S e = ⊥)
    (hprod : ∀ g : involutionCentralizer n S e, ∃ j ∈ J,
      ∃ s ∈ (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)),
        ∃ r ∈ centralizerOddCore n S e, g = j * s * r)
    (hSR : (S : Subgroup G) ≤ Subgroup.centralizer
      (((centralizerOddCore n S e).map (involutionCentralizer n S e).subtype : Subgroup G) :
        Set G))
    (hRcomm : ∀ a ∈ centralizerOddCore n S e, ∀ b ∈ centralizerOddCore n S e, a * b = b * a) :
    centralizerOddCore n S e ≤ Subgroup.center (involutionCentralizer n S e) := by
  intro r₀ hr₀
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨j, hj, s, hs, r, hr, rfl⟩ := hprod g
  have hjr : j * r₀ = r₀ * j :=
    Subtype.ext (lift_commute_oddCore n S e J hJR ⟨j, hj, rfl⟩ ⟨r₀, hr₀, rfl⟩)
  have hsS : (s : G) ∈ (S : Subgroup G) := by
    rw [centralizerSylow_coe] at hs
    exact hs
  have hsr : s * r₀ = r₀ * s :=
    Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hSR hsS) _ ⟨r₀, hr₀, rfl⟩).symm)
  have hrr : r * r₀ = r₀ * r := hRcomm r hr r₀ hr₀
  calc j * s * r * r₀ = j * s * (r₀ * r) := by rw [mul_assoc, hrr]
    _ = j * (s * r₀) * r := by group
    _ = j * (r₀ * s) * r := by rw [hsr]
    _ = (j * r₀) * s * r := by group
    _ = r₀ * j * s * r := by rw [hjr]
    _ = r₀ * (j * s * r) := by group

theorem lift_sylow_complement [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (J : Subgroup (involutionCentralizer n S e)) [J.Normal]
    (hJR : J ⊓ centralizerOddCore n S e = ⊥)
    (hRcent : centralizerOddCore n S e ≤ Subgroup.center (involutionCentralizer n S e))
    (hprod : ∀ g : involutionCentralizer n S e, ∃ j ∈ J,
      ∃ s ∈ (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)),
        ∃ r ∈ centralizerOddCore n S e, g = j * s * r) :
    ∃ JS : Subgroup (involutionCentralizer n S e),
      (JS : Set (involutionCentralizer n S e)) = (J : Set (involutionCentralizer n S e)) *
        ((centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)) :
          Set (involutionCentralizer n S e)) ∧
      JS ⊓ centralizerOddCore n S e = ⊥ ∧
      (∃ μ : centralizerOddCore n S e × JS ≃* involutionCentralizer n S e,
        ∀ z, (μ z : involutionCentralizer n S e) = z.1 * z.2) ∧
      ∃ φ : JS ≃* centralizerOddCoreQuotient n S e,
        ∀ k : JS, φ k = centralizerOddCoreMap n S e k := by
  set SN : Subgroup (involutionCentralizer n S e) :=
    (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e))
    with hSN
  set R := centralizerOddCore n S e with hRdef
  set JS := J ⊔ SN with hJS
  have hset : (JS : Set (involutionCentralizer n S e)) = (J : Set _) * (SN : Set _) :=
    Subgroup.normal_mul J SN
  have hJSR : JS ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    intro g ⟨hgJS, hgR⟩
    rw [Subgroup.mem_bot]
    have hg' : g ∈ (JS : Set (involutionCentralizer n S e)) := hgJS
    rw [hset] at hg'
    obtain ⟨j, hj, s, hs, rfl⟩ := Set.mem_mul.mp hg'
    obtain ⟨k, hk⟩ := (centralizerSylow n hn S e).isPGroup' ⟨s, hs⟩
    have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    set ψ := QuotientGroup.mk' J with hψ
    have hψj : ψ j = 1 := (QuotientGroup.eq_one_iff _).mpr hj
    have hψ : ψ (j * s) = ψ s := by rw [map_mul, hψj, one_mul]
    have hd1 : orderOf (ψ (j * s)) ∣ 2 ^ k := by
      rw [hψ]
      exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk', map_one])
    have hd2 : orderOf (ψ (j * s)) ∣ orderOf (j * s) := orderOf_map_dvd ψ _
    have hodd := odd_orderOf_of_mem (centralizerOddCore_card_odd n S e) hgR
    have hcop : Nat.Coprime (orderOf (ψ (j * s))) (2 ^ k) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr (hodd.of_dvd_nat hd2))
    have h1 : ψ (j * s) = 1 := orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hd1)
    have hjsJ : j * s ∈ J := (QuotientGroup.eq_one_iff _).mp h1
    have h2 : j * s ∈ J ⊓ R := ⟨hjsJ, hgR⟩
    rw [hJR, Subgroup.mem_bot] at h2
    exact h2
  have hsup : R ⊔ JS = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨j, hj, s, hs, r, hr, rfl⟩ := hprod g
    have hrjs : j * s * r = r * (j * s) :=
      ((Subgroup.mem_center_iff.mp (hRcent hr)) (j * s))
    rw [hrjs]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hr)
      (Subgroup.mem_sup_right (Subgroup.mul_mem _ (Subgroup.mem_sup_left hj)
        (Subgroup.mem_sup_right hs)))
  have hcomm : ∀ g ∈ R, ∀ z ∈ JS, g * z = z * g := fun g hg z _ =>
    ((Subgroup.mem_center_iff.mp (hRcent hg)) z).symm
  obtain ⟨μ, hμ⟩ := exists_prod_mulEquiv_of_commute R JS ⊤ hcomm
    (by rw [inf_comm]; exact hJSR) hsup
  refine ⟨JS, hset, hJSR, ⟨μ.trans Subgroup.topEquiv, fun z => hμ z⟩, ?_⟩
  let πJS : JS →* centralizerOddCoreQuotient n S e :=
    (centralizerOddCoreMap n S e).comp JS.subtype
  have hinj : Function.Injective πJS := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hkR : (k : involutionCentralizer n S e) ∈ R := (QuotientGroup.eq_one_iff _).mp hk
    have h1 : (k : involutionCentralizer n S e) ∈ JS ⊓ R := ⟨k.2, hkR⟩
    rw [hJSR, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hsurj : Function.Surjective πJS := by
    intro h
    obtain ⟨g, rfl⟩ := centralizerOddCoreMap_surjective n S e h
    obtain ⟨j, hj, s, hs, r, hr, rfl⟩ := hprod g
    refine ⟨⟨j * s, Subgroup.mul_mem _ (Subgroup.mem_sup_left hj) (Subgroup.mem_sup_right hs)⟩, ?_⟩
    change centralizerOddCoreMap n S e (j * s) = centralizerOddCoreMap n S e (j * s * r)
    have hr1 : centralizerOddCoreMap n S e r = 1 := (QuotientGroup.eq_one_iff (N := R) r).mpr hr
    rw [map_mul (centralizerOddCoreMap n S e) (j * s) r, hr1, mul_one]
  exact ⟨MulEquiv.ofBijective πJS ⟨hinj, hsurj⟩, fun k => rfl⟩

theorem involution_centralizes_oddCore (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hRA : (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype =
      torusFixedCore n S e)
    (hA₀mem : ∀ g, g ∈ torusFixedCore n S e ↔
      g ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ∧
        g * wreathModelHom S e (Original.x2 (2 ^ n)) = wreathModelHom S e (Original.x2 (2 ^ n)) * g)
    {g : G} {k : G} (hk : k ∈ involutionCentralizer n S e)
    (hkg : k * wreathModelHom S e (Original.x2 (2 ^ n)) * k⁻¹ = g) {r : G}
    (hr : r ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype) :
    g * r = r * g := by
  set y := wreathModelHom S e (Original.x2 (2 ^ n)) with hy
  have hr' : k⁻¹ * r * k⁻¹⁻¹ ∈
      (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype :=
    conj_mem_oddCore n S e ((involutionCentralizer n S e).inv_mem hk) hr
  rw [inv_inv] at hr'
  have hA := (hA₀mem _).mp (hRA ▸ hr')
  have h1 : y * (k⁻¹ * r * k) * y⁻¹ = k⁻¹ * r * k := by
    rw [← hA.2, mul_inv_cancel_right]
  rw [← hkg]
  calc k * y * k⁻¹ * r = k * (y * (k⁻¹ * r * k) * y⁻¹) * k⁻¹ * (k * y * k⁻¹) := by group
    _ = k * (k⁻¹ * r * k) * k⁻¹ * (k * y * k⁻¹) := by rw [h1]
    _ = r * (k * y * k⁻¹) := by group

end CFSG.Wreathed.ConfinedOddCore
