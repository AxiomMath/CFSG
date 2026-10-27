module

public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneLocalBlocks
public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneRegularBasis
public import CFSG.CharacterTheory.Wreathed.UniqueLocalBlockSectionColumns
public import CFSG.CharacterTheory.Semidihedral.Principal.ActualSimpleLayerInvolutionColumns

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.FieldFactorOne

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.Wreathed.CompatibleFamily
open CFSG.Wreathed.LinearLocalTwistMoment CFSG.RankTwoShapes

variable {G : Type} [Group G] [Fintype G] {n : ℕ} {S : Sylow 2 G}
  (fS : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}

omit [Fintype G] in
theorem thetaG_ne_zero (θ : C t →* ℂˣ) (g : G) : ((thetaG t θ g : ℂˣ) : ℂ) ≠ 0 :=
  Units.ne_zero _

theorem typeStar_involution_columns (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    (hindex : ∀ V : Subgroup G, V.index ≠ 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (θ : C t →* ℂˣ) (hθS : ∀ c : C t, (c : G) ∈ (S : Subgroup G) → θ c = 1)
    (hθT : ∀ g ∈ Subgroup.normalizer
        ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G),
      ∀ c c' : C t,
        (c : G) ∈ Subgroup.centralizer
          ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G) →
        (c' : G) = g * c * g⁻¹ → θ c' = θ c)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (normalizerBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    (lambdaLabel : normalizerBasis.index)
    (hlambda : ∀ (x : Subgroup.normalizer ((S : Subgroup G) : Set G)) (q : G)
      (c : Subgroup.centralizer ((S : Subgroup G) : Set G)), q ∈ (S : Subgroup G) →
        (x : G) = q * c → (normalizerBasis.representation lambdaLabel).character x =
          thetaG t θ (c : G))
    (B : basis.index)
    (hB : brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
      (Subgroup.normalizer ((S : Subgroup G) : Set G)) (Subgroup.centralizer_le_normalizer _) le_rfl
        normalizerBasis lambdaLabel = centralCharacterResidueHom basis ideal B) :
    ∃ (e : ℤ) (φ : Subgroup.centralizer (Subgroup.zpowers t : Set G) → ℂ)
      (U V : basis.index → ℤ),
      (p ^ f % 4 = 1 → e = 1) ∧ (p ^ f % 4 = 3 → e = -1) ∧ (e = 1 ∨ e = -1) ∧
      φ 1 = ((p ^ f : ℕ) : ℂ) ∧
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        ∀ y : Subgroup.centralizer (Subgroup.zpowers t : Set G), Odd (orderOf y) →
          (basis.representation χ).character (t * y) =
            ((U χ : ℂ) + V χ * (1 + e * φ y)) * thetaG t θ (y : G)) ∧
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B, U χ * U χ = 8 ∧
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B, U χ * V χ = -4 ∧
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B, V χ * V χ =
        2 ^ (n - 2) + 2 ∧
      ∀ g : G, (∀ a c : G, a * c = g → Commute a c → (∃ k : ℕ, orderOf a = 2 ^ k) →
          ¬ 2 ∣ orderOf c → ¬ IsConj a t) →
        ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
            (U χ : ℂ) * starRingEnd ℂ ((basis.representation χ).character g) = 0 ∧
          ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
            (V χ : ℂ) * starRingEnd ℂ ((basis.representation χ).character g) = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : orderOf t = 2 := orderOf_t fS hn ht
  set Ct := Subgroup.centralizer (Subgroup.zpowers t : Set G) with hCtdef
  have hCt : Ct = C t := Principal.centralizer_zpowers_eq_centralizer_singleton t
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := Ct)
  obtain ⟨e, φ, he1, he3, he, hφ1, ⟨lφ, hlφB, hlφ⟩, hindep, D, hD, hD00, hD01, hD11⟩ :=
    regular_basis_data n hn S fS hindex t ht2 hnonab hcentral hnc p f hp hpodd hf hmodel ideal
      Ct hCt localBasis
  have hu2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
  have htC : t ∈ C t := by
    rw [C, Subgroup.mem_centralizer_singleton_iff]
  obtain ⟨ψLabel, hψchar, hbr, huniq, hβ⟩ := typeStar_local_block fS hn ht hindex θ hθS hθT
    basis ideal normalizerBasis lambdaLabel hlambda B hB hu2 (Subgroup.mem_zpowers t) htC
    localBasis
  set lam := family t θ (Subgroup.zpowers t) with hlam
  have hsp : Special t (Subgroup.zpowers t) := special_zpowers (Subgroup.mem_zpowers t) htC
  have hlamval : ∀ y : Ct, (lam y : ℂ) = thetaG t θ (y : G) := fun y => by
    rw [hlam, family_apply_special fS hn ht θ hθT hsp y]
  set σ := linearTwistLabelEquiv localBasis lam with hσ
  set B₀ := principalCoefficientBlock localBasis ideal with hB₀
  set β := coefficientBlock localBasis (localizedComplexIntegerRing ideal) ψLabel with hβdef
  have hβimage : β = B₀.image σ := hβ
  have hσchar : ∀ χ₀ (y : Ct), (localBasis.representation (σ χ₀)).character y =
      thetaG t θ (y : G) * (localBasis.representation χ₀).character y := fun χ₀ y => by
    rw [hσ, linearTwistLabelEquiv_character, hlamval]
  let b : Fin 2 → Ct → ℂ := ![fun y => thetaG t θ (y : G), fun y => thetaG t θ (y : G) *
    (1 + (e : ℂ) * φ y)]
  have hb0 : ∀ y, b 0 y = thetaG t θ (y : G) := fun y => rfl
  have hb1 : ∀ y, b 1 y = thetaG t θ (y : G) * (1 + (e : ℂ) * φ y) := fun y => rfl
  have hψβ : ψLabel ∈ β := coefficientBlock_self_mem _ _ _
  have hlφβ : σ lφ ∈ β := by
    rw [hβimage]
    exact Finset.mem_image_of_mem σ hlφB
  have hbmem : ∀ j, ∃ c : localBasis.index → ℂ, ∀ y, ¬ 2 ∣ orderOf y →
      b j y = ∑ θ' ∈ β, c θ' * (localBasis.representation θ').character y := by
    intro j
    fin_cases j
    · refine ⟨fun θ' => if θ' = ψLabel then 1 else 0, fun y _ => ?_⟩
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', hψβ, ↓reduceIte]
      rw [hψchar]
      rfl
    · refine ⟨fun θ' => (if θ' = ψLabel then 1 else 0) + (if θ' = σ lφ then (e : ℂ) else 0),
        fun y _ => ?_⟩
      simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', hψβ, hlφβ, ↓reduceIte]
      rw [hψchar, hσchar, hlφ]
      change thetaG t θ (y : G) * (1 + (e : ℂ) * φ y) = _
      ring
  have hbindep : ∀ c : Fin 2 → ℂ, (∀ y, ¬ 2 ∣ orderOf y → ∑ j, c j * b j y = 0) → c = 0 := by
    intro c hc
    have h := hindep (c 0) (c 1) fun y hy => by
      have hy' : ¬ 2 ∣ orderOf y := Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hy)
      have h0 := hc y hy'
      rw [Fin.sum_univ_two, hb0, hb1] at h0
      have hne := thetaG_ne_zero θ (y : G)
      have h1 : thetaG t θ (y : G) * (c 0 + c 1 * (1 + (e : ℂ) * φ y)) = 0 := by
        linear_combination h0
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hne
      · exact h
    funext j
    fin_cases j
    · exact h.1
    · exact h.2
  let d : localBasis.index → Fin 2 → ℤ := fun θ' j => D (σ.symm θ') j
  have hd : ∀ θ' ∈ β, ∀ y, ¬ 2 ∣ orderOf y →
      (localBasis.representation θ').character y = ∑ j, (d θ' j : ℂ) * b j y := by
    intro θ' hθ' y hy
    rw [hβimage] at hθ'
    obtain ⟨χ₀, hχ₀, rfl⟩ := Finset.mem_image.mp hθ'
    have hyodd : Odd (orderOf y) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hy)
    rw [hσchar, hD χ₀ hχ₀ y hyodd, Fin.sum_univ_two, hb0, hb1]
    simp only [d, Equiv.symm_apply_apply]
    ring
  have hu : orderOf t = 2 ^ 1 := by rw [ht2, pow_one]
  have hζ : IsPrimitiveRoot (-1 : ℂ) (2 ^ 1) := by
    rw [pow_one]
    exact IsPrimitiveRoot.neg_one 0 (by norm_num)
  obtain ⟨U', m, lam', hm, hlam', hU'def, -, hrow, -, hgram, horth⟩ :=
    unique_local_block_primary_section_integral_columns basis ideal 2 le_rfl hu hu2 localBasis
      B ψLabel hbr huniq hζ 2 (by norm_num) b hbmem hbindep d hd
  have hlampm : ∀ θ', lam' θ' = 1 ∨ lam' θ' = -1 := fun θ' => by
    obtain ⟨k, hk⟩ := (hlam' θ').1
    rw [hk]
    rcases Nat.even_or_odd k with hk' | hk'
    · exact Or.inl hk'.neg_one_pow
    · exact Or.inr hk'.neg_one_pow
  let ε : localBasis.index → ℤ := fun θ' => if lam' θ' = 1 then 1 else -1
  have hε : ∀ θ', ((ε θ' : ℤ) : ℂ) = lam' θ' := fun θ' => by
    rcases hlampm θ' with h | h
    · simp only [ε, h, ↓reduceIte, Int.cast_one]
    · have hne : lam' θ' ≠ 1 := by rw [h]; norm_num
      show ((if lam' θ' = 1 then 1 else -1 : ℤ) : ℂ) = lam' θ'
      rw [ite_eq_right hne, h]
      push_cast
      ring
  set U : basis.index → ℤ := fun χ => ∑ θ' ∈ β, (m χ θ' : ℤ) * ε θ' * d θ' 0 with hUdef
  set V : basis.index → ℤ := fun χ => ∑ θ' ∈ β, (m χ θ' : ℤ) * ε θ' * d θ' 1 with hVdef
  have hU : ∀ χ, (U χ : ℂ) = U' χ 0 := fun χ => by
    rw [hU'def χ 0, hUdef]
    push_cast
    refine Finset.sum_congr rfl fun θ' _ => ?_
    rw [hε]
  have hV : ∀ χ, (V χ : ℂ) = U' χ 1 := fun χ => by
    rw [hU'def χ 1, hVdef]
    push_cast
    refine Finset.sum_congr rfl fun θ' _ => ?_
    rw [hε]
  have hreindex : ∀ j k, ∑ θ' ∈ β, ((d θ' j * d θ' k : ℤ) : ℂ) =
      ∑ χ₀ ∈ B₀, ((D χ₀ j * D χ₀ k : ℤ) : ℂ) := by
    intro j k
    rw [hβimage, Finset.sum_image (fun x _ y _ hxy => σ.injective hxy)]
    refine Finset.sum_congr rfl fun χ₀ _ => ?_
    simp only [d, Equiv.symm_apply_apply]
  have hgramZ : ∀ j k, ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
      ((U' χ j * U' χ k) : ℂ) = ∑ χ₀ ∈ B₀, ((D χ₀ j * D χ₀ k : ℤ) : ℂ) := by
    intro j k
    rw [← hreindex, ← hgram j k]
    refine Finset.sum_congr rfl fun χ _ => ?_
    have hreal : starRingEnd ℂ (U' χ j) = U' χ j := by
      rw [hU'def χ j, map_sum]
      refine Finset.sum_congr rfl fun θ' _ => ?_
      rw [← hε θ', map_mul, map_mul, map_natCast, map_intCast, map_intCast]
    rw [hreal]
  refine ⟨e, φ, U, V, he1, he3, he, hφ1, fun χ hχ y hy => ?_, ?_, ?_, ?_, fun g hg => ?_⟩
  · have hy' : ¬ 2 ∣ orderOf y := Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hy)
    rw [hrow χ hχ y hy', Fin.sum_univ_two, hb0, hb1, ← hU, ← hV]
    ring
  · have h := hgramZ 0 0
    simp only [← hU] at h
    have h' : ((∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        U χ * U χ : ℤ) : ℂ) = ((∑ χ₀ ∈ B₀, D χ₀ 0 * D χ₀ 0 : ℤ) : ℂ) := by
      push_cast at h ⊢
      exact h
    rw [Int.cast_injective h', hD00]
  · have h := hgramZ 0 1
    simp only [← hU, ← hV] at h
    have h' : ((∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        U χ * V χ : ℤ) : ℂ) = ((∑ χ₀ ∈ B₀, D χ₀ 0 * D χ₀ 1 : ℤ) : ℂ) := by
      push_cast at h ⊢
      exact h
    rw [Int.cast_injective h', hD01]
  · have h := hgramZ 1 1
    simp only [← hV] at h
    have h' : ((∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        V χ * V χ : ℤ) : ℂ) = ((∑ χ₀ ∈ B₀, D χ₀ 1 * D χ₀ 1 : ℤ) : ℂ) := by
      push_cast at h ⊢
      exact h
    rw [Int.cast_injective h', hD11]
  · refine ⟨?_, ?_⟩
    · have h := horth g hg 0
      simpa only [← hU] using h
    · have h := horth g hg 1
      simpa only [← hV] using h

end CFSG.Semidihedral.FieldFactorOne
