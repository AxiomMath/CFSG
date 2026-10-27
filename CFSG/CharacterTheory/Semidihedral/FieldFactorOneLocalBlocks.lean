module

public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneFamily
public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneSylowNormalizer
public import CFSG.CharacterTheory.Wreathed.LinearLocalTwistMoment

public section

open scoped Classical

namespace CFSG.Semidihedral.FieldFactorOne

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.Wreathed.CompatibleFamily
open CFSG.Wreathed.LinearLocalTwistMoment

variable {G : Type} [Group G] [Fintype G] {n : ℕ} {S : Sylow 2 G}
  (fS : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}

omit [Fintype G] in
theorem special_zpowers {u : G} (htu : t ∈ Subgroup.zpowers u) (hut : u ∈ C t) :
    Special t (Subgroup.zpowers u) := by
  refine ⟨htu, fun x hx => ?_⟩
  have hle : Subgroup.zpowers u ≤ C t := (Subgroup.zpowers_le (H := C t)).mpr hut
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

@[expose] noncomputable def sylowLinearCharacter (hn : 4 ≤ n) (θ : C t →* ℂˣ)
    (h1 : ∀ z : Subgroup.centralizer ((S : Subgroup G) : Set G), (z : G) ∈ (S : Subgroup G) →
      family t θ (S : Subgroup G) z = 1) :
    Subgroup.normalizer ((S : Subgroup G) : Set G) →* ℂˣ :=
  productLinearCharacter (S : Subgroup G) (family t θ (S : Subgroup G)) h1
    (Subgroup.normalizer ((S : Subgroup G) : Set G)) (sylow_normalizer_eq_mul_centralizer hn S fS)

theorem typeStar_local_block (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    (hindex : ∀ V : Subgroup G, V.index ≠ 2) (θ : C t →* ℂˣ)
    (hθS : ∀ c : C t, (c : G) ∈ (S : Subgroup G) → θ c = 1)
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
        normalizerBasis lambdaLabel = centralCharacterResidueHom basis ideal B)
    {u : G} (hu2 : IsPGroup 2 (Subgroup.zpowers u)) (htu : t ∈ Subgroup.zpowers u)
    (hut : u ∈ C t)
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers u : Set G))) :
    ∃ ψLabel : localBasis.index,
      (∀ c, (localBasis.representation ψLabel).character c = thetaG t θ (c : G)) ∧
      brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers u) hu2
          (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) localBasis ψLabel =
        centralCharacterResidueHom basis ideal B ∧
      (∀ β, brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers u) hu2
          (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) localBasis β =
            centralCharacterResidueHom basis ideal B →
        β ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) ψLabel) ∧
      coefficientBlock localBasis (localizedComplexIntegerRing ideal) ψLabel =
        linearTwistedBlock localBasis (family t θ (Subgroup.zpowers u))
          (principalCoefficientBlock localBasis ideal) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hψ := family_compatible fS hn ht hindex θ hθS hθT
  have hS1 : (S : Subgroup G) ≠ ⊥ := by
    intro h
    have htS := t_mem_sylow fS ht
    rw [h, Subgroup.mem_bot] at htS
    have := orderOf_t fS hn ht
    rw [htS, orderOf_one] at this
    exact absurd this (by norm_num)
  have hsp := special_zpowers htu hut
  have hu1 : Subgroup.zpowers u ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at htu
    have := orderOf_t fS hn ht
    rw [htu, orderOf_one] at this
    exact absurd this (by norm_num)
  have hfamS : ∀ (x : Subgroup.normalizer ((S : Subgroup G) : Set G)) (q : G)
      (c : Subgroup.centralizer ((S : Subgroup G) : Set G)), q ∈ (S : Subgroup G) →
        (x : G) = q * c → (normalizerBasis.representation lambdaLabel).character x =
          family t θ (S : Subgroup G) c := by
    intro x q c hq hx
    have hSsp : Special t (S : Subgroup G) := ⟨t_mem_sylow fS ht, fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (sylow_le_C fS hn ht hy)⟩
    rw [hlambda x q c hq hx, family_apply_special fS hn ht θ hθT hSsp c]
  obtain ⟨-, -, -, -, hcyc⟩ := compatible_family_unique_local_blocks basis ideal 2 S hS1
    (sylow_normalizer_eq_mul_centralizer hn S fS) (fun g => ((thetaG t θ (g : G) : ℂˣ) : ℂ))
    (family t θ) hψ normalizerBasis lambdaLabel hfamS B hB
  obtain ⟨-, hloc⟩ := hcyc (Subgroup.zpowers u) hu2 hu1 inferInstance
  obtain ⟨ψLabel, hψLabel⟩ := exists_linear_label localBasis (family t θ (Subgroup.zpowers u))
  obtain ⟨hbr, huniq, hmem⟩ := hloc localBasis ψLabel (principalCharacterLabel localBasis)
    hψLabel (principalCharacterLabel_character localBasis)
  refine ⟨ψLabel, fun c => ?_, hbr, fun β hβ => ?_, ?_⟩
  · rw [hψLabel c, family_apply_special fS hn ht θ hθT hsp c]
  · exact (coefficientBlock_mem_iff _ _ _ _).mpr (sameCoefficientBlock_symm _ _ (huniq β hβ))
  · ext θ'
    rw [hmem θ', mem_linearTwistedBlock]

theorem exists_typeStar_block (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    (hindex : ∀ V : Subgroup G, V.index ≠ 2) (θ : C t →* ℂˣ)
    (hθS : ∀ c : C t, (c : G) ∈ (S : Subgroup G) → θ c = 1)
    (hθT : ∀ g ∈ Subgroup.normalizer
        ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G),
      ∀ c c' : C t,
        (c : G) ∈ Subgroup.centralizer
          ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G) →
        (c' : G) = g * c * g⁻¹ → θ c' = θ c)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (normalizerBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G))) :
    ∃ lambdaLabel : normalizerBasis.index,
      (∀ (x : Subgroup.normalizer ((S : Subgroup G) : Set G)) (q : G)
        (c : Subgroup.centralizer ((S : Subgroup G) : Set G)), q ∈ (S : Subgroup G) →
          (x : G) = q * c → (normalizerBasis.representation lambdaLabel).character x =
            thetaG t θ (c : G)) ∧
      ∃ B : basis.index,
        brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
          (Subgroup.normalizer ((S : Subgroup G) : Set G)) (Subgroup.centralizer_le_normalizer _)
            le_rfl normalizerBasis lambdaLabel = centralCharacterResidueHom basis ideal B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hψ := family_compatible fS hn ht hindex θ hθS hθT
  have hS2 : IsPGroup 2 (S : Subgroup G) := S.isPGroup'
  have hS1 : (S : Subgroup G) ≠ ⊥ := by
    intro h
    have htS := t_mem_sylow fS ht
    rw [h, Subgroup.mem_bot] at htS
    have := orderOf_t fS hn ht
    rw [htS, orderOf_one] at this
    exact absurd this (by norm_num)
  have h1 := hψ.1 (S : Subgroup G) hS2 hS1
  obtain ⟨lambdaLabel, hlabel⟩ := exists_linear_label normalizerBasis
    (sylowLinearCharacter fS hn θ h1)
  have hSsp : Special t (S : Subgroup G) := ⟨t_mem_sylow fS ht, fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (sylow_le_C fS hn ht hy)⟩
  refine ⟨lambdaLabel, fun x q c hq hx => ?_, ?_⟩
  · rw [hlabel x, sylowLinearCharacter, productLinearCharacter_apply _ _ h1 _ _ x hq c hx,
      family_apply_special fS hn ht θ hθT hSsp c]
  · exact brauerNormalizer_block_image_exists basis ideal 2 (S : Subgroup G) hS2 _
      (Subgroup.centralizer_le_normalizer _) le_rfl normalizerBasis lambdaLabel

omit [Fintype G] in
theorem thetaG_one (g : G) : thetaG t (1 : C t →* ℂˣ) g = 1 := by
  unfold thetaG
  split_ifs <;> rfl

omit [Fintype G] in
theorem family_one (Q : Subgroup G) (x : Subgroup.centralizer (Q : Set G)) :
    family t (1 : C t →* ℂˣ) Q x = 1 := by
  unfold family
  split_ifs <;> rfl

theorem principal_local_block (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    (hindex : ∀ V : Subgroup G, V.index ≠ 2)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    {u : G} (hu2 : IsPGroup 2 (Subgroup.zpowers u)) (htu : t ∈ Subgroup.zpowers u)
    (hut : u ∈ C t)
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers u : Set G))) :
    brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers u) hu2
        (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) localBasis (principalCharacterLabel localBasis) =
      centralCharacterResidueHom basis ideal (principalCharacterLabel basis) ∧
    ∀ β, brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers u) hu2
        (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) localBasis β =
          centralCharacterResidueHom basis ideal (principalCharacterLabel basis) →
      β ∈ principalCoefficientBlock localBasis ideal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨brauerNormalizer_principal_residue_image basis ideal 2 _ hu2 _ le_rfl
    (Subgroup.centralizer_le_normalizer _) localBasis _ (principalCharacterLabel_character basis) _
    (principalCharacterLabel_character localBasis), fun β hβ => ?_⟩
  obtain ⟨normalizerBasis⟩ := finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.normalizer ((S : Subgroup G) : Set G))
  obtain ⟨ψLabel, -, -, huniq, hblock⟩ := typeStar_local_block fS hn ht hindex 1
    (fun _ _ => rfl) (fun _ _ _ _ _ _ => rfl) basis ideal normalizerBasis
    (principalCharacterLabel normalizerBasis)
    (fun x q c _ _ => by
      rw [principalCharacterLabel_character, Pi.one_apply, thetaG_one, Units.val_one])
    (principalCharacterLabel basis)
    (brauerNormalizer_principal_residue_image basis ideal 2 _ S.isPGroup' _
      (Subgroup.centralizer_le_normalizer _) le_rfl normalizerBasis _
      (principalCharacterLabel_character basis) _
      (principalCharacterLabel_character normalizerBasis))
    hu2 htu hut localBasis
  have hmem := huniq β hβ
  rw [hblock, mem_linearTwistedBlock] at hmem
  obtain ⟨θ₀, hθ₀, hval⟩ := hmem
  have hβθ₀ : β = θ₀ := localBasis.distinct (funext fun x => by
    change (localBasis.representation β).character x = (localBasis.representation θ₀).character x
    rw [hval, family_one, Units.val_one, one_mul])
  rw [hβθ₀]
  exact hθ₀

end CFSG.Semidihedral.FieldFactorOne
