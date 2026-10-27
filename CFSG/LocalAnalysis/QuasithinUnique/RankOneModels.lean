module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneModelsAmbient
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneModelsLinear
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneModelsUnitary
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneModelsSuzuki
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismLinearKernel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismUnitaryKernel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiLayerKernel
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.ProperTwoGeneratedCore.RootCenter CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open scoped MatrixGroups commutatorElement

theorem HasFieldScalarStructure.isElemAbelian {G : Type*} [Group G] {V : Subgroup G} {q : ℕ}
    (h : HasFieldScalarStructure V q) : IsElemAbelian 2 V :=
  ⟨⟨⟨fun x y => Subtype.ext (h.mul_comm x x.2 y y.2)⟩⟩, h.sq_eq_one⟩

theorem hasFieldScalarStructure_omega₁_of_mulEquiv {X M : Type*} [Group X] [Group M] [Finite M]
    {q : ℕ} (e : X ≃* M) (P : Sylow 2 M)
    (h : HasFieldScalarStructure
      ((CFSG.omega₁ (G := (P : Subgroup M)) (p := 2)).map (P : Subgroup M).subtype) q)
    (Q : Sylow 2 X) :
    HasFieldScalarStructure
      ((CFSG.omega₁ (G := (Q : Subgroup X)) (p := 2)).map (Q : Subgroup X).subtype) q := by
  obtain ⟨ε, hε⟩ := exists_mulEquiv_map_eq e P Q
  rw [← hε, ← map_omega₁_map]
  exact h.map ε

theorem four_le_two_pow {n : ℕ} (hn : 2 ≤ n) : 4 ≤ 2 ^ n :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem finite_psu3 (f : ℕ) : Finite (PSU3 2 f) := by
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * f))) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  infer_instance

theorem linear_standard (f : ℕ) (hf : 2 ≤ f) :
    ∃ P : Sylow 2 PSL(2, GaloisField 2 f), HasFieldScalarStructure
      ((CFSG.omega₁ (G := (P : Subgroup PSL(2, GaloisField 2 f))) (p := 2)).map
        (P : Subgroup PSL(2, GaloisField 2 f)).subtype) (2 ^ f) := by
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hchar : CharP (GaloisField 2 f) 2 := LinearModel.charP_two_of_card hcard
  obtain ⟨P, hP⟩ := LinearModel.exists_sylow_eq_rootGroup hcard
  refine ⟨P, ?_⟩
  have hΩ := map_omega₁_eq_of_isElemAbelian (Q := (P : Subgroup PSL(2, GaloisField 2 f)))
    (by rw [hP]; exact LinearModel.rootGroup_isElemAbelian)
  rw [hΩ, hP]
  exact linear_hasFieldScalarStructure hcard

theorem exists_psu3_equiv (f : ℕ) (hf : 2 ≤ f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (J : HermitianForm 3 K),
      Nat.card K = (2 ^ f) ^ 2 ∧ Nat.card {x : K // J.conj x = x} = 2 ^ f ∧
        J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
        Nonempty (ProjectiveSpecialUnitaryMatrixGroup J ≃* PSU3 2 f) := by
  let k := GaloisField 2 f
  let K := FiniteField.Extension k 2 2
  let J := CFSG.BenderSuzuki.binaryQuadraticHermitian f (by omega)
  have : CharP K 2 := CharP.of_ringHom_of_ne_zero (algebraMap k K) 2 (by norm_num)
  have hKcard : Nat.card K = (2 ^ f) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 f (by omega)]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f :=
    CFSG.BenderSuzuki.quadraticBinaryFrobenius_fixed_card f (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  obtain ⟨e⟩ := CFSG.BenderSuzuki.projectiveSpecialUnitary_equiv_PSU3Model J f hf hJ hKcard hfixed
  have hmodel : CFSG.Theory.Comparator.PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
  exact ⟨K, inferInstance, inferInstance, J, hKcard, hfixed, hJ,
    ⟨e.trans (MulEquiv.subgroupCongr hmodel)⟩⟩

theorem unitary_standard (f : ℕ) (hf : 2 ≤ f) :
    ∃ P : Sylow 2 (PSU3 2 f), HasFieldScalarStructure
      ((CFSG.omega₁ (G := (P : Subgroup (PSU3 2 f))) (p := 2)).map
        (P : Subgroup (PSU3 2 f)).subtype) (2 ^ f) := by
  obtain ⟨K, _, _, J, hcard, hfixed, hJ, ⟨e⟩⟩ := exists_psu3_equiv f hf
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective _ Subtype.coe_injective
  let P₀ := unitaryCoverSylow J f hf hcard hfixed hJ
  have hΩ : (CFSG.omega₁ (G := (P₀ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)))
      (p := 2)).map (P₀ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype =
      (unitaryCoverFirstCoord J).ker.map (hermitianUnipotentPSU J hJ) :=
    map_omega₁_unitaryCoverRoot J hJ
  have h₀ := unitary_hasFieldScalarStructure J f hf hcard hfixed hJ
  rw [← hΩ] at h₀
  exact ⟨P₀.mapSurjective (f := e.toMonoidHom) e.surjective,
    hasFieldScalarStructure_omega₁_of_mulEquiv e.symm P₀ h₀ _⟩

noncomputable def szEquivSuzukiGroup (a : ℕ) :
    Sz a ≃* CFSG.Blueprint.suzukiGroup a (GaloisField 2 (2 * a + 1)) :=
  (suzukiCoverNativeEquiv a).trans (SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup
    (GaloisField.card 2 (2 * a + 1) (by omega))).symm

theorem finite_sz (a : ℕ) : Finite (Sz a) :=
  Finite.of_equiv _ (szEquivSuzukiGroup a).symm.toEquiv

theorem suzuki_standard (a : ℕ) (ha : 1 ≤ a) :
    ∃ P : Sylow 2 (Sz a), HasFieldScalarStructure
      ((CFSG.omega₁ (G := (P : Subgroup (Sz a))) (p := 2)).map (P : Subgroup (Sz a)).subtype)
      (2 ^ (2 * a + 1)) := by
  have hK : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  let e := szEquivSuzukiGroup a
  obtain ⟨P₀, hP₀⟩ := SuzukiModel.exists_sylow_eq_suzukiU hK
  have hΩ : (CFSG.omega₁ (G := (P₀ : Subgroup (CFSG.Blueprint.suzukiGroup a
      (GaloisField 2 (2 * a + 1))))) (p := 2)).map (P₀ : Subgroup _).subtype =
      CFSG.LieType.Ree.suzukiZ0 a (GaloisField 2 (2 * a + 1)) := by
    rw [hP₀]
    exact SuzukiLayerKernel.map_omega₁_suzukiU hK
  have h₀ := suzuki_hasFieldScalarStructure hK
  rw [← hΩ] at h₀
  exact ⟨P₀.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective,
    hasFieldScalarStructure_omega₁_of_mulEquiv e P₀ h₀ _⟩

theorem hasFieldScalarStructure_omega₁_of_fusionIsBenderGroup
    {X : Type*} [Group X]
    (hX : fusionIsBenderGroup X) (Q : Sylow 2 X) :
    ∃ q : ℕ, 4 ≤ q ∧ HasFieldScalarStructure
      ((CFSG.omega₁ (G := (Q : Subgroup X)) (p := 2)).map (Q : Subgroup X).subtype) q := by
  rcases hX with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · obtain ⟨P, hP⟩ := linear_standard f hf
    have : Finite PSL(2, GaloisField 2 f) := inferInstance
    exact ⟨2 ^ f, four_le_two_pow hf, hasFieldScalarStructure_omega₁_of_mulEquiv e P hP Q⟩
  · obtain ⟨P, hP⟩ := unitary_standard f hf
    have := finite_psu3 f
    exact ⟨2 ^ f, four_le_two_pow hf, hasFieldScalarStructure_omega₁_of_mulEquiv e P hP Q⟩
  · obtain ⟨P, hP⟩ := suzuki_standard a ha
    have := finite_sz a
    exact ⟨2 ^ (2 * a + 1), four_le_two_pow (by omega),
      hasFieldScalarStructure_omega₁_of_mulEquiv e P hP Q⟩


theorem finite_of_fusionIsBenderGroup {X : Type*} [Group X] (hX : fusionIsBenderGroup X) :
    Finite X := by
  rcases hX with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · exact Finite.of_equiv _ e.symm.toEquiv
  · have := finite_psu3 f
    exact Finite.of_equiv _ e.symm.toEquiv
  · have := finite_sz a
    exact Finite.of_equiv _ e.symm.toEquiv

theorem omega₁_eq_center_of_card {X : Type*} [Group X] [Finite X] {Q V : Subgroup X} {q : ℕ}
    (hV : V = (CFSG.omega₁ (G := Q) (p := 2)).map Q.subtype) (hVcard : Nat.card V = q)
    (hz : ∀ z ∈ Subgroup.center Q, z ^ 2 = 1) (hzcard : Nat.card (Subgroup.center Q) = q) :
    V = (Subgroup.center Q).map Q.subtype := by
  have hZV : (Subgroup.center Q).map Q.subtype ≤ V := by
    rintro _ ⟨z, hz', rfl⟩
    rw [hV, SuzukiLayerKernel.map_omega₁_subtype]
    exact Subgroup.subset_closure ⟨z.2, by
      rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hz z hz', OneMemClass.coe_one]⟩
  have h1 : Nat.card ((Subgroup.center Q).map Q.subtype) = q := by
    rw [Subgroup.card_map_of_injective Q.subtype_injective, hzcard]
  exact (Subgroup.eq_of_le_of_card_ge hZV (by rw [h1, hVcard])).symm

theorem linear_rank_one_involution_normalizer (f : ℕ) (hf : 2 ≤ f)
    (Q : Sylow 2 PSL(2, GaloisField 2 f)) (V : Subgroup PSL(2, GaloisField 2 f))
    (hV : V = (CFSG.omega₁ (G := (Q : Subgroup PSL(2, GaloisField 2 f))) (p := 2)).map
      (Q : Subgroup PSL(2, GaloisField 2 f)).subtype) :
    V = Q ∧ IsElemAbelian 2 V ∧ Nat.card V = 2 ^ f ∧ IsCyclic V.normalizerMonoidHom.range ∧
      Nat.card V.normalizerMonoidHom.range = 2 ^ f - 1 ∧
      ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃! α : V.normalizerMonoidHom.range, (α : MulAut V) v = w := by
  obtain ⟨P, hP⟩ := linear_standard f hf
  have : Finite PSL(2, GaloisField 2 f) := inferInstance
  have hS : HasFieldScalarStructure V (2 ^ f) := by
    rw [hV]
    exact hasFieldScalarStructure_omega₁_of_mulEquiv (MulEquiv.refl _) P hP Q
  have hVQ : V ≤ (Q : Subgroup PSL(2, GaloisField 2 f)) := hV ▸ Subgroup.map_subtype_le _
  have hQcard := (bender_psl2_borel_full f hf Q).2.2.2.2
  exact ⟨Subgroup.eq_of_le_of_card_ge hVQ (by rw [hQcard, pow_one, hS.card_eq]),
    hS.isElemAbelian, hS.card_eq, hS.normalizer_action.1, hS.normalizer_action.2.1,
    hS.normalizer_action.2.2⟩

theorem unitary_rank_one_involution_normalizer (f : ℕ) (hf : 2 ≤ f)
    (Q : Sylow 2 (PSU3 2 f)) (V : Subgroup (PSU3 2 f))
    (hV : V = (CFSG.omega₁ (G := (Q : Subgroup (PSU3 2 f))) (p := 2)).map
      (Q : Subgroup (PSU3 2 f)).subtype) :
    V = (Subgroup.center (Q : Subgroup (PSU3 2 f))).map (Q : Subgroup (PSU3 2 f)).subtype ∧
      IsElemAbelian 2 V ∧ Nat.card V = 2 ^ f ∧ IsCyclic V.normalizerMonoidHom.range ∧
      Nat.card V.normalizerMonoidHom.range = 2 ^ f - 1 ∧
      ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃! α : V.normalizerMonoidHom.range, (α : MulAut V) v = w := by
  obtain ⟨P, hP⟩ := unitary_standard f hf
  have := finite_psu3 f
  have hS : HasFieldScalarStructure V (2 ^ f) := by
    rw [hV]
    exact hasFieldScalarStructure_omega₁_of_mulEquiv (MulEquiv.refl _) P hP Q
  have hB := bender_psu3_borel_full f hf Q
  exact ⟨omega₁_eq_center_of_card hV hS.card_eq hB.2.2.1 hB.2.2.2.1, hS.isElemAbelian,
    hS.card_eq, hS.normalizer_action.1, hS.normalizer_action.2.1, hS.normalizer_action.2.2⟩

theorem suzuki_rank_one_involution_normalizer (a : ℕ) (ha : 1 ≤ a)
    (Q : Sylow 2 (Sz a)) (V : Subgroup (Sz a))
    (hV : V = (CFSG.omega₁ (G := (Q : Subgroup (Sz a))) (p := 2)).map
      (Q : Subgroup (Sz a)).subtype) :
    V = (Subgroup.center (Q : Subgroup (Sz a))).map (Q : Subgroup (Sz a)).subtype ∧
      IsElemAbelian 2 V ∧ Nat.card V = 2 ^ (2 * a + 1) ∧
      IsCyclic V.normalizerMonoidHom.range ∧
      Nat.card V.normalizerMonoidHom.range = 2 ^ (2 * a + 1) - 1 ∧
      ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃! α : V.normalizerMonoidHom.range, (α : MulAut V) v = w := by
  obtain ⟨P, hP⟩ := suzuki_standard a ha
  have := finite_sz a
  have hS : HasFieldScalarStructure V (2 ^ (2 * a + 1)) := by
    rw [hV]
    exact hasFieldScalarStructure_omega₁_of_mulEquiv (MulEquiv.refl _) P hP Q
  have hB := bender_suzuki_borel_full a ha Q
  exact ⟨omega₁_eq_center_of_card hV hS.card_eq hB.2.2.1 hB.2.2.2.1, hS.isElemAbelian,
    hS.card_eq, hS.normalizer_action.1, hS.normalizer_action.2.1, hS.normalizer_action.2.2⟩

theorem constructed_rank_one_involution_normalizer
    {X : Type*} [Group X]
    (hX : fusionIsBenderGroup X) (Q : Sylow 2 X) (V : Subgroup X)
    (hV : V = (CFSG.omega₁ (G := (Q : Subgroup X)) (p := 2)).map (Q : Subgroup X).subtype) :
    IsElemAbelian 2 V ∧ 4 ≤ Nat.card V ∧ IsCyclic V.normalizerMonoidHom.range ∧
      Nat.card V.normalizerMonoidHom.range = Nat.card V - 1 ∧
      ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃! α : V.normalizerMonoidHom.range, (α : MulAut V) v = w := by
  obtain ⟨q, hq, hS⟩ := hasFieldScalarStructure_omega₁_of_fusionIsBenderGroup hX Q
  rw [← hV] at hS
  refine ⟨hS.isElemAbelian, hS.card_eq ▸ hq, hS.normalizer_action.1, ?_,
    hS.normalizer_action.2.2⟩
  rw [hS.normalizer_action.2.1, hS.card_eq]

theorem layerKernel_of_mulEquiv_aux {X M : Type*} [Group X] [Group M] [Finite M] (e : X ≃* M)
    (P : Sylow 2 M)
    (hP : ∀ γ : MulAut M, (P : Subgroup M).map γ.toMonoidHom = P →
      (∀ v ∈ (CFSG.omega₁ (G := (P : Subgroup M)) (p := 2)).map (P : Subgroup M).subtype,
        γ v = v) →
      (∀ x ∈ (P : Subgroup M), x⁻¹ * γ x ∈
        (CFSG.omega₁ (G := (P : Subgroup M)) (p := 2)).map (P : Subgroup M).subtype) →
      ∃ b ∈ (P : Subgroup M), γ = MulAut.conj b)
    (Q : Sylow 2 X) (V : Subgroup X)
    (hV : V = (CFSG.omega₁ (G := (Q : Subgroup X)) (p := 2)).map (Q : Subgroup X).subtype)
    (γ : MulAut X) (hγQ : (Q : Subgroup X).map γ.toMonoidHom = Q) (hγV : ∀ v ∈ V, γ v = v)
    (hγQV : ∀ x ∈ (Q : Subgroup X), x⁻¹ * γ x ∈ V) :
    ∃ b ∈ (Q : Subgroup X), γ = MulAut.conj b := by
  obtain ⟨ε, hε⟩ := exists_mulEquiv_map_eq e P Q
  subst hV
  rw [← hε] at hγQ hγV hγQV ⊢
  exact layerKernel_map ε (P : Subgroup M) hP γ hγQ hγV hγQV

theorem suzuki_Sylow_layer_kernel_of_mulEquiv
    {X : Type*} [Group X] {a : ℕ} (ha : 1 ≤ a)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : X ≃* CFSG.Blueprint.suzukiGroup a K) (Q : Sylow 2 X) (V : Subgroup X)
    (hV : V = (CFSG.omega₁ (G := (Q : Subgroup X)) (p := 2)).map (Q : Subgroup X).subtype)
    (γ : MulAut X) (hγQ : (Q : Subgroup X).map γ.toMonoidHom = Q) (hγV : ∀ v ∈ V, γ v = v)
    (hγQV : ∀ x ∈ (Q : Subgroup X), x⁻¹ * γ x ∈ V) :
    ∃ b ∈ (Q : Subgroup X), γ = MulAut.conj b := by
  obtain ⟨P, -⟩ := SuzukiModel.exists_sylow_eq_suzukiU hK
  have hP : ∀ γ₀ : MulAut (CFSG.Blueprint.suzukiGroup a K),
      (P : Subgroup (CFSG.Blueprint.suzukiGroup a K)).map γ₀.toMonoidHom = P →
      (∀ v ∈ (CFSG.omega₁ (G := (P : Subgroup (CFSG.Blueprint.suzukiGroup a K))) (p := 2)).map
        (P : Subgroup (CFSG.Blueprint.suzukiGroup a K)).subtype, γ₀ v = v) →
      (∀ x ∈ (P : Subgroup (CFSG.Blueprint.suzukiGroup a K)), x⁻¹ * γ₀ x ∈
        (CFSG.omega₁ (G := (P : Subgroup (CFSG.Blueprint.suzukiGroup a K))) (p := 2)).map
          (P : Subgroup (CFSG.Blueprint.suzukiGroup a K)).subtype) →
      ∃ b ∈ (P : Subgroup (CFSG.Blueprint.suzukiGroup a K)), γ₀ = MulAut.conj b :=
    fun γ₀ h₁ h₂ h₃ => suzuki_rank_one_Sylow_layer_kernel ha hK P
      ((CFSG.omega₁ (G := (P : Subgroup (CFSG.Blueprint.suzukiGroup a K))) (p := 2)).map
        (P : Subgroup (CFSG.Blueprint.suzukiGroup a K)).subtype) rfl γ₀ h₁ h₂ h₃
  exact layerKernel_of_mulEquiv_aux e P hP Q V hV γ hγQ hγV hγQV

theorem constructed_rank_one_Sylow_layer_kernel {X : Type*} [Group X]
    (hX : fusionIsBenderGroup X) (Q : Sylow 2 X) (V : Subgroup X)
    (hV : V = (CFSG.omega₁ (G := (Q : Subgroup X)) (p := 2)).map (Q : Subgroup X).subtype)
    (γ : MulAut X) (hγQ : (Q : Subgroup X).map γ.toMonoidHom = Q) (hγV : ∀ v ∈ V, γ v = v)
    (hγQV : ∀ x ∈ (Q : Subgroup X), x⁻¹ * γ x ∈ V) :
    ∃ b ∈ (Q : Subgroup X), γ = MulAut.conj b := by
  rcases hX with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · exact linear_rank_one_Sylow_layer_kernel_of_mulEquiv hf
      (GaloisField.card 2 f (by omega)) e Q V hV γ hγQ hγV hγQV
  · obtain ⟨K, _, _, J, hcard, hfixed, hJ, ⟨e'⟩⟩ := exists_psu3_equiv f hf
    exact unitary_rank_one_Sylow_layer_kernel_of_mulEquiv J f hf hcard hfixed hJ (e.trans e'.symm)
      Q V hV γ hγQ hγV hγQV
  · exact suzuki_Sylow_layer_kernel_of_mulEquiv ha (GaloisField.card 2 (2 * a + 1) (by omega))
      (e.trans (szEquivSuzukiGroup a)) Q V hV γ hγQ hγV hγQV


theorem constructed_rank_one_involution_normalizer_ambient
    {G : Type*} [Group G]
    {L P V : Subgroup G} (hL : fusionIsBenderGroup L) (hP : IsSylowTwoOf P L)
    (hV : V = Subgroup.closure {x | x ∈ P ∧ x ^ 2 = 1}) :
    IsElemAbelian 2 V ∧ 4 ≤ Nat.card V ∧
      (∀ a ∈ V, a ≠ 1 → ∀ b ∈ V, b ≠ 1 →
        ∃ n ∈ L ⊓ Subgroup.normalizer (V : Set G), n⁻¹ * a * n = b) ∧
      (∀ n ∈ L ⊓ Subgroup.normalizer (V : Set G), ∀ a ∈ V, a ≠ 1 → n⁻¹ * a * n = a →
        ∀ x ∈ V, n⁻¹ * x * n = x) ∧
      (∃ g ∈ L ⊓ Subgroup.normalizer (V : Set G),
        ∀ n ∈ L ⊓ Subgroup.normalizer (V : Set G), ∃ k : ℕ, ∀ x ∈ V,
          n⁻¹ * x * n = (g ^ k)⁻¹ * x * g ^ k) := by
  obtain ⟨hPL, hp, hidx⟩ := hP
  obtain ⟨Q, hQ⟩ := exists_sylow_subgroupOf hPL hp hidx
  obtain ⟨q, hq, hS⟩ := hasFieldScalarStructure_omega₁_of_fusionIsBenderGroup hL Q
  have hVV : V = ((CFSG.omega₁ (G := (Q : Subgroup L)) (p := 2)).map
      (Q : Subgroup L).subtype).map L.subtype := by
    rw [hV, SuzukiLayerKernel.map_omega₁_subtype, hQ, map_closure_involutions_subgroupOf hPL]
  subst hVV
  obtain ⟨h1, h2, h3⟩ := hS.ambient
  exact ⟨isElemAbelian_map_subtype hS.isElemAbelian, by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hS.card_eq]; exact hq, h1, h2, h3⟩

private theorem trivial_sylow_layer_action_aux {G : Type*} [Group G] {H S U L V : Subgroup G}
    (hSH : S ≤ H) (hUS : U ≤ S) (hU : IsElemAbelian 2 U)
    (hcl : ∀ a ∈ U, ∀ g ∈ H, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ U)
    (hLH : L ≤ H) (hUL : U ≤ Subgroup.normalizer (L : Set G))
    (hV : V = Subgroup.closure {x | x ∈ S ⊓ L ∧ x ^ 2 = 1})
    (htrans : ∀ a ∈ V, a ≠ 1 → ∀ b ∈ V, b ≠ 1 →
      ∃ n ∈ L ⊓ Subgroup.normalizer (V : Set G), n⁻¹ * a * n = b) :
    U ≤ Subgroup.centralizer (V : Set G) ∧ ∀ u ∈ U, ∀ x ∈ S ⊓ L, x⁻¹ * (u⁻¹ * x * u) ∈ V := by
  have hVP : V ≤ S ⊓ L := by
    rw [hV]
    exact (Subgroup.closure_le _).2 fun x hx => hx.1
  have hAV : U ⊓ L ≤ V := by
    intro a ha
    rw [hV]
    exact Subgroup.subset_closure ⟨⟨hUS ha.1, ha.2⟩, hU.2 a ha.1⟩
  have hUnorm : ∀ s ∈ S, ∀ u ∈ U, s⁻¹ * u * s ∈ U := fun s hs u hu =>
    hcl u hu s (hSH hs) (S.mul_mem (S.mul_mem (S.inv_mem hs) (hUS hu)) hs)
  have hAinv : ∀ n ∈ L ⊓ Subgroup.normalizer (V : Set G), ∀ a ∈ U ⊓ L, n⁻¹ * a * n ∈ U ⊓ L := by
    rintro n ⟨hnL, hnV⟩ a ⟨haU, haL⟩
    have haV : a ∈ V := hAV ⟨haU, haL⟩
    have hmem : n⁻¹ * a * n ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (V : Set G)).inv_mem hnV) a).1
        haV
      simpa using this
    exact ⟨hcl a haU n (hLH hnL) (hVP hmem).1,
      L.mul_mem (L.mul_mem (L.inv_mem hnL) haL) hnL⟩
  have hdich : U ⊓ L = ⊥ ∨ U ⊓ L = V := by
    by_cases hA1 : U ⊓ L = ⊥
    · exact Or.inl hA1
    · refine Or.inr (le_antisymm hAV fun b hbV => ?_)
      obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA1
      have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
      by_cases hb1 : b = 1
      · rw [hb1]; exact Subgroup.one_mem _
      · obtain ⟨n, hn, hnab⟩ := htrans a (hAV haA) ha1' b hbV hb1
        rw [← hnab]
        exact hAinv n hn a haA
  have hcomm : ∀ x ∈ S ⊓ L, ∀ u ∈ U, ⁅x, u⁆ ∈ U ⊓ L := by
    intro x hx u hu
    refine ⟨?_, ?_⟩
    · have h1 : x * u * x⁻¹ ∈ U := by
        have := hUnorm x⁻¹ (S.inv_mem hx.1) u hu
        simpa using this
      rw [commutatorElement_def]
      exact U.mul_mem h1 (U.inv_mem hu)
    · have h2 : u * x⁻¹ * u⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.1 (hUL hu) x⁻¹).1 (L.inv_mem hx.2)
      have : ⁅x, u⁆ = x * (u * x⁻¹ * u⁻¹) := by
        rw [commutatorElement_def]; group
      rw [this]
      exact L.mul_mem hx.2 h2
  have hcommle : ⁅S ⊓ L, U⁆ ≤ U ⊓ L :=
    Subgroup.commutator_le.2 fun x hx u hu => hcomm x hx u hu
  have hconc : ⁅S ⊓ L, U⁆ ≤ V ∧ U ≤ Subgroup.centralizer (V : Set G) := by
    rcases hdich with h0 | h0
    · refine ⟨hcommle.trans (h0 ▸ bot_le), fun u hu => ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h1 : ⁅v, u⁆ ∈ U ⊓ L := hcomm v (hVP hv) u hu
      rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    · refine ⟨hcommle.trans h0.le, fun u hu => ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hvU : v ∈ U := by
        rw [← h0] at hv
        exact hv.1
      exact congrArg Subtype.val (hU.1.is_comm.comm ⟨v, hvU⟩ ⟨u, hu⟩)
  refine ⟨hconc.2, fun u hu x hx => ?_⟩
  have hmem : ⁅x⁻¹, u⁻¹⁆ ∈ ⁅S ⊓ L, U⁆ :=
    Subgroup.commutator_mem_commutator ((S ⊓ L).inv_mem hx) (U.inv_mem hu)
  have h := hconc.1 hmem
  simpa [commutatorElement_def, mul_assoc] using h

theorem strong_closure_rank_one_action_inner
    {G : Type*} [Group G] {H S U L : Subgroup G}
    (hS : IsSylowTwoOf S H) (hUS : U ≤ S) (hU : IsElemAbelian 2 U)
    (hcl : ∀ a ∈ U, ∀ g ∈ H, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ U)
    (hLH : L ≤ H) (hL : fusionIsBenderGroup L) (hUL : U ≤ Subgroup.normalizer (L : Set G))
    (hP : IsSylowTwoOf (S ⊓ L) L) :
    ∀ u ∈ U, ∃ p ∈ S ⊓ L, ∀ x ∈ L, u⁻¹ * x * u = p⁻¹ * x * p := by
  have : Finite L := finite_of_fusionIsBenderGroup hL
  obtain ⟨hPL, hp, hidx⟩ := hP
  obtain ⟨Q, hQ⟩ := exists_sylow_subgroupOf hPL hp hidx
  obtain ⟨q, hq, hS'⟩ := hasFieldScalarStructure_omega₁_of_fusionIsBenderGroup hL Q
  set V' := (CFSG.omega₁ (G := (Q : Subgroup L)) (p := 2)).map (Q : Subgroup L).subtype with hV'
  have hV : V'.map L.subtype = Subgroup.closure {x | x ∈ S ⊓ L ∧ x ^ 2 = 1} := by
    rw [hV', SuzukiLayerKernel.map_omega₁_subtype, hQ, map_closure_involutions_subgroupOf hPL]
  obtain ⟨htrans, -, -⟩ := hS'.ambient
  obtain ⟨hcent, hconj⟩ := trivial_sylow_layer_action_aux hS.1 hUS hU hcl hLH hUL hV htrans
  intro u hu
  have hun : u ∈ Subgroup.normalizer (L : Set G) := hUL hu
  have huS : u ∈ S := hUS hu
  let γ : MulAut L := L.normalizerMonoidHom ⟨u⁻¹, inv_mem hun⟩
  have hγ : ∀ x : L, ((γ x : L) : G) = u⁻¹ * x * u := fun x => by
    change (u⁻¹ * (x : G) * u⁻¹⁻¹ : G) = _
    rw [inv_inv]
  have hγQ : (Q : Subgroup L).map γ.toMonoidHom = Q := by
    refine Subgroup.eq_of_le_of_card_ge ?_
      (le_of_eq (Subgroup.card_map_of_injective γ.injective).symm)
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ (Q : Subgroup L) := hx
    rw [hQ, Subgroup.mem_subgroupOf] at hx' ⊢
    change (γ x : G) ∈ S ⊓ L
    rw [hγ]
    refine ⟨S.mul_mem (S.mul_mem (S.inv_mem huS) hx'.1) huS, ?_⟩
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hun) (x : G)).1 hx'.2
    rwa [inv_inv] at this
  have hγV : ∀ v ∈ V', γ v = v := fun v hv => by
    have hvV : (v : G) ∈ V'.map L.subtype := ⟨v, hv, rfl⟩
    have h1 : (v : G) * u = u * v := Subgroup.mem_centralizer_iff.1 (hcent hu) (v : G) hvV
    apply Subtype.ext
    rw [hγ, mul_assoc, h1, inv_mul_cancel_left]
  have hγQV : ∀ x ∈ (Q : Subgroup L), x⁻¹ * γ x ∈ V' := fun x hx => by
    have hxP : (x : G) ∈ S ⊓ L := by
      rw [hQ] at hx
      exact Subgroup.mem_subgroupOf.1 hx
    have h1 := hconj u hu (x : G) hxP
    refine (Subgroup.mem_map_iff_mem L.subtype_injective).1 ?_
    change ((x⁻¹ * γ x : L) : G) ∈ V'.map L.subtype
    rw [Subgroup.coe_mul, hγ]
    simpa using h1
  obtain ⟨b, hb, hγb⟩ := constructed_rank_one_Sylow_layer_kernel hL Q V' hV' γ hγQ hγV hγQV
  refine ⟨(b : G)⁻¹, ?_, fun x hx => ?_⟩
  · rw [hQ] at hb
    exact (S ⊓ L).inv_mem (Subgroup.mem_subgroupOf.1 hb)
  · have h1 := congrArg (fun φ : MulAut L => ((φ ⟨x, hx⟩ : L) : G)) hγb
    simp only [hγ, MulAut.conj_apply, Subgroup.coe_mul, InvMemClass.coe_inv] at h1
    rw [inv_inv]
    exact h1


theorem strong_closure_rank_one_action_inner_of_group
    {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) {U L : Subgroup H} (hUS : U ≤ S) (hU : IsElemAbelian 2 U)
    (hcl : fusionStronglyClosed (U : Set H) S) (hL : fusionIsBenderGroup L)
    (hUL : U ≤ Subgroup.normalizer (L : Set H))
    (hP : IsSylowTwoOf ((S : Subgroup H) ⊓ L) L) :
    ∀ u ∈ U, ∃ p ∈ (S : Subgroup H) ⊓ L, ∀ x ∈ L, u⁻¹ * x * u = p⁻¹ * x * p := by
  have hS : IsSylowTwoOf (S : Subgroup H) ⊤ := by
    refine ⟨le_top, S.isPGroup', ?_⟩
    have := S.not_dvd_index
    rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right]
  exact strong_closure_rank_one_action_inner hS hUS hU
    (fun a ha g _ hg => hcl a ha g hg) le_top hL hUL hP

end CFSG.QuasithinUnique
