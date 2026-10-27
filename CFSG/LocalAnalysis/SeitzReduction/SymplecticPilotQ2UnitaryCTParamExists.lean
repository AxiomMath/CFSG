module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2UnitaryCTParam

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LieType.Universal.Unitary (SU antidiag)

section Neighbour

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_surjective_primeFormP_nsNeighbourCore_unitary {m : ℕ} (hset : SeitzSetting G L)
    (hK : Nat.card K = 2) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1)) {κ : Sp2mKind}
    (hκ : κ = .unitaryEven ∨ κ = .unitaryOdd) (h : NsKindSp e t k κ)
    (hN : t ∈ normalizer (centralizerPerfectCore (modelToG e (nsTorusSp K k)) : Set G)) :
    ∃ (r : ℕ) (K' : Type) (_ : Field K') (h' : UnitaryFieldData 2 1 K') (C₀ : GL (Fin r) K')
      (hC₀ : IsPrimeFormGram C₀) (φ : K' ≃+* K')
      (ρ' : centralizerPerfectCore (modelToG e (nsTorusSp K k)) →*
        primeFormP h' (C₀ : Matrix (Fin r) (Fin r) K')),
      ((κ = .unitaryEven ∧ r = 2 * m ∧ (C₀ : Matrix (Fin r) (Fin r) K') = blockSwapJ r m) ∨
        (κ = .unitaryOdd ∧ r = 2 * m + 1 ∧ (C₀ : Matrix (Fin r) (Fin r) K') = 1)) ∧
      (∀ x, φ x = h'.bar x) ∧ Function.Surjective ρ' ∧
        ρ'.ker ≤ center (centralizerPerfectCore (modelToG e (nsTorusSp K k))) ∧
        Odd (Nat.card ρ'.ker) ∧
        ∀ y, ρ' ((centralizerPerfectCore (modelToG e (nsTorusSp K k))).normalizerMonoidHom
          ⟨t, hN⟩ y) = primeFormFieldHom h' hC₀ φ (ρ' y) := by
  have hκ' : IsLinearUnitaryKind κ := by
    rcases hκ with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr rfl))
  obtain ⟨S, _, ρ, τ, hρ, hker, hodd, hty, -, hρθ, hττ, hout, hfix⟩ :=
    exists_surjective_neighbourCore_linearUnitary_two hset hK hm e htC ht k rfl rfl hκ' h hN
  obtain ⟨r, hS, hr⟩ : ∃ r, LieModel S .PSU r 2 1 ∧
      ((κ = .unitaryEven ∧ r = 2 * m) ∨ (κ = .unitaryOdd ∧ r = 2 * m + 1)) := by
    rcases hκ with rfl | rfl
    · exact ⟨_, hty, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨_, hty, Or.inr ⟨rfl, rfl⟩⟩
  obtain ⟨K', _, h', C₀, hC₀, -, -, φ, ε, hcase, hφ, hε⟩ :=
    exists_primeFormFieldHom_eq_of_lieModel_PSU' hS hττ hout hfix
  have hker' : (ε.toMonoidHom.comp ρ).ker = ρ.ker := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  refine ⟨r, K', inferInstance, h', C₀, hC₀, φ, ε.toMonoidHom.comp ρ, ?_, hφ,
    ε.surjective.comp hρ, hker'.symm ▸ hker, hker'.symm ▸ hodd, fun y => ?_⟩
  · rcases hr with ⟨hκe, rfl⟩ | ⟨hκo, rfl⟩
    · rcases hcase with ⟨hodd2, -⟩ | ⟨r', hr', hJ⟩
      · exact absurd hodd2 (Nat.not_odd_iff_even.2 (even_two_mul m))
      · obtain rfl : r' = m := by omega
        exact Or.inl ⟨hκe, rfl, hJ⟩
    · rcases hcase with ⟨-, h1⟩ | ⟨r', hr', -⟩
      · exact Or.inr ⟨hκo, rfl, h1⟩
      · omega
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hρθ, ← hε, MulEquiv.coe_toMonoidHom,
      MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

theorem exists_nsGramParam_even {m : ℕ} [Finite K] [CharP K 2] (hset : SeitzSetting G L)
    (hK : Nat.card K = 2) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1))
    (hk : NsKindSp e t k .unitaryEven) :
    ∃ (K' : Type) (_ : Field K') (h : UnitaryFieldData 2 1 K') (_ : CharP h.fixedField 2)
      (C₀ : GL (Fin (2 * m)) K') (_ : IsPrimeFormGram C₀)
      (hC₀ : (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K') = blockSwapJ (2 * m) m)
      (ι : K ≃+* h.fixedField) (Φ : gramSU h (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K') →* G),
      Φ.range = centralizerPerfectCore (modelToG e (nsTorusSp K k)) ∧
      Φ.ker ≤ center (gramSU h (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K')) ∧
      ∀ x : StatedSp m K, Φ (uModelSU h hC₀ (statedSpMap (ι : K →+* h.fixedField) m x)) =
        ((e.symm ((complSpEquiv k x : complSp K k) : StatedSp (m + 1) K) : L) : G) := by
  have hN : t ∈ normalizer (centralizerPerfectCore (modelToG e (nsTorusSp K k)) : Set G) :=
    F4Pilot.normalizer_le_normalizer_centralizerPerfectCore _
      (UnitaryPilot.mem_normalizer_modelToG_of_mem_centralizer e htC _)
  obtain ⟨r, K', _, h', C₀, hC, φ, ρ', hcase, hφ, hρs, hρker, hρodd, hρt⟩ :=
    exists_surjective_primeFormP_nsNeighbourCore_unitary hset hK hm e htC ht k (Or.inl rfl) hk
      hN
  obtain ⟨-, rfl, hJ⟩ : Sp2mKind.unitaryEven = .unitaryEven ∧ r = 2 * m ∧
      (C₀ : Matrix (Fin r) (Fin r) K') = blockSwapJ r m := by
    rcases hcase with h1 | ⟨h2, -⟩
    · exact h1
    · exact absurd h2 (by decide)
  have hφb : φ = UnitaryPilot.barRingEquiv h' := RingEquiv.ext fun x =>
    (hφ x).trans (UnitaryPilot.barRingEquiv_apply h' x).symm
  subst hφb
  have hk2 : CharP h'.fixedField 2 :=
    CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer.fixedField_charP h'
  have hq : ¬(2 * m = 3 ∧ 2 ^ 1 = 2) := fun h3 => by omega
  obtain ⟨ι, Φ, hrange, hker, hN1⟩ := exists_nsParam_of_proj e hK hm htC k h' hC
    (gramSU_exists_section_of_odd_two h' hC (by omega))
    (uModelSU h' hJ) (uModelP_injective (h := h') (by omega) hJ)
    (range_uModelP (h := h') (by omega) hq hC hJ) hN ρ' hρs hρker hρodd hρt
  exact ⟨K', inferInstance, h', hk2, C₀, hC, hJ, ι, Φ, hrange, hker, hN1⟩

theorem exists_nsGramParam_odd {m : ℕ} [Finite K] [CharP K 2] (hset : SeitzSetting G L)
    (hK : Nat.card K = 2) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1))
    (hk : NsKindSp e t k .unitaryOdd) :
    ∃ (K' : Type) (_ : Field K') (h : UnitaryFieldData 2 1 K') (_ : CharP h.fixedField 2)
      (C₀ : GL (Fin (2 * m + 1)) K') (_ : IsPrimeFormGram C₀)
      (hC₀ : ((C₀ : GL (Fin (2 * m + 1)) K') :
        Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') = 1),
      ∀ β : StatedSp m h.fixedField ≃*
          matrixIsometryGroup (1 : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) h.fixedField),
        ∃ (ι : K ≃+* h.fixedField)
          (Φ : gramSU h (C₀ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') →* G),
          Φ.range = centralizerPerfectCore (modelToG e (nsTorusSp K k)) ∧
          Φ.ker ≤ center (gramSU h (C₀ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K')) ∧
          ∀ x : StatedSp m K,
            Φ (isoOneToSU h hC₀ (β (statedSpMap (ι : K →+* h.fixedField) m x))) =
              ((e.symm ((complSpEquiv k x : complSp K k) : StatedSp (m + 1) K) : L) : G) := by
  have hN : t ∈ normalizer (centralizerPerfectCore (modelToG e (nsTorusSp K k)) : Set G) :=
    F4Pilot.normalizer_le_normalizer_centralizerPerfectCore _
      (UnitaryPilot.mem_normalizer_modelToG_of_mem_centralizer e htC _)
  obtain ⟨r, K', _, h', C₀, hC, φ, ρ', hcase, hφ, hρs, hρker, hρodd, hρt⟩ :=
    exists_surjective_primeFormP_nsNeighbourCore_unitary hset hK hm e htC ht k (Or.inr rfl) hk
      hN
  obtain ⟨-, rfl, h1⟩ : Sp2mKind.unitaryOdd = .unitaryOdd ∧ r = 2 * m + 1 ∧
      (C₀ : Matrix (Fin r) (Fin r) K') = 1 := by
    rcases hcase with ⟨h2, -⟩ | h1
    · exact absurd h2 (by decide)
    · exact h1
  have hφb : φ = UnitaryPilot.barRingEquiv h' := RingEquiv.ext fun x =>
    (hφ x).trans (UnitaryPilot.barRingEquiv_apply h' x).symm
  subst hφb
  have hk2 : CharP h'.fixedField 2 :=
    CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer.fixedField_charP h'
  have hq : ¬(2 * m + 1 = 3 ∧ 2 ^ 1 = 2) := fun h3 => by omega
  refine ⟨K', inferInstance, h', hk2, C₀, hC, h1, fun β => ?_⟩
  have hμ : Function.Injective ((QuotientGroup.mk' (normOneScalars h'
      (gramSU h' (C₀ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K')) (2 * m + 1))).comp
        ((isoOneToSU h' h1).comp β.toMonoidHom)) :=
    (proj_isoOneToSU_injective (by omega) h1).comp β.injective
  have hμr : ((QuotientGroup.mk' (normOneScalars h'
      (gramSU h' (C₀ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K')) (2 * m + 1))).comp
        ((isoOneToSU h' h1).comp β.toMonoidHom)).range =
      fixedSubgroup (primeFormFieldHom h' hC (UnitaryPilot.barRingEquiv h')) := by
    rw [← MonoidHom.comp_assoc, MonoidHom.range_comp, MonoidHom.range_eq_top.2 β.surjective,
      ← MonoidHom.range_eq_map]
    exact range_proj_isoOneToSU (by omega) hq hC h1
  obtain ⟨ι, Φ, hrange, hker, hN1⟩ := exists_nsParam_of_proj e hK hm htC k h' hC
    (gramSU_one_exists_section_of_odd_two h' h1 (by omega)
      (by rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one m))
    ((isoOneToSU h' h1).comp β.toMonoidHom) hμ hμr hN ρ' hρs hρker hρodd hρt
  exact ⟨ι, Φ, hrange, hker, hN1⟩

end Neighbour

section Transport

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {m : ℕ}
  {F : Type} [Field F] [Finite F] [CharP F 2] {ι : K →+* F}
  {hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c} {e : L ≃* StatedSp (m + 1) K}
  {k : Fin (m + 1)} {K' : Type} [Field K'] {h : UnitaryFieldData 2 1 K'} [CharP h.fixedField 2]
  {ι' : K ≃+* h.fixedField}

@[expose] noncomputable def nsUniParamOfGram {C₀ : GL (Fin (2 * m)) K'}
    (hC₀ : (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K') = blockSwapJ (2 * m) m)
    (θ : F ≃+* K') (hθι : ∀ c, θ (ι c) = (ι' c : K'))
    (Φ : gramSU h (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K') →* G)
    (hrange : Φ.range = centralizerPerfectCore (modelToG e (nsTorusSp K k)))
    (hker : Φ.ker ≤ center (gramSU h (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K')))
    (hN1 : ∀ x : StatedSp m K,
      Φ (uModelSU h hC₀ (statedSpMap (ι' : K →+* h.fixedField) m x)) =
        ((e.symm ((complSpEquiv k x : complSp K k) : StatedSp (m + 1) K) : L) : G)) :
    NsUniParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι e k where
  Φ := Φ.comp (((ctuBlockEquiv (unitaryInvolution F 2 1) (Nat.zero_le 1) k).trans
    (ctuGramEquiv h hC₀ θ)).toMonoidHom)
  ker_le := by
    intro x hx
    exact mem_center_of_mulEquiv_mem_center _ (hker hx)
  range_eq := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, hrange]
  N1 y hy := by
    rw [spBlock_compl_singleton] at hy
    obtain ⟨x, hx⟩ := (complSpEquiv k).surjective ⟨y, hy⟩
    have hyx : y = ((complSpEquiv k x : complSp K k) : StatedSp (m + 1) K) := by rw [hx]
    subst hyx
    change Φ (ctuGramEquiv h hC₀ θ (ctuBlockEquiv (unitaryInvolution F 2 1) (Nat.zero_le 1) k
      ⟨_, _⟩)) = _
    rw [ctuBlockEquiv_ctuEmbed, ctuGramEquiv_ctuEmbed h hC₀ θ hι ι' hθι, hN1 x]

@[expose] noncomputable def nsUniParamOfGramOdd [Finite h.fixedField]
    {C₀ : GL (Fin (2 * m + 1)) K'}
    (hC₀ : ((C₀ : GL (Fin (2 * m + 1)) K') : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') = 1)
    (θ : F ≃+* K') (hθι : ∀ c, θ (ι c) = (ι' c : K')) (P : GL (Fin (2 * m + 1)) h.fixedField)
    (hP : ((P : GL (Fin (2 * m + 1)) h.fixedField) :
      Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) h.fixedField) * antidiag (2 * m + 1) *
        ((P : GL (Fin (2 * m + 1)) h.fixedField) :
          Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) h.fixedField)ᵀ = 1)
    (Φ : gramSU h (C₀ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') →* G)
    (hrange : Φ.range = centralizerPerfectCore (modelToG e (nsTorusSp K k)))
    (hker : Φ.ker ≤ center (gramSU h (C₀ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K')))
    (hN1 : ∀ x : StatedSp m K,
      Φ (isoOneToSU h hC₀ (oddBeta P hP (statedSpMap (ι' : K →+* h.fixedField) m x))) =
        ((e.symm ((complSpEquiv k x : complSp K k) : StatedSp (m + 1) K) : L) : G)) :
    NsUniParam 1 le_rfl (unitaryInvolution F 2 1) ι hι e k where
  Φ := Φ.comp (((ctuBlockEquiv (unitaryInvolution F 2 1) le_rfl k).trans
    (ctuOddGramEquiv h hC₀ θ P hP)).toMonoidHom)
  ker_le := by
    intro x hx
    exact mem_center_of_mulEquiv_mem_center _ (hker hx)
  range_eq := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, hrange]
  N1 y hy := by
    rw [spBlock_compl_singleton] at hy
    obtain ⟨x, hx⟩ := (complSpEquiv k).surjective ⟨y, hy⟩
    have hyx : y = ((complSpEquiv k x : complSp K k) : StatedSp (m + 1) K) := by rw [hx]
    subst hyx
    change Φ (ctuOddGramEquiv h hC₀ θ P hP (ctuBlockEquiv (unitaryInvolution F 2 1) le_rfl k
      ⟨_, _⟩)) = _
    rw [ctuBlockEquiv_ctuEmbed, ctuOddGramEquiv_ctuEmbed h hC₀ θ P hP hι ι' hθι, hN1 x]

end Transport

section Input


theorem spTwoUniParamInput_unitaryEven_holds :
    SpTwoUniParamInput .unitaryEven 0 (Nat.zero_le 1) := by
  intro G _ _ L hset n K _ _ _ hK hn e t ht hKt hroot
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hP := fun k => exists_nsGramParam_even hset hK (by omega : 3 ≤ n) e htC ht k (hroot k)
  obtain ⟨K₀', _, h₀, _, -, -, -, ι₀, -⟩ := hP 0
  have : Finite K₀' := h₀.finite
  have : CharP K₀' 2 := h₀.charP
  have hF : Nat.card K₀' = (2 ^ 1) ^ 2 := by rw [h₀.card]; norm_num
  set ι : K →+* K₀' := h₀.fixedField.subtype.comp (ι₀ : K →+* h₀.fixedField) with hιdef
  have hι : ∀ c, unitaryInvolution K₀' 2 1 (ι c) = ι c := fun c => by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← h₀.bar_apply]
    exact (h₀.mem_fixedField.1 (ι₀ c).2)
  refine ⟨K₀', inferInstance, inferInstance, inferInstance, hF, ι, hι, fun k => ?_⟩
  obtain ⟨K', _, h, _, C₀, hC, hC₀, ι', Φ, hrange, hker, hN1⟩ := hP k
  have : Finite K' := h.finite
  obtain ⟨θ, hθ⟩ := exists_ringEquiv_comp_eq ι
    (h.fixedField.subtype.comp (ι' : K →+* h.fixedField)) (by rw [hF, h.card]; norm_num)
  exact ⟨nsUniParamOfGram hC₀ θ hθ Φ hrange hker hN1⟩

theorem spTwoUniParamInput_unitaryOdd_holds : SpTwoUniParamInput .unitaryOdd 1 le_rfl := by
  intro G _ _ L hset n K _ _ _ hK hn e t ht hKt hroot
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hP := fun k => exists_nsGramParam_odd hset hK (by omega : 3 ≤ n) e htC ht k (hroot k)
  obtain ⟨K₀', _, h₀, _, C₀, hC, hC₀, hβ₀⟩ := hP 0
  have : Finite K₀' := h₀.finite
  have : CharP K₀' 2 := h₀.charP
  have : Finite h₀.fixedField :=
    CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer.fixedField_finite h₀
  obtain ⟨P₀, hP₀⟩ := exists_mul_antidiag_mul_transpose_eq_one (k := h₀.fixedField)
    (n := 2 * n + 1) (i₀ := ⟨n, by omega⟩) (Fin.ext (by simp only [Fin.val_rev]; omega))
  obtain ⟨ι₀, -⟩ := hβ₀ (oddBeta P₀ hP₀)
  have hF : Nat.card K₀' = (2 ^ 1) ^ 2 := by rw [h₀.card]; norm_num
  set ι : K →+* K₀' := h₀.fixedField.subtype.comp (ι₀ : K →+* h₀.fixedField) with hιdef
  have hι : ∀ c, unitaryInvolution K₀' 2 1 (ι c) = ι c := fun c => by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← h₀.bar_apply]
    exact (h₀.mem_fixedField.1 (ι₀ c).2)
  refine ⟨K₀', inferInstance, inferInstance, inferInstance, hF, ι, hι, fun k => ?_⟩
  obtain ⟨K', _, h, _, C, hCk, hCk₀, hβ⟩ := hP k
  have : Finite K' := h.finite
  have : Finite h.fixedField :=
    CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer.fixedField_finite h
  obtain ⟨P, hPk⟩ := exists_mul_antidiag_mul_transpose_eq_one (k := h.fixedField)
    (n := 2 * n + 1) (i₀ := ⟨n, by omega⟩) (Fin.ext (by simp only [Fin.val_rev]; omega))
  obtain ⟨ι', Φ, hrange, hker, hN1⟩ := hβ (oddBeta P hPk)
  obtain ⟨θ, hθ⟩ := exists_ringEquiv_comp_eq ι
    (h.fixedField.subtype.comp (ι' : K →+* h.fixedField)) (by rw [hF, h.card]; norm_num)
  exact ⟨nsUniParamOfGramOdd hCk₀ θ hθ P hPk Φ hrange hker hN1⟩

end Input

end CFSG.SeitzReduction.SymplecticPilot
