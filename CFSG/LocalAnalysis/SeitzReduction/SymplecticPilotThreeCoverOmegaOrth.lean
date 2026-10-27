module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeCoverOmegaLevi

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LieType.Steinberg (sl2Upper)
open CFSG.SeitzReduction.LinearPilot (upperUnit diagUnit weylUnit coe_upperUnit subfieldSL
  twistedSubfield mem_twistedSubfield upperUnit_add upperUnit_inv upperUnit_mul_comm map_upperUnit
  map_weylUnit upperUnit_one_inv)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_le_centralizer
  normalizer_le_normalizer_centralizerPerfectCore)
open scoped MatrixGroups

section Orth

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F]

theorem modelToG_simpleRootSL2_zero_le_centralizer_pieceCore_two_of_fieldHom
    (hset : SeitzSetting G L) (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (ι : K →+* F) {σ : F ≃+* F}
    (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (φ : SL(2, F) →* G) (hM : φ.range = pieceCore e ({2} : Finset (Fin 3)))
    (hφι : ∀ A : SL(2, K),
      φ (SpecialLinearGroup.map ι A) = ((e.symm (longBlock K 3 2 A) : L) : G))
    (hφσ : ∀ A : SL(2, F), t * φ A * t⁻¹ = φ (SpecialLinearGroup.map σ.toRingHom A)) :
    modelToG e (simpleRootSL2 K (0 : Fin 3)) ≤
      centralizer (pieceCore e ({2} : Finset (Fin 3)) : Set G) := by
  classical
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp (by norm_num) e)
  have hσι : ∀ c : K, σ.toRingHom (ι c) = ι c := fun c => (hfix (ι c)).2 ⟨c, rfl⟩
  obtain ⟨ω, hω⟩ := LinearPilot.exists_trace_one_of_involution hσ1 hσσ
  have hFK : Nat.card F = Nat.card K ^ 2 := LinearPilot.natCard_eq_sq_of_trace_one ι hσσ hfix hω
  set z : G := ((e.symm (siegDiag K 2 1) : L) : G) with hzdef
  have hz : φ (upperUnit 1) = z := by
    have h := hφι (upperUnit 1)
    rw [map_upperUnit, map_one] at h
    rw [h, hzdef, siegDiag_eq_longBlock]
  set g : G := (φ (upperUnit ω))⁻¹ with hgdef
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hσω : t * φ (upperUnit ω) * t = φ (upperUnit ω * upperUnit 1) := by
    have h := hφσ (upperUnit ω)
    rw [htinv, map_upperUnit] at h
    rw [h, ← upperUnit_add]
    congr 2
  have hg : g⁻¹ * t * g = t * z := by
    rw [hgdef, inv_inv, ← hz]
    calc φ (upperUnit ω) * t * (φ (upperUnit ω))⁻¹
        = t * (t * φ (upperUnit ω) * t) * (φ (upperUnit ω))⁻¹ := by
          rw [show t * (t * φ (upperUnit ω) * t) * (φ (upperUnit ω))⁻¹ =
            (t * t) * φ (upperUnit ω) * t * (φ (upperUnit ω))⁻¹ by group, htt, one_mul]
      _ = t * φ (upperUnit 1) := by rw [hσω, upperUnit_mul_comm, map_mul]; group
  have hgz : g * z = z * g := by
    rw [hgdef, ← hz, ← map_inv, ← map_mul, ← map_mul, upperUnit_inv, upperUnit_mul_comm]
  set e₁ := swapChart e with he₁
  have hz₁ : ((e₁.symm (siegDiag K 1 1) : L) : G) = z := by
    rw [he₁, swapChart_symm_siegDiag]
  set φ' : StatedSp 3 K →* G :=
    (MulAut.conj g⁻¹).toMonoidHom.comp (L.subtype.comp e₁.symm.toMonoidHom) with hφ'def
  have hφ' : Function.Injective φ' :=
    (MulAut.conj g⁻¹).injective.comp (L.subtype_injective.comp e₁.symm.injective)
  have hφ'r : φ'.range = CFSG.conjugate L g := by
    rw [hφ'def, MonoidHom.range_comp, EPilot.range_subtype_comp_mulEquiv_symm]
    rfl
  have hφ'z : φ' (siegDiag K 1 1) = ((e₁.symm (siegDiag K 1 1) : L) : G) := by
    rw [hz₁]
    change g⁻¹ * ((e₁.symm (siegDiag K 1 1) : L) : G) * g⁻¹⁻¹ = z
    rw [hz₁, ((show Commute g z from hgz).inv_left).eq, mul_inv_cancel_right]
  set j : SL(2, K) →* G :=
    φ.comp ((MulAut.conj (upperUnit ω)).toMonoidHom.comp (SpecialLinearGroup.map ι)) with hjdef
  have hj : ∀ s, j s = φ (upperUnit ω * SpecialLinearGroup.map ι s * (upperUnit ω)⁻¹) :=
    fun s => rfl
  have hS : (twistedSubfield ι ω).map φ = j.range := by
    rw [hjdef, MonoidHom.range_comp, MonoidHom.range_comp]
    rfl
  have := LinearPilot.isSimpleGroup_specialLinearGroup_two (K := K) hK
  have := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  have hSt : j.range ≤ centralizer ({g⁻¹ * t * g} : Set G) := by
    rintro _ ⟨s, rfl⟩
    rw [mem_centralizer_singleton_iff, hg]
    set y := upperUnit ω * SpecialLinearGroup.map ι s * (upperUnit ω)⁻¹ with hydef
    have hy : y ∈ twistedSubfield ι ω := (mem_twistedSubfield ι).2 ⟨s, rfl⟩
    have hfixed : (t * z) * φ y * (t * z)⁻¹ = φ y := by
      rw [← hz]
      calc t * φ (upperUnit 1) * φ y * (t * φ (upperUnit 1))⁻¹ =
            t * φ (upperUnit 1 * y * (upperUnit 1)⁻¹) * t⁻¹ := by
              simp only [map_mul, map_inv]
              group
        _ = φ (SpecialLinearGroup.map σ.toRingHom (upperUnit 1 * y * (upperUnit 1)⁻¹)) := hφσ _
        _ = φ (upperUnit 1 * SpecialLinearGroup.map σ.toRingHom y * upperUnit 1) := by
              congr 1
              rw [map_mul, map_mul, map_inv, map_upperUnit, map_one, upperUnit_one_inv]
        _ = φ y := by rw [LinearPilot.twistedSubfield_fixed ι σ.toRingHom hσι hω hy]
    rw [hj, ← hydef]
    rw [mul_inv_eq_iff_eq_mul] at hfixed
    exact hfixed.symm
  have hSY : j.range ≤ centralizer (modelToG e₁ (threeTorus K) : Set G) := by
    have h1 : j.range ≤ φ.range := by
      rintro _ ⟨s, rfl⟩
      exact ⟨_, rfl⟩
    rw [hM] at h1
    exact h1.trans ((centralizerPerfectCore_le_centralizer _).trans
      (centralizer_le ((modelToG_swapChart_threeTorus_le e).trans inf_le_right)))
  have hzS : z ∈ j.range := ⟨upperUnit 1, by
    rw [hj, map_upperUnit, map_one, upperUnit_mul_comm, mul_inv_cancel_right, hz]⟩
  set B := modelToG e (simpleRootSL2 K (0 : Fin 3)) with hBdef
  have hBperf : ⁅B, B⁆ = B := by
    rw [hBdef, UnitaryPilot.modelToG_def, ← Subgroup.map_commutator, ← Subgroup.map_commutator,
      commutator_simpleRootSL2_eq_of_four_le hK 0]
  have hBL : B ≤ L := map_subtype_le _
  have hBA : B ≤ centralizer (modelToG e (longRootSp2 K 3 2) : Set G) :=
    UnitaryPilot.modelToG_le_centralizer e
      (simpleRootSL2_zero_le_complSp_two.trans (complSp_le_centralizer_longRootSp2 2))
  have hzA : z ∈ modelToG e (longRootSp2 K 3 2) :=
    UnitaryPilot.symm_mem_modelToG e (siegDiag_mem_longRootSp2 2 1)
  have hBz : B ≤ centralizer ({z} : Set G) :=
    hBA.trans (centralizer_le (Set.singleton_subset_iff.2 hzA))
  have hBY : B ≤ centralizer (modelToG e₁ (threeTorus K) : Set G) :=
    (UnitaryPilot.modelToG_le_centralizer e
      (simpleRootSL2_le_centralizer_leviTorusSp (Finset.mem_singleton_self 0))).trans
      (centralizer_le ((modelToG_swapChart_threeTorus_le e).trans inf_le_left))
  have hcore := le_centralizer_of_conj_eq_mul_three hset.standardSetting hOut hK e₁ htC ht
    (by rw [hz₁]; exact hg) hφ' hφ'r hφ'z (LinearPilot.commutator_range_eq_self_of_isPerfect j)
    (LinearPilot.eq_bot_or_eq_top_of_normal_range j) hSt hSY (by rw [hz₁]; exact hzS) hBperf
    hBL (by rw [hz₁]; exact hBz) hBY
  rw [le_centralizer_iff, ← hM, MonoidHom.range_eq_map,
    ← LinearPilot.sup_twistedSubfield_eq_top_of_trace_one ι hK hFK hσι hω, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    rw [hφι A]
    exact (le_centralizer_iff.1 hBA) (UnitaryPilot.symm_mem_modelToG e ⟨A, rfl⟩)
  · rw [hS]
    exact hcore


end Orth

section Unitary

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.SeitzReduction.F4Pilot (statedSpMap coe_statedSpMap)

variable {f : ℕ} {K' : Type} [Field K'] (h : UnitaryFieldData 2 f K') [CharP h.fixedField 2]
  {C₀ : GL (Fin (2 * 2)) K'}
  (hC₀ : (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') = blockSwapJ (2 * 2) 2)

omit [CharP h.fixedField 2] in
theorem primeFormFieldSU_lambdaU (hC : IsPrimeFormGram C₀) (A : SL(2, K')) :
    primeFormFieldSU h hC (UnitaryPilot.barRingEquiv h) (lambdaU h hC₀ A) =
      lambdaU h hC₀ (SpecialLinearGroup.map (UnitaryPilot.barRingEquiv h).toRingHom A) := by
  apply Subtype.ext
  apply Units.ext
  rw [F4Pilot.coe_primeFormFieldSU, coe_lambdaU, coe_lambdaU, lambdaUMat_eq, lambdaUMat_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UnitaryPilot.barRingEquiv_apply, UnitaryFieldData.bar_bar]

variable {K : Type} [Field K] [CharP K 2]

theorem uModelSU_tauSp_longBlock_one (ι : K ≃+* h.fixedField) (A : SL(2, K)) :
    uModelSU h hC₀ (statedSpMap (ι : K →+* h.fixedField) 2 (tauSp (longBlock K 2 1 A))) =
      lambdaU h hC₀ (SpecialLinearGroup.map (h.fixedField.subtype.comp (ι : K →+* h.fixedField))
        A) := by
  apply Subtype.ext
  apply Units.ext
  have hb : ∀ c : h.fixedField, h.bar (c : K') = c := fun c => c.2
  rw [coe_uModelSU, spModelSL_statedSpMap_tauSp_longBlock_one, coe_lambdaU, lambdaUMat_eq,
    coe_swapPairSL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapPairMat, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.submatrix_apply, hb] <;> rfl

end Unitary

section OrthUnitary

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.SeitzReduction.F4Pilot (statedSpMap)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockStandardPair)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem modelToG_simpleRootSL2_zero_le_centralizer_pieceCore_two_of_unitary_twisted
    (hset : SeitzSetting G L) {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hn : SpThreeUnitaryNormalized e t f 0 true) :
    modelToG e (simpleRootSL2 K (0 : Fin 3)) ≤
      centralizer (pieceCore e ({2} : Finset (Fin 3)) : Set G) := by
  obtain ⟨K', _, h, _, C₀, hC, hC₀, ι₀, Φ, hrange, hker, hN1, hN3⟩ := hn
  have : Finite K' := h.finite
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hN1' : ∀ x : StatedSp 2 K,
      Φ (uModelSU h hC₀ (statedSpMap (ι₀ : K →+* h.fixedField) 2 (tauSp x))) =
        ((e.symm ((complSpEquiv 0 x : complSp K 0) : StatedSp 3 K) : L) : G) := fun x => hN1 x
  set ι : K →+* K' := h.fixedField.subtype.comp (ι₀ : K →+* h.fixedField) with hιdef
  set σ := UnitaryPilot.barRingEquiv h with hσdef
  have hσ1 : σ ≠ 1 := by
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    intro h1
    apply hc
    rw [← UnitaryPilot.barRingEquiv_apply, ← hσdef, h1]
    rfl
  have hσσ : σ * σ = 1 := UnitaryPilot.barRingEquiv_mul_self h
  have hfix : ∀ x : K', σ x = x ↔ x ∈ Set.range ι := by
    intro x
    constructor
    · intro hx
      have hx' : x ∈ h.fixedField := by
        rw [UnitaryFieldData.mem_fixedField, ← UnitaryPilot.barRingEquiv_apply]
        exact hx
      refine ⟨ι₀.symm ⟨x, hx'⟩, ?_⟩
      simp [hιdef]
    · rintro ⟨c, rfl⟩
      rw [hσdef, UnitaryPilot.barRingEquiv_apply]
      exact (ι₀ c).2
  set φ : SL(2, K') →* G := Φ.comp (lambdaU h hC₀) with hφdef
  have hM : φ.range = pieceCore e ({2} : Finset (Fin 3)) := by
    rw [pieceCore_two_eq_map_lambdaU_of_N1 hKc hf e h hC₀ ι₀ Φ hrange hker hN1', hφdef,
      MonoidHom.range_comp]
  have hφι : ∀ A : SL(2, K),
      φ (SpecialLinearGroup.map ι A) = ((e.symm (longBlock K 3 2 A) : L) : G) := by
    intro A
    change Φ (lambdaU h hC₀ (SpecialLinearGroup.map ι A)) = _
    rw [hιdef, ← uModelSU_tauSp_longBlock_one h hC₀ ι₀ A, hN1', coe_complSpEquiv_apply,
      spEmbed_longBlock]
    rfl
  have hφσ : ∀ A : SL(2, K'), t * φ A * t⁻¹ = φ (SpecialLinearGroup.map σ.toRingHom A) := by
    intro A
    change t * Φ (lambdaU h hC₀ A) * t⁻¹ =
      Φ (lambdaU h hC₀ (SpecialLinearGroup.map σ.toRingHom A))
    rw [hN3, primeFormFieldSU_lambdaU h hC₀ hC]
  exact modelToG_simpleRootSL2_zero_le_centralizer_pieceCore_two_of_fieldHom hset hK4 e htC ht ι
    hσ1 hσσ hfix φ hM hφι hφσ

end OrthUnitary

section Pair

open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockStandardPair)


@[expose] def SpThreeOmegaMinusTwistedPairInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* StatedSp 3 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 3, RootKindSp e t f k .unitaryEven) → SpThreeTwisted e →
        ∃ (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (W : Subgroup G),
          TwistedB2BlockStandardPair hirr W (modelToG e (simpleRootSL2 K 1))
            (pieceCore e ({2} : Finset (Fin 3)))

theorem spThreeOmegaMinusPairInput_of_twistedPairInput (hp : SpThreeOmegaMinusTwistedPairInput) :
    SpThreeOmegaMinusPairInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t hto hKt hroot htw
  have htC : t ∈ centralizer (L : Set G) := by
    have h1 : t ∈ zpowers t := mem_zpowers t
    rw [← hKt] at h1
    exact h1.1
  refine ⟨?_, hp G L hset f K hKc hf e t hto hKt hroot htw⟩
  exact modelToG_simpleRootSL2_zero_le_centralizer_pieceCore_two_of_unitary_twisted hset hKc hf e
    htC hto (spThreeUnitaryNormalized_of_twisted hset hKc hf e htC hto 0 (hroot 0) htw)

theorem spThreeUnitaryEvenRecognitionInput_of_twistedPair (hs : SpThreeUnitaryEvenStandardInput)
    (hp : SpThreeOmegaMinusTwistedPairInput) : SpThreeUnitaryEvenRecognitionInput :=
  spThreeUnitaryEvenRecognitionInput_of_inputs hs
    (spThreeOmegaMinusPairInput_of_twistedPairInput hp)

end Pair

end CFSG.SeitzReduction.SymplecticPilot
