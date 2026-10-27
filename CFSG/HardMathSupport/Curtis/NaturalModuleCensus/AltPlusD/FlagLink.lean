module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltPlusD.FlagSpin
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSpinMinus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted Matrix

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

omit [Finite F] [CharP F 2] in
theorem finrank_eSpan : Module.finrank F (eSpan n (K := F)) = n - 1 := by
  have hb := (Pi.basisFun F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)).linearIndependent
  have hli : LinearIndependent F (fun j : Fin (n - 1) =>
      (Pi.basisFun F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)) (Sum.inl j)) :=
    hb.comp _ Sum.inl_injective
  have hli' : LinearIndependent F (eVec n (K := F)) := by
    convert hli using 2
    simp [eVec, Pi.basisFun_apply]
  rw [eSpan, finrank_span_eq_card hli', Fintype.card_fin]


theorem exists_smul_mulVec_of_mk_eq {σ : Type} [Fintype σ] [DecidableEq σ] {K : Type} [Field K]
    {Q₀ : (σ → K) → K} {A B : StatedOmega Q₀}
    (h : (QuotientGroup.mk A : StatedProj (StatedOmega Q₀)) = QuotientGroup.mk B) :
    ∃ d : K, ∀ x : σ → K, ((A : GL σ K) : Matrix σ σ K) *ᵥ x =
      d • (((B : GL σ K) : Matrix σ σ K) *ᵥ x) :=
  CFSG.Open.StatedAPI.exists_smul_mulVec_of_mk_eq h

variable (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

theorem exists_stab_of_overgroup (hn : 4 ≤ n) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedOmega (StatedQuadMinus n F b c))) (T : Sylow 2 Y)
    (J : Subgroup Y) (hNJ : Subgroup.normalizer (T : Set Y) ≤ J)
    (hshort : ∀ π' : spinGroup (quadMinus n F b c) →* Y,
      π'.ker = (e.symm.toMonoidHom.comp (spinToStatedProj (quadMinus n F b c)
        (range_spinMatrix_quadMinus hn hirr))).ker →
      ∀ k : Fin (n - 1), ¬ k.val + 1 < n - 1 →
        ¬ (rankOne (minusDatum n hirr).rootGroup k).map π' ≤ J) :
    ∃ W : Submodule F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F),
      (∀ w ∈ W, StatedQuadMinus n F b c w = 0) ∧ Module.finrank F W = n - 1 ∧
      ∀ y ∈ J, ∀ A : StatedOmega (StatedQuadMinus n F b c),
        (QuotientGroup.mk A : StatedProj (StatedOmega (StatedQuadMinus n F b c))) = e y →
        ∀ w ∈ W, ((A : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *ᵥ w ∈ W := by
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have hB := borelQuotient_spinMinus hirr hn e
  set π := e.symm.toMonoidHom.comp (spinToStatedProj (quadMinus n F b c)
        (range_spinMatrix_quadMinus hn hirr)) with hπ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 (posUnipotent (minusDatum n hirr)) := isPGroup_iSup_pos hB.extras hB.pGroup
  have hidx : ¬ 2 ∣ ((posUnipotent (minusDatum n hirr)).map π).index := fun hd =>
    hB.not_dvd_index (hd.trans (Subgroup.index_map_dvd _ hB.surj))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y ((hU2.map π).toSylow hidx) T
  set π' : spinGroup (quadMinus n F b c) →* Y := (MulAut.conj g).toMonoidHom.comp π with hπ'
  have hπ'surj : Function.Surjective π' := (MulAut.conj g).surjective.comp hB.surj
  have hker : π'.ker = π.ker := by
    ext z
    simp [hπ', MonoidHom.mem_ker]
  have hT : (T : Subgroup Y) = (posUnipotent (minusDatum n hirr)).map π' := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    change Subgroup.map (MulAut.conj g).toMonoidHom ((posUnipotent _).map π) = _
    rw [Subgroup.map_map]
  have hQ : BorelQuotient (minusDatum n hirr) (minusWeyl n hirr) (minusTorus n hirr) π'
      (Nat.card F ^ 2 - 1) :=
    { ct := hB.ct, extras := hB.extras, pGroup := hB.pGroup, surj := hπ'surj, odd := hB.odd
      torus_pow := hB.torus_pow
      ker_central := fun z hz => hB.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => hB.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : (borel (minusDatum n hirr) (minusTorus n hirr)).map π' ≤ J := by
    rw [← hNπ]; exact hNJ
  have hBA : borel (minusDatum n hirr) (minusTorus n hirr) ≤ J.comap π' :=
    fun b hb => hBJ ⟨b, hb, rfl⟩
  have hJeq := eq_map_borel_sup_of_le hQ.ct hQ.extras hπ'surj hBJ
  have hbor : borel (minusDatum n hirr) (minusTorus n hirr) ≤
      stabE (n := n) (b := b) (c := c) := by
    refine sup_le (iSup_le fun i => ?_) ?_
    · by_cases hk : i.val + 1 < n - 1
      · exact (hB.ct.H_le i).trans (rankOne_le_stabE_of_lt hirr hk)
      · rw [minusTorus_of_not_lt n hirr hk]
        exact shortTorus_le_stabE hirr i
    · exact iSup₂_le fun γ hγ => minusRootGroup_le_stabE hirr hγ.1 hγ.2
  have hJle : J ≤ (stabE (n := n) (b := b) (c := c)).map π' := by
    refine hJeq.le.trans (sup_le (Subgroup.map_mono hbor) (iSup₂_le fun i hi =>
      Subgroup.map_mono ?_))
    by_cases hk : i.val + 1 < n - 1
    · exact rankOne_le_stabE_of_lt hirr hk
    · exact absurd (Subgroup.map_le_iff_le_comap.2 (rankOne_le_of_mem_negIndices hBA hi))
        (hshort π' hker i hk)
  obtain ⟨Ag, hAg⟩ := QuotientGroup.mk_surjective (e g)
  have hAgunit : IsUnit ((Ag : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
      Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :=
    (Ag : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F).isUnit
  have hAginj : Function.Injective (Matrix.mulVecLin ((Ag : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
      Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)) :=
    Matrix.mulVec_injective_iff_isUnit.mpr hAgunit
  refine ⟨(eSpan n (K := F)).map (Matrix.mulVecLin ((Ag : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
      Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)),
    ?_, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    rw [Matrix.mulVecLin_apply, preserves_of_mem_statedOmega Ag.2]
    have hv' : v ∈ eSpan n (K := F) := hv
    rw [mem_eSpan_iff] at hv'
    have h1 : ∀ i, v (.inr (.inl i)) = 0 := fun i => hv' _ (fun k => by simp)
    have h2 : ∀ t, v (.inr (.inr t)) = 0 := fun t => hv' _ (fun k => by simp)
    simp [StatedQuadMinus, h1, h2]
  · exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hAginj _)).symm.trans
      (finrank_eSpan (n := n) (F := F))
  · intro y hy A hA w hw
    obtain ⟨k, hk, rfl⟩ := hJle hy
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
    rw [Matrix.mulVecLin_apply]
    have hπk : e (π k) = (QuotientGroup.mk ⟨spinMatrix (quadMinus n F b c) k,
        spinMatrix_mem_of_range_eq _ (range_spinMatrix_quadMinus hn hirr) k⟩ :
        StatedProj (StatedOmega (StatedQuadMinus n F b c))) := by
      rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
        spinToStatedProj_apply]
    have hek : (QuotientGroup.mk A : StatedProj (StatedOmega (StatedQuadMinus n F b c))) =
        QuotientGroup.mk (Ag * ⟨spinMatrix (quadMinus n F b c) k,
          spinMatrix_mem_of_range_eq _ (range_spinMatrix_quadMinus hn hirr) k⟩ * Ag⁻¹) := by
      rw [hA, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hAg, ← hπk]
      simp [hπ', MulAut.conj_apply]
    obtain ⟨d, hd⟩ := exists_smul_mulVec_of_mk_eq hek
    rw [hd]
    refine Submodule.smul_mem _ _ ⟨spinMatrix (quadMinus n F b c) k *ᵥ v, ?_, ?_⟩
    · have hv' : v ∈ eSpan n (K := F) := hv
      rw [spinMatrix_mulVec]
      exact hk v hv'
    · simp only [Matrix.mulVecLin_apply]
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec]
      congr 2
      rw [Subgroup.coe_inv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
