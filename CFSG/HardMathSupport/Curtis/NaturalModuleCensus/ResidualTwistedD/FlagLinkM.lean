module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualTwistedD.FlagSpinM
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltPlusD.FlagLink

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted Matrix

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

include hirr in
omit [CharP F 2] in
theorem exists_stab_of_missing_node (hn : 4 ≤ n)
    (π' : spinGroup (quadMinus n F b c) →* StatedProj (StatedOmega (StatedQuadMinus n F b c)))
    (g : StatedProj (StatedOmega (StatedQuadMinus n F b c)))
    (hπ' : ∀ k, π' k = g * spinToStatedProj (quadMinus n F b c)
      (range_spinMatrix_quadMinus hn hirr) k * g⁻¹)
    (hQ : BorelQuotient (minusDatum n hirr) (minusWeyl n hirr) (minusTorus n hirr) π'
      (Nat.card F ^ 2 - 1))
    {J : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n F b c)))}
    (hBJ : (borel (minusDatum n hirr) (minusTorus n hirr)).map π' ≤ J)
    {j : Fin (n - 1)}
    (hj : ¬ (rankOne (minusDatum n hirr).rootGroup j).map π' ≤ J) :
    ∃ W : Submodule F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F),
      (∀ w ∈ W, StatedQuadMinus n F b c w = 0) ∧ Module.finrank F W = j.val + 1 ∧
      ∀ y ∈ J, ∀ A : StatedOmega (StatedQuadMinus n F b c),
        (QuotientGroup.mk A : StatedProj (StatedOmega (StatedQuadMinus n F b c))) = y →
        ∀ w ∈ W, ((A : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *ᵥ w ∈
            W := by
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have hBA : borel (minusDatum n hirr) (minusTorus n hirr) ≤ J.comap π' :=
    fun b hb => hBJ ⟨b, hb, rfl⟩
  have hJeq := eq_map_borel_sup_of_le hQ.ct hQ.extras hQ.surj hBJ
  have hJle : J ≤ (stabEM (n := n) (b := b) (c := c) (j.val + 1)).map π' := by
    refine hJeq.le.trans (sup_le (Subgroup.map_mono (borel_le_stabEM hirr)) (iSup₂_le fun i hi =>
      Subgroup.map_mono ?_))
    have hij : i ≠ j := fun h =>
      hj (h ▸ Subgroup.map_le_iff_le_comap.2 (rankOne_le_of_mem_negIndices hBA hi))
    by_cases hk : i.val + 1 < n - 1
    · refine rankOne_le_stabEM_of_lt hirr hk fun h => hij (Fin.ext ?_)
      omega
    · refine rankOne_le_stabEM_short hirr hk ?_
      have h1 : i.val ≠ j.val := fun h => hij (Fin.ext h)
      have h2 := i.2
      have h3 := j.2
      omega
  obtain ⟨Ag, hAg⟩ := QuotientGroup.mk_surjective g
  have hAgunit : IsUnit ((Ag : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
      Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :=
    (Ag : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F).isUnit
  have hAginj : Function.Injective (Matrix.mulVecLin
      ((Ag : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
      Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)) :=
    Matrix.mulVec_injective_iff_isUnit.mpr hAgunit
  refine ⟨(eSpanM n (K := F) (j.val + 1)).map (Matrix.mulVecLin
      ((Ag : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
      Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)),
    ?_, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    rw [Matrix.mulVecLin_apply, preserves_of_mem_statedOmega Ag.2]
    have hv' : v ∈ eSpanM n (K := F) (j.val + 1) := hv
    rw [mem_eSpanM_iff] at hv'
    have h1 : ∀ i, v (.inr (.inl i)) = 0 := fun i => hv' _ (fun k _ => by simp)
    have h2 : ∀ t, v (.inr (.inr t)) = 0 := fun t => hv' _ (fun k _ => by simp)
    simp [StatedQuadMinus, h1, h2]
  · exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hAginj _)).symm.trans
      (finrank_eSpanM (n := n) (K := F) (m := j.val + 1) (by have := j.2; omega))
  · intro y hy A hA w hw
    obtain ⟨k, hk, rfl⟩ := hJle hy
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
    rw [Matrix.mulVecLin_apply]
    have hek : (QuotientGroup.mk A : StatedProj (StatedOmega (StatedQuadMinus n F b c))) =
        QuotientGroup.mk (Ag * ⟨spinMatrix (quadMinus n F b c) k,
          spinMatrix_mem_of_range_eq _ (range_spinMatrix_quadMinus hn hirr) k⟩ * Ag⁻¹) := by
      rw [hA, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hAg, hπ' k,
        spinToStatedProj_apply]
    obtain ⟨d, hd⟩ := exists_smul_mulVec_of_mk_eq hek
    rw [hd]
    refine Submodule.smul_mem _ _ ⟨spinMatrix (quadMinus n F b c) k *ᵥ v, ?_, ?_⟩
    · have hv' : v ∈ eSpanM n (K := F) (j.val + 1) := hv
      rw [spinMatrix_mulVec]
      exact hk v hv'
    · simp only [Matrix.mulVecLin_apply]
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec]
      congr 2
      rw [Subgroup.coe_inv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
