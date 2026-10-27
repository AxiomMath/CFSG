module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeD.FlagStabPlus
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltPlusD.FlagLink
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRadical

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Spin Matrix

@[expose] def nodeCowt (n : ℕ) (k : Fin n) (i : Fin n) : ℤ :=
  if k.val + 2 < n then (if i.val ≤ k.val then 1 else 0)
  else if k.val + 2 = n then (if i.val + 1 = n then -1 else 1)
  else 1

theorem nodeCowt_dom (n : ℕ) (k : Fin n) (i j : Fin n) (hij : i < j) :
    nodeCowt n k j ≤ nodeCowt n k i ∧ -nodeCowt n k j ≤ nodeCowt n k i := by
  have : (i : ℕ) < j := hij
  have := j.isLt
  have := k.isLt
  unfold nodeCowt
  split_ifs <;> omega

theorem nodeCowt_pos (n : ℕ) (hn : 2 ≤ n) (k : Fin n) : 0 < nodeCowt n k ⟨0, by omega⟩ := by
  have := k.isLt
  unfold nodeCowt
  split_ifs <;> simp_all
  omega

theorem nodeCowt_node (n : ℕ) (k i : Fin n) (hik : i ≠ k) (hn : 2 ≤ n) :
    nodeCowt n k (rootIdxD n i) + boolSign (rootSignD n i) * nodeCowt n k (rootIdxD' n i) = 0 := by
  have hik' : i.val ≠ k.val := fun h => hik (Fin.ext h)
  have := k.isLt
  have := i.isLt
  by_cases h : i.val + 1 < n
  · rw [rootIdxD_of_lt n h, rootIdxD'_of_lt n h, rootSignD_of_lt n h, boolSign_false]
    unfold nodeCowt
    split_ifs <;> simp_all <;> omega
  · rw [rootSignD_of_not_lt n h, boolSign_true]
    unfold nodeCowt
    simp only [val_rootIdxD_of_not_lt n h, val_rootIdxD'_of_not_lt n h]
    split_ifs <;> simp_all <;> omega

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_stab_of_overgroup_plus (hn : 4 ≤ n) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedOmega (StatedQuadPlus n F))) (T : Sylow 2 Y)
    (J : Subgroup Y) (hNJ : Subgroup.normalizer (T : Set Y) ≤ J) (hJ : J ≠ ⊤) :
    ∃ W : Submodule F (Fin n ⊕ Fin n → F), W ≠ ⊥ ∧
      (∀ w ∈ W, StatedQuadPlus n F w = 0) ∧
      ∀ y ∈ J, ∀ A : StatedOmega (StatedQuadPlus n F),
        (QuotientGroup.mk A : StatedProj (StatedOmega (StatedQuadPlus n F))) = e y →
        ∀ w ∈ W, ((A : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ w ∈ W := by
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  have hB := borelQuotient_spinPlus hn3 e
  set π := e.symm.toMonoidHom.comp (spinToStatedProj (quadPlus n F)
        (range_spinMatrix_quadPlus hn3)) with hπ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 (posUnipotent (plusDatum n F hn3)) :=
    isPGroup_iSup_pos hB.extras hB.pGroup
  have hidx : ¬ 2 ∣ ((posUnipotent (plusDatum n F hn3)).map π).index := fun hd =>
    hB.not_dvd_index (hd.trans (Subgroup.index_map_dvd _ hB.surj))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y ((hU2.map π).toSylow hidx) T
  set π' : spinGroup (quadPlus n F) →* Y := (MulAut.conj g).toMonoidHom.comp π with hπ'
  have hπ'surj : Function.Surjective π' := (MulAut.conj g).surjective.comp hB.surj
  have hker : π'.ker = π.ker := by
    ext z
    simp [hπ', MonoidHom.mem_ker]
  have hT : (T : Subgroup Y) = (posUnipotent (plusDatum n F hn3)).map π' := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    change Subgroup.map (MulAut.conj g).toMonoidHom ((posUnipotent _).map π) = _
    rw [Subgroup.map_map]
  have hQ : BorelQuotient (plusDatum n F hn3) (weylD F hn3) (fun k => (torusD F hn3 k).range) π'
      (Nat.card F - 1) :=
    { ct := hB.ct, extras := hB.extras, pGroup := hB.pGroup, surj := hπ'surj, odd := hB.odd
      torus_pow := hB.torus_pow
      ker_central := fun z hz => hB.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => hB.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : (borel (plusDatum n F hn3) (fun k => (torusD F hn3 k).range)).map π' ≤ J := by
    rw [← hNπ]; exact hNJ
  have hBA : borel (plusDatum n F hn3) (fun k => (torusD F hn3 k).range) ≤ J.comap π' :=
    fun b hb => hBJ ⟨b, hb, rfl⟩
  have hJeq := eq_map_borel_sup_of_le hQ.ct hQ.extras hπ'surj hBJ
  obtain ⟨k, hk⟩ := CFSG.AGLEmbedding.LieOut.exists_node_not_mem_negIndices hQ hBJ hJ
  set c : Fin n → ℤ := nodeCowt n k with hc
  have hdom : ∀ i j : Fin n, i < j → c j ≤ c i ∧ -c j ≤ c i := fun i j hij => nodeCowt_dom n k i j hij
  have hbor := borel_le_stabSub (K := F) hn3 c hdom
  have hJle : J ≤ (stabSub (quadPlus n F) (flagSpace F c)).map π' := by
    refine hJeq.le.trans (sup_le (Subgroup.map_mono hbor) (iSup₂_le fun i hi =>
      Subgroup.map_mono ?_))
    have hik : i ≠ k := fun h => hk (h ▸ hi)
    exact rankOneD_le_stabSub (K := F) hn3 c i (nodeCowt_node n k i hik (by omega))
  obtain ⟨Ag, hAg⟩ := QuotientGroup.mk_surjective (e g)
  have hAgunit : IsUnit ((Ag : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :=
    (Ag : GL (Fin n ⊕ Fin n) F).isUnit
  have hAginj : Function.Injective (Matrix.mulVecLin ((Ag : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) :=
    Matrix.mulVec_injective_iff_isUnit.mpr hAgunit
  refine ⟨(flagSpace F c).map (Matrix.mulVecLin ((Ag : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)), ?_, ?_, ?_⟩
  · intro hbot
    apply flagSpace_ne_bot (K := F) c (m := ⟨0, by omega⟩) (nodeCowt_pos n (by omega) k)
    rw [Submodule.eq_bot_iff] at hbot ⊢
    intro x hx
    apply hAginj
    rw [map_zero]
    exact hbot _ (Submodule.mem_map_of_mem hx)
  · rintro _ ⟨v, hv, rfl⟩
    rw [Matrix.mulVecLin_apply, preserves_of_mem_statedOmega Ag.2, ← congrFun (coe_quadPlus n F) v]
    exact quadPlus_flagSpace c hv
  · intro y hy A hA w hw
    obtain ⟨k, hk, rfl⟩ := hJle hy
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
    rw [Matrix.mulVecLin_apply]
    have hπk : e (π k) = (QuotientGroup.mk ⟨spinMatrix (quadPlus n F) k,
        spinMatrix_mem_of_range_eq _ (range_spinMatrix_quadPlus hn3) k⟩ :
        StatedProj (StatedOmega (StatedQuadPlus n F))) := by
      rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
        spinToStatedProj_apply]
    have hek : (QuotientGroup.mk A : StatedProj (StatedOmega (StatedQuadPlus n F))) =
        QuotientGroup.mk (Ag * ⟨spinMatrix (quadPlus n F) k,
          spinMatrix_mem_of_range_eq _ (range_spinMatrix_quadPlus hn3) k⟩ * Ag⁻¹) := by
      rw [hA, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hAg, ← hπk]
      simp [hπ', MulAut.conj_apply]
    obtain ⟨d, hd⟩ := exists_smul_mulVec_of_mk_eq hek
    rw [hd]
    refine Submodule.smul_mem _ _ ⟨spinMatrix (quadPlus n F) k *ᵥ v, ?_, ?_⟩
    · rw [spinMatrix_mulVec]
      exact hk v hv
    · simp only [Matrix.mulVecLin_apply]
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec]
      congr 2
      rw [Subgroup.coe_inv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
