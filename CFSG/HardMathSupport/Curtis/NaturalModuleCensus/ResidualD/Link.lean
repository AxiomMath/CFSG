module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualD.FlagStab
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSpin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRadical

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualD

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

theorem one_le_nodeCowt_of_ne (n : ℕ) (hn : 4 ≤ n) (k : Fin n) (hk : k.val ≠ 0) (i : Fin n)
    (hi : i.val ≤ 1) : 1 ≤ nodeCowt n k i := by
  have := k.isLt
  unfold nodeCowt
  split_ifs <;> omega

section

variable {n : ℕ} {F : Type} [Field F]

@[expose] noncomputable def genΩ [Finite F] [CharP F 2] (hn : 3 ≤ n)
    (x : spinGroup (quadPlus n F)) : StatedOmega (StatedQuadPlus n F) :=
  ⟨spinMatrix (quadPlus n F) x, spinMatrix_mem_of_range_eq _ (range_spinMatrix_quadPlus hn) x⟩

@[expose] noncomputable def ωp [Finite F] [CharP F 2] (hn : 3 ≤ n) (k : Fin n) :
    StatedOmega (StatedQuadPlus n F) :=
  genΩ hn (rootD F hn k (.ofAdd 1))

@[expose] noncomputable def ωn [Finite F] [CharP F 2] (hn : 3 ≤ n) (k : Fin n) :
    StatedOmega (StatedQuadPlus n F) :=
  genΩ hn (negRootD F hn k (.ofAdd 1))

end

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
theorem exists_smul_mulVec_of_mk_eq' {σ : Type} [Fintype σ] [DecidableEq σ] {K : Type} [Field K]
    {Q₀ : (σ → K) → K} {A B : StatedOmega Q₀}
    (h : (QuotientGroup.mk A : StatedProj (StatedOmega Q₀)) = QuotientGroup.mk B) :
    ∃ d : K, ∀ x : σ → K, ((A : GL σ K) : Matrix σ σ K) *ᵥ x =
      d • (((B : GL σ K) : Matrix σ σ K) *ᵥ x) :=
  CFSG.Open.StatedAPI.exists_smul_mulVec_of_mk_eq h

omit [Finite F] [CharP F 2] in
theorem two_le_finrank_flagSpace (hn : 4 ≤ n) (c : Fin n → ℤ) (h0 : 1 ≤ c ⟨0, by omega⟩)
    (h1 : 1 ≤ c ⟨1, by omega⟩) : 2 ≤ Module.finrank F (flagSpace F c) := by
  let f : Fin 2 → Fin n ⊕ Fin n := fun j => .inl ⟨j.val, by have := j.isLt; omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    simp only [f, Sum.inl.injEq, Fin.mk.injEq] at hab
    exact Fin.ext hab
  have hli : LinearIndependent F (fun j : Fin 2 => (Pi.basisFun F (Fin n ⊕ Fin n)) (f j)) :=
    (Pi.basisFun F (Fin n ⊕ Fin n)).linearIndependent.comp f hf
  have hle : Submodule.span F (Set.range (fun j : Fin 2 => (Pi.basisFun F (Fin n ⊕ Fin n)) (f j)))
      ≤ flagSpace F c := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    intro a ha
    have hj : a = f j := by
      by_contra hne
      apply ha
      simp [Pi.basisFun_apply, hne]
    subst hj
    have hj2 := j.isLt
    simp only [f, flagWt]
    fin_cases j
    · exact h0
    · exact h1
  have := Submodule.finrank_mono hle
  rwa [finrank_span_eq_card hli, Fintype.card_fin] at this


theorem exists_conj_data_plus (hn : 4 ≤ n) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedOmega (StatedQuadPlus n F))) (T : Sylow 2 Y)
    (J : Subgroup Y) (hNJ : Subgroup.normalizer (T : Set Y) ≤ J) (hJ : J ≠ ⊤) :
    ∃ (Ag : StatedOmega (StatedQuadPlus n F)) (I : Set (Fin n)), (∃ k, k ∉ I) ∧
      (∀ k, k ∉ I → ∃ W : Submodule F (Fin n ⊕ Fin n → F),
        (∀ w ∈ W, StatedQuadPlus n F w = 0) ∧ (k.val ≠ 0 → 2 ≤ Module.finrank F W) ∧
        ∀ y ∈ J, ∀ A : StatedOmega (StatedQuadPlus n F),
          (QuotientGroup.mk A : StatedProj (StatedOmega (StatedQuadPlus n F))) = e y →
          ∀ w ∈ W, ((A : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ w ∈ W) ∧
      (∀ i ∈ I, e.symm (QuotientGroup.mk (Ag * ωp (by omega) i * Ag⁻¹)) ∈ J ∧
        e.symm (QuotientGroup.mk (Ag * ωn (by omega) i * Ag⁻¹)) ∈ J) := by
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
  obtain ⟨k0, hk0⟩ := CFSG.AGLEmbedding.LieOut.exists_node_not_mem_negIndices hQ hBJ hJ
  obtain ⟨Ag, hAg⟩ := QuotientGroup.mk_surjective (e g)
  have hπx : ∀ x : spinGroup (quadPlus n F), e (π' x) =
      (QuotientGroup.mk (Ag * genΩ hn3 x * Ag⁻¹) :
        StatedProj (StatedOmega (StatedQuadPlus n F))) := by
    intro x
    have hπk : e (π x) = (QuotientGroup.mk (genΩ hn3 x) :
        StatedProj (StatedOmega (StatedQuadPlus n F))) := by
      rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
        spinToStatedProj_apply]
      rfl
    rw [hπ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul,
      map_inv, hπk, ← hAg, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  refine ⟨Ag, negIndices (plusDatum n F hn3) (J.comap π'), ⟨k0, hk0⟩, ?_, ?_⟩
  · intro k hk
    set c : Fin n → ℤ := nodeCowt n k with hc
    have hdom : ∀ i j : Fin n, i < j → c j ≤ c i ∧ -c j ≤ c i :=
      fun i j hij => nodeCowt_dom n k i j hij
    have hbor := borel_le_stabSub (K := F) hn3 c hdom
    have hJle : J ≤ (stabSub (quadPlus n F) (flagSpace F c)).map π' := by
      refine hJeq.le.trans (sup_le (Subgroup.map_mono hbor) (iSup₂_le fun i hi =>
        Subgroup.map_mono ?_))
      have hik : i ≠ k := fun h => hk (h ▸ hi)
      exact rankOneD_le_stabSub (K := F) hn3 c i (nodeCowt_node n k i hik (by omega))
    have hAgunit : IsUnit ((Ag : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := (Ag : GL (Fin n ⊕ Fin n) F).isUnit
    have hAginj : Function.Injective (Matrix.mulVecLin ((Ag : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) :=
      Matrix.mulVec_injective_iff_isUnit.mpr hAgunit
    refine ⟨(flagSpace F c).map (Matrix.mulVecLin ((Ag : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)), ?_, ?_, ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      rw [Matrix.mulVecLin_apply, preserves_of_mem_statedOmega Ag.2,
        ← congrFun (coe_quadPlus n F) v]
      exact quadPlus_flagSpace c hv
    · intro hk0'
      rw [← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hAginj _)]
      refine two_le_finrank_flagSpace hn c ?_ ?_
      · exact one_le_nodeCowt_of_ne n hn k hk0' _ (by simp)
      · exact one_le_nodeCowt_of_ne n hn k hk0' _ (by simp)
    · intro y hy A hA w hw
      obtain ⟨x, hx, rfl⟩ := hJle hy
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
      rw [Matrix.mulVecLin_apply]
      have hek : (QuotientGroup.mk A : StatedProj (StatedOmega (StatedQuadPlus n F))) =
          QuotientGroup.mk (Ag * genΩ hn3 x * Ag⁻¹) := by rw [hA, hπx]
      obtain ⟨d, hd⟩ := exists_smul_mulVec_of_mk_eq' hek
      rw [hd]
      refine Submodule.smul_mem _ _ ⟨spinMatrix (quadPlus n F) x *ᵥ v, ?_, ?_⟩
      · rw [spinMatrix_mulVec]
        exact hx v hv
      · simp only [Matrix.mulVecLin_apply, genΩ]
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
          ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        congr 2
        rw [Subgroup.coe_inv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
          Units.val_one, Matrix.one_mulVec]
  · intro i hi
    have hLi := Subgroup.map_mono (rankOne_le_of_mem_negIndices hBA hi) |>.trans
      (Subgroup.map_comap_le _ _)
    have h1 : π' (rootD F hn3 i (.ofAdd 1)) ∈ J := by
      refine hLi ⟨rootD F hn3 i (.ofAdd 1), ?_, rfl⟩
      change _ ∈ plusRootGroup n F hn3 (Pi.single i 1) ⊔ plusRootGroup n F hn3 (-Pi.single i 1)
      rw [plusRootGroup_single hn3 i]
      exact Subgroup.mem_sup_left ⟨_, rfl⟩
    have h2 : π' (negRootD F hn3 i (.ofAdd 1)) ∈ J := by
      refine hLi ⟨negRootD F hn3 i (.ofAdd 1), ?_, rfl⟩
      change _ ∈ plusRootGroup n F hn3 (Pi.single i 1) ⊔ plusRootGroup n F hn3 (-Pi.single i 1)
      refine Subgroup.mem_sup_right ?_
      have hh := plusRootGroup_neg_single (K := F) hn3 i
      exact (SetLike.ext_iff.mp hh _).mpr ⟨_, rfl⟩
    refine ⟨?_, ?_⟩
    · have := hπx (rootD F hn3 i (.ofAdd 1))
      have h1' : e.symm (QuotientGroup.mk (Ag * genΩ hn3 (rootD F hn3 i (.ofAdd 1)) * Ag⁻¹)) ∈ J := by
        rw [← this, MulEquiv.symm_apply_apply]
        exact h1
      exact h1'
    · have := hπx (negRootD F hn3 i (.ofAdd 1))
      have h2' : e.symm (QuotientGroup.mk (Ag * genΩ hn3 (negRootD F hn3 i (.ofAdd 1)) * Ag⁻¹)) ∈ J := by
        rw [← this, MulEquiv.symm_apply_apply]
        exact h2
      exact h2'

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualD
