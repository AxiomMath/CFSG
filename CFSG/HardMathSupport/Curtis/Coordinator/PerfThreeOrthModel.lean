module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelSylow

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit Matrix

section

variable {K : Type} [Field K]

theorem eq_zero_or_one_of_card_two' (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  by_contra! h
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
  exact h.2 ((hy c h.1).trans (hy 1 one_ne_zero).symm)

theorem statedScalars_eq_bot (hK : Nat.card K = 2) {ι : Type} [Fintype ι] [DecidableEq ι] :
    StatedScalars ι K = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨u, rfl⟩
  have hu : u = 1 := by
    apply Units.ext
    rcases eq_zero_or_one_of_card_two' hK (u : K) with h | h
    · exact absurd h u.ne_zero
    · exact h
  rw [hu, map_one]
  exact Subgroup.one_mem _

variable (K) in
@[expose] noncomputable def scalarQuot (hK : Nat.card K = 2) (n : ℕ) :
    StatedOmega (StatedQuadPlus n K) ≃* StatedProj (StatedOmega (StatedQuadPlus n K)) :=
  MulEquiv.ofBijective
    (QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf
      (StatedOmega (StatedQuadPlus n K))))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by
        rw [QuotientGroup.ker_mk', statedScalars_eq_bot hK, Subgroup.bot_subgroupOf]),
      QuotientGroup.mk'_surjective _⟩

theorem scalarQuot_symm_mk (hK : Nat.card K = 2) (n : ℕ) (A : StatedOmega (StatedQuadPlus n K)) :
    (scalarQuot K hK n).symm (QuotientGroup.mk A) = A :=
  (scalarQuot K hK n).symm_apply_apply A

variable (K) in
@[expose] noncomputable def projEquivElementary (hK : Nat.card K = 2) {n : ℕ} (hn : 3 ≤ n) :
    StatedProj (StatedOmega (StatedQuadPlus n K)) ≃* ↥(elementaryGroup (quadPlus n K)) :=
  (scalarQuot K hK n).symm.trans
    (statedOmegaEquiv (coe_quadPlus n K) (commutator_orthogonalGroup_quadPlus hn))

theorem projEquivElementary_mk (hK : Nat.card K = 2) {n : ℕ} (hn : 3 ≤ n)
    (A : StatedOmega (StatedQuadPlus n K)) :
    projEquivElementary K hK hn (QuotientGroup.mk A) =
      statedOmegaEquiv (coe_quadPlus n K) (commutator_orthogonalGroup_quadPlus hn) A := by
  simp only [projEquivElementary, MulEquiv.trans_apply, scalarQuot_symm_mk]

theorem coe_projEquivElementary_mk (hK : Nat.card K = 2) {n : ℕ} (hn : 3 ≤ n)
    (A : StatedOmega (StatedQuadPlus n K)) :
    ((projEquivElementary K hK hn (QuotientGroup.mk A) : ↥(elementaryGroup (quadPlus n K))) :
      (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) = toLinEquiv (Fin n ⊕ Fin n) K A :=
  by rw [projEquivElementary_mk]; rfl

theorem mem_borel_of_stab (hK : Nat.card K = 2) {n : ℕ} (hn : 3 ≤ n)
    (ε : ↥(elementaryGroup (quadPlus n K)))
    (h : ∀ i, (stdFlag n K i).map (ε : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)).toLinearMap =
      stdFlag n K i) :
    (projEquivElementary K hK hn).symm ε ∈ plusProjectiveBorel n K := by
  set A := (statedOmegaEquiv (coe_quadPlus n K) (commutator_orthogonalGroup_quadPlus hn)).symm ε
    with hA
  have hε : (projEquivElementary K hK hn) (QuotientGroup.mk A) = ε := by
    rw [projEquivElementary_mk, hA, MulEquiv.apply_symm_apply]
  have : (projEquivElementary K hK hn).symm ε = QuotientGroup.mk A := by
    rw [MulEquiv.symm_apply_eq, hε]
  rw [this, plusProjectiveBorel, statedProjectiveFlagStabilizer, Subgroup.mem_iInf]
  intro i
  refine (mem_statedProjectiveSubspaceStabilizer_mk (StatedQuadPlus n K) (stdFlag n K i) A).mpr ?_
  rw [mem_statedDerivedSubspaceStabilizer]
  have h2 := h i
  have h3 : toLinEquiv (Fin n ⊕ Fin n) K A.val =
      (ε : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) := by
    rw [← coe_projEquivElementary_mk hK hn A]
    rw [hε]
  rw [h3]
  exact h2

end

section Eichler

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem map_eichler_eq_of_totSingular {U : Submodule K V} (hU : ∀ x ∈ U, Q x = 0) {e : V}
    (he : e ∈ U) (y : V) : U.map (eichler Q e y).toLinearMap = U := by
  have hle : U.map (eichler Q e y).toLinearMap ≤ U := by
    rintro _ ⟨x, hx, rfl⟩
    by_cases h : Q e = 0 ∧ polar Q e y = 0
    · have hxe : polar Q x e = 0 := by
        rw [polar, hU _ (U.add_mem hx he), hU _ hx, hU _ he]
        simp
      change eichler Q e y x ∈ U
      rw [eichler_apply h.1 h.2, hxe, zero_smul, add_zero]
      exact U.sub_mem hx (U.smul_mem _ he)
    · change eichler Q e y x ∈ U
      rw [eichler_of_not h]
      exact hx
  exact Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq _ _)

end Eichler

section Sylow

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_conj_borel_le {G : Type} [Group G] [Finite G] {n : ℕ} (hn : 3 ≤ n)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) (T : Sylow 2 G) (J : Subgroup G)
    (hNJ : Subgroup.normalizer ((T : Subgroup G) : Set G) ≤ J) :
    ∃ x : StatedProj (StatedOmega (StatedQuadPlus n K)),
      ∀ b ∈ plusProjectiveBorel n K, x * b * x⁻¹ ∈ J.map e.toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀⟩ := plusProjectiveUnipotent_isSylow n K 2 hn
  set TP : Sylow 2 (StatedProj (StatedOmega (StatedQuadPlus n K))) :=
    T.mapSurjective (f := e.toMonoidHom) e.surjective with hTP
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (StatedProj (StatedOmega (StatedQuadPlus n K))) S₀ TP
  refine ⟨x, fun b hb => ?_⟩
  have hN : Subgroup.normalizer ((S₀ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))) :
      Set (StatedProj (StatedOmega (StatedQuadPlus n K)))) = plusProjectiveBorel n K := by
    rw [hS₀]
    exact plusProjectiveUnipotent_normalizer n K hn
  have hTPeq : (TP : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))) =
      (S₀ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))).map
        (MulAut.conj x).toMonoidHom := by
    rw [← hx, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hNTP : Subgroup.normalizer ((TP : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))) :
      Set (StatedProj (StatedOmega (StatedQuadPlus n K)))) =
      (plusProjectiveBorel n K).map (MulAut.conj x).toMonoidHom := by
    rw [hTPeq, ← hN, Subgroup.map_equiv_normalizer_eq]
  have hTe : (TP : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))) =
      (T : Subgroup G).map e.toMonoidHom := by
    rw [hTP]
    exact Sylow.coe_mapSurjective _ T
  have hNe : Subgroup.normalizer ((TP : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))) :
      Set (StatedProj (StatedOmega (StatedQuadPlus n K)))) =
      (Subgroup.normalizer ((T : Subgroup G) : Set G)).map e.toMonoidHom := by
    rw [hTe, ← Subgroup.map_equiv_normalizer_eq]
  have hmem : (MulAut.conj x) b ∈ Subgroup.normalizer ((TP : Subgroup
      (StatedProj (StatedOmega (StatedQuadPlus n K)))) :
      Set (StatedProj (StatedOmega (StatedQuadPlus n K)))) := by
    rw [hNTP]
    exact ⟨b, hb, rfl⟩
  rw [hNe] at hmem
  obtain ⟨j, hj, hjb⟩ := hmem
  rw [MulAut.conj_apply] at hjb
  exact ⟨j, hNJ hj, hjb⟩

end Sylow

section Count

variable {K : Type} [Field K] [Finite K]

theorem card_singular_quadPlus_four (hK : Nat.card K = 2) :
    Nat.card {v : Fin 4 ⊕ Fin 4 → K // quadPlus 4 K v = 0} = 136 := by
  have : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  let e : ZMod 2 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_two hq
  let e₀ : (Fin 4 ⊕ Fin 4 → ZMod 2) ≃ (Fin 4 ⊕ Fin 4 → K) :=
    Equiv.arrowCongr (Equiv.refl _) e.toEquiv
  have key : {v : Fin 4 ⊕ Fin 4 → ZMod 2 // ∑ i : Fin 4, v (.inl i) * v (.inr i) = 0} ≃
      {v : Fin 4 ⊕ Fin 4 → K // quadPlus 4 K v = 0} := by
    refine Equiv.subtypeEquiv e₀ fun v => ?_
    rw [quadPlus_apply]
    simp only [e₀, Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.refl_apply,
      Function.comp_apply, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ← map_mul]
    rw [← map_sum, map_eq_zero_iff e e.injective]
  rw [← Nat.card_congr key, Nat.card_eq_fintype_card]
  decide +kernel

end Count

end CFSG.HardMathSupport.Curtis.Coordinator
