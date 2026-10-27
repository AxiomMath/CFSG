module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofKleinSix
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthLow
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentAssemble
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentScaled
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentSimilarity

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.KleinSix

open Matrix QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K]

theorem eichler_swap {u w : Fin 3 ⊕ Fin 3 → K} (hu : quadPlus 3 K u = 0)
    (hw : quadPlus 3 K w = 0) (huw : polar (quadPlus 3 K) u w = 0) (c : K) :
    eichler (quadPlus 3 K) w (c • u) = eichler (quadPlus 3 K) u ((-c) • w) := by
  have hwu : polar (quadPlus 3 K) w u = 0 := by rw [polar_comm, huw]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply hw (by rw [polar_smul_right, hwu, smul_zero]),
    eichler_apply hu (by rw [polar_smul_right, huw, smul_zero])]
  simp only [polar_smul_right, QuadraticMap.map_smul, hu, hw, smul_eq_mul, mul_zero, zero_mul,
    add_zero]
  module

theorem eq_zero_of_polar_plusVec {v : Fin 3 ⊕ Fin 3 → K}
    (h : ∀ k r, polar (quadPlus 3 K) v (plusVec 3 K k r) = 0) : v = 0 := by
  funext x
  rcases x with k | k
  · have := h k false
    rwa [plusVec_false, polar_quadPlus_single_inr] at this
  · have := h k true
    rwa [plusVec_true, polar_quadPlus_single_inl] at this

theorem elementaryGroup_le_range :
    elementaryGroup (quadPlus 3 K) ≤ (rhoGL (K := K)).range := by
  refine (plusFrame 3 K le_rfl).elementaryGroup_le (fun {i j} hij s t c => ?_)
    (fun i s v hv => ?_) (fun v hv _ => eq_zero_of_polar_plusVec hv)
  · change eichler (quadPlus 3 K) (plusVec 3 K j t) (c • plusVec 3 K i s) ∈ _
    have hsw : eichler (quadPlus 3 K) (plusVec 3 K j t) (c • plusVec 3 K i s) =
        eichler (quadPlus 3 K) (plusVec 3 K i s) ((-c) • plusVec 3 K j t) :=
      eichler_swap (quadPlus_plusVec 3 K i s) (quadPlus_plusVec 3 K j t)
        (by rw [polar_quadPlus_plusVec]; exact ite_eq_right_iff.mpr fun h => absurd h.1 hij) c
    fin_cases i <;> fin_cases j <;> cases s <;> cases t
    · exact absurd rfl hij
    · exact absurd rfl hij
    · exact absurd rfl hij
    · exact absurd rfl hij
    · rw [hsw]
      exact ⟨_, rho_transv_30 (-c)⟩
    · rw [hsw]
      exact ⟨_, rho_transv_21 (-c)⟩
    · exact ⟨_, rho_transv_12 c⟩
    · exact ⟨_, rho_transv_03 c⟩
    · exact ⟨_, rho_transv_20 c⟩
    · rw [hsw]
      exact ⟨_, rho_transv_31 (-c)⟩
    · exact ⟨_, rho_transv_13 c⟩
    · rw [hsw]
      exact ⟨_, rho_transv_02 (-c)⟩
    · exact ⟨_, rho_transv_30 c⟩
    · rw [hsw]
      exact ⟨_, rho_transv_12 (-c)⟩
    · exact ⟨_, rho_transv_21 c⟩
    · rw [hsw]
      exact ⟨_, rho_transv_03 (-c)⟩
    · exact absurd rfl hij
    · exact absurd rfl hij
    · exact absurd rfl hij
    · exact absurd rfl hij
    · rw [hsw]
      exact ⟨_, rho_transv_10 (-c)⟩
    · rw [hsw]
      exact ⟨_, rho_transv_32 (-c)⟩
    · exact ⟨_, rho_transv_23 c⟩
    · exact ⟨_, rho_transv_01 c⟩
    · rw [hsw]
      exact ⟨_, rho_transv_20 (-c)⟩
    · rw [hsw]
      exact ⟨_, rho_transv_13 (-c)⟩
    · exact ⟨_, rho_transv_31 c⟩
    · exact ⟨_, rho_transv_02 c⟩
    · exact ⟨_, rho_transv_10 c⟩
    · rw [hsw]
      exact ⟨_, rho_transv_23 (-c)⟩
    · exact ⟨_, rho_transv_32 c⟩
    · rw [hsw]
      exact ⟨_, rho_transv_01 (-c)⟩
    · exact absurd rfl hij
    · exact absurd rfl hij
    · exact absurd rfl hij
    · exact absurd rfl hij
  · rw [eq_zero_of_polar_plusVec hv, eichler_zero_right]
    exact one_mem _


theorem range_le_orthogonalGroup :
    (rhoGL (K := K)).range ≤ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K) := by
  rintro _ ⟨g, rfl⟩
  exact rhoGL_mem_orthogonalGroup g

theorem quadPlus_nondegenerate : (polarBilin (quadPlus 3 K)).Nondegenerate :=
  ⟨fun v hv => eq_zero_of_polar_plusVec fun k r => hv _,
    fun v hv => eq_zero_of_polar_plusVec fun k r => by
      rw [polar_comm]
      exact hv _⟩

@[expose] noncomputable def singularT : Submodule K (Fin 3 ⊕ Fin 3 → K) :=
  LinearMap.ker (LinearMap.funLeft K K (Sum.inr : Fin 3 → Fin 3 ⊕ Fin 3))

theorem singularT_singular (x : Fin 3 ⊕ Fin 3 → K) (hx : x ∈ singularT) : quadPlus 3 K x = 0 := by
  have h : ∀ i, x (.inr i) = 0 := fun i => congrFun (LinearMap.mem_ker.mp hx) i
  rw [quadPlus_apply]
  simp [h]

theorem finrank_singularT : Module.finrank K (singularT (K := K)) = 3 := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.funLeft K K (Sum.inr : Fin 3 → Fin 3 ⊕ Fin 3))
  have h1 : Module.finrank K
      (LinearMap.range (LinearMap.funLeft K K (Sum.inr : Fin 3 → Fin 3 ⊕ Fin 3))) = 3 := by
    rw [LinearMap.range_eq_top.mpr (LinearMap.funLeft_surjective_of_injective _ _ _
      Sum.inr_injective), finrank_top, Module.finrank_fin_fun]
  have h2 : Module.finrank K (Fin 3 ⊕ Fin 3 → K) = 6 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  unfold singularT
  omega

open CFSG.ComponentClassification.CatalogueBOrthogonal in
theorem range_eq_elementaryGroup [Finite K] (h2 : (2 : K) ≠ 0) :
    (rhoGL (K := K)).range = elementaryGroup (quadPlus 3 K) := by
  refine le_antisymm ?_ elementaryGroup_le_range
  have hSL := CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 4 K
    (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))
  have hperf : commutator (Matrix.SpecialLinearGroup (Fin 4) K) = ⊤ :=
    Group.isPerfect_def.mp hSL.1
  calc (rhoGL (K := K)).range = (commutator (Matrix.SpecialLinearGroup (Fin 4) K)).map rhoGL := by
        rw [hperf, ← MonoidHom.range_eq_map]
    _ = ⁅(rhoGL (K := K)).range, (rhoGL (K := K)).range⁆ := map_commutator_eq (f := rhoGL)
    _ ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K),
          TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)⁆ :=
        Subgroup.commutator_mono range_le_orthogonalGroup range_le_orthogonalGroup
    _ = elementaryGroup (quadPlus 3 K) := by
        rw [← Subgroup.map_subtype_commutator]
        exact derived_map_eq_elementary _ h2 quadPlus_nondegenerate
          (finrank_singularT.ge) singularT_singular


open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatalogueBOrthogonal CFSG.Assembly.LowTwoRank in
theorem quadPlus_three_component [Finite K] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = p ^ e)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K))}
    (hM : CFSG.IsComponent M) : OddLieCentralQuotient p M := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hq := derived_quasisimple (quadPlus 3 K) h2 quadPlus_nondegenerate finrank_singularT.ge
    singularT_singular
  have hMeq := eq_commutator_of_isComponent hq hM
  have hmap := derived_map_eq_elementary (quadPlus 3 K) h2 quadPlus_nondegenerate
    finrank_singularT.ge singularT_singular
  have hrange := range_eq_elementaryGroup (K := K) h2
  let eD : commutator (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)) ≃*
      (rhoGL (K := K)).range :=
    ((commutator (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K))).equivMapOfInjective
      (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)).subtype
      (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)).subtype_injective).trans
      (MulEquiv.subgroupCongr (hmap.trans hrange.symm))
  let eM : M ≃* (rhoGL (K := K)).range := (MulEquiv.subgroupCongr hMeq).trans eD
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 4 K (by norm_num)
    (Or.inl (by norm_num)) (Or.inl (by norm_num))
  have hrq : CFSG.IsQuasisimple (rhoGL (K := K)).range :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eD hq
  obtain ⟨eS⟩ := nonempty_centerQuotient_equiv_range hSL rhoGL (ne_bot_of_isQuasisimple hrq)
  let eTot : M ⧸ Subgroup.center M ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) K :=
    (QuotientGroup.congr _ _ eM (Subgroup.map_center_eq eM)).trans eS.symm
  have hadm : StatedLieAdmissible .PSL 4 p e :=
    ⟨hp, he, by norm_num, fun h => by have := (Prod.mk.inj h).1; omega,
      fun h => by have := (Prod.mk.inj h).1; omega⟩
  exact ⟨.PSL, 4, e, hadm, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eTot.symm
    (Or.inl ⟨by decide, ⟨hadm, K, inferInstance, inferInstance, hK,
      ⟨projectiveSpecialLinearGroupEquivStatedProj 4 K⟩⟩⟩)⟩

open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.RankThree.PartOne.KCOrthogonalDescent CFSG.Assembly.LowTwoRank in
theorem split_six_component {k W : Type} [Field k] [Finite k] [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hk : Nat.card k = p ^ e) (Q₀ : QuadraticForm k W) (hQ₀ : Q₀.polarBilin.Nondegenerate)
    (hdim : Module.finrank k W = 6)
    (hT : ∃ T : Submodule k W, Module.finrank k T = 3 ∧ ∀ x ∈ T, Q₀ x = 0)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q₀)} (hM : CFSG.IsComponent M) :
    OddLieCentralQuotient p M := by
  obtain ⟨m, δ, hδ, ⟨H⟩⟩ := exists_regular_split Q₀ hQ₀
  have hfin := H.finrank_eq
  have hwitt := H.sourceWittIndex_eq hQ₀
  obtain ⟨T, hTdim, hTQ⟩ := hT
  have h3 := CFSG.Blueprint.EvenSource.le_sourceWittIndex (K := k) (V := W) (⇑Q₀) (W := T) hTQ
  have hm : m = 3 := by omega
  have hδ0 : δ = 0 := by omega
  have H' : HypSplit Q₀ 3 0 := by rw [← hm, ← hδ0]; exact H
  let bk := H'.b.reindex (HypSplit.plusEquiv 3)
  have hS : ∀ w, quadPlus 3 k (bk.equivFun w) = ((1 : kˣ) : k) * Q₀ w := fun w => by
    rw [Units.val_one, one_mul, show quadPlus 3 k (bk.equivFun w) =
      StatedQuadPlus 3 k (bk.equivFun w) from congrFun (coe_quadPlus 3 k) _]
    exact H'.displayPlus w
  let eO : TauCeti.QuadraticMap.orthogonalGroup Q₀ ≃*
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 k) :=
    ((TauCeti.QuadraticMap.orthogonalGroup Q₀).equivMapOfInjective
      (linConj bk.equivFun).toMonoidHom (linConj bk.equivFun).injective).trans
      (MulEquiv.subgroupCongr (map_orthogonalGroup bk.equivFun 1 hS))
  have hM' := CFSG.LocalCores.isComponent_map_mulEquiv eO hM
  exact oddLieCentralQuotient_of_mulEquiv (M.equivMapOfInjective eO.toMonoidHom eO.injective)
    (quadPlus_three_component hp hp2 he hk hM')

end CFSG.ComponentClassification.CatLeafProof.KleinSix
