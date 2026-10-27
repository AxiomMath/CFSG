module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcE6
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcToral
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E6C4

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup

theorem outerCoreTrivAt_of_normal_quasisimple {T : Type} [Group T] [Finite T]
    (hZ : center T = ⊥) {i : MulAut T} {J : Subgroup T} (hJi : ∀ j ∈ J, i j = j)
    (hJn : ∀ s : T, i s = s → ∀ j ∈ J, s * j * s⁻¹ ∈ J) (hJq : CFSG.IsQuasisimple J)
    (hfix : ∀ β : MulAut T, Odd (orderOf β) → (∀ j ∈ J, β j = j) → β = 1) :
    OuterCoreTrivAt i := by
  intro R hRodd hRi hRc r hr
  have hTfix : ∀ t ∈ oddFixed i, i t = t := by
    have hle : oddFixed i ≤ i.toMonoidHom.eqLocus (MonoidHom.id _) := by
      rw [oddFixed, closure_le]
      rintro s ⟨hs, -⟩
      exact hs
    exact fun t ht => hle ht
  have hJN : (J.subgroupOf (oddFixed i)).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hJn _ (hTfix _ g.2) _ (mem_subgroupOf.1 hn)⟩
  have hcomp : GorensteinWalter.IsComponentOf J (oddFixed i) := by
    refine ⟨(le_oddClosure_of_perfect le_rfl hJq.1.commutator_eq_top).trans (closure_mono ?_),
      hJN.isSubnormal, gw_isQuasisimple_of_isQuasisimple hJq⟩
    rintro g ⟨hgJ, hgo⟩
    exact ⟨hJi g hgJ, hgo⟩
  exact hfix r (odd_orderOf_of_mem hRodd hr) fun j hj =>
    fix_of_isComponentOf hRi hRc hZ hRodd hr hcomp hj

section SignedGraph

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits
  CFSG.Timmesfeld CFSG.LieType.Chevalley.E6SignedGraph
open CFSG.ComponentClassification.CatLeafProof (rootChar_single')
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)
open CFSG.LieType.HighestRoot (rankOneGroup rankOneGroup_adjDatum)
open CFSG.ComponentClassification.Burgoyne.E2 (rootPair_le_rootGenerated e6Alpha4_check e6GammaC4
  e6GammaC4_check e6GammaC4_reg e6Theta e6Theta_check e6_pair_cover
  eq_one_of_rootDiagAut_fix_pair orbitSign_one exists_eq_rootDiagAut_of_odd_fix
  rootChar_eq_one_of_fix_pinnedX)

theorem eq_one_of_odd_fix_rootGenerated
    {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2)
    {β : MulAut (adjointGroup TwistTag.E6.tag K)} (hβ : Odd (orderOf β))
    (hfixS : ∀ u : adjointGroup TwistTag.E6.tag K, (u : ModGL TwistTag.E6.tag K) ∈
      rootGenerated K → β u = u) : β = 1 := by
  set k4 : Fin TwistTag.E6.tag.rank := ⟨3, by decide⟩ with hk4
  have hk : ∀ x ∈ rankOne (adjDatum (rootOperatorFamily TwistTag.E6.tag) K).rootGroup k4,
      β x = x := by
    intro x hx
    change _ ∈ rankOneGroup (adjDatum (rootOperatorFamily TwistTag.E6.tag) K) (Pi.single k4 1)
      at hx
    rw [rankOneGroup_adjDatum _ (isRoot_single _ _), mem_subgroupOf] at hx
    exact hfixS x (rootPair_le_rootGenerated e6Alpha4_check hx)
  obtain ⟨e, rfl⟩ := exists_eq_rootDiagAut_of_odd_fix (τ := TwistTag.E6.tag) (Or.inl rfl) hK hβ k4
    hk e6GammaC4
    (fun y hy => mem_rootFinset.1 (e6GammaC4_check y hy y.1 (by simp)).1)
    (fun y hy u hu => hfixS u (rootPair_le_rootGenerated (e6GammaC4_check y hy) hu))
    12 (fun α hα => e6GammaC4_reg α (mem_rootFinset.2 hα))
  have hchar : ∀ γ : E6Vec, (∀ v ∈ [γ, -γ], v ∈ rootFinset TwistTag.E6.tag ∧ keep v = true ∧
      rho v = v) → rootChar e γ = 1 := by
    intro γ hγ
    have hγr : IsRoot TwistTag.E6.tag γ := mem_rootFinset.1 (hγ γ (by simp)).1
    refine rootChar_eq_one_of_fix_pinnedX hγr (hfixS _ (rootPair_le_rootGenerated hγ ?_))
    exact le_sup_left (a := rootSubgroup TwistTag.E6.tag K γ) (Subgroup.subset_closure ⟨1, rfl⟩)
  have he4 : e k4 = 1 := by
    rw [← rootChar_single' e k4]
    exact hchar _ e6Alpha4_check
  have hθ := hchar _ e6Theta_check
  have hpair : ∀ j : Fin TwistTag.E6.tag.rank, j ≠ ⟨1, by decide⟩ → j ≠ k4 → e j = 1 := by
    intro j hj1 hj3
    obtain ⟨a, h, ha, hj | hj⟩ := e6_pair_cover j hj1 hj3
    · rw [hj]
      exact (eq_one_of_rootDiagAut_fix_pair a h (orbitSign_one ha) hfixS).1
    · rw [hj]
      exact (eq_one_of_rootDiagAut_fix_pair a h (orbitSign_one ha) hfixS).2
  have hne1 : ∀ j : Fin TwistTag.E6.tag.rank, j ≠ ⟨1, by decide⟩ → e j = 1 := by
    intro j hj
    by_cases hj3 : j = k4
    · rw [hj3]
      exact he4
    · exact hpair j hj hj3
  have he1 : e ⟨1, by decide⟩ ^ 2 = 1 := by
    have hprod : rootChar e e6Theta = e ⟨1, by decide⟩ ^ (e6Theta ⟨1, by decide⟩) := by
      refine Finset.prod_eq_single _ (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ _) h)
      rw [hne1 b hb, one_zpow]
    have h2 : e6Theta ⟨1, by decide⟩ = 2 := by decide
    rw [hprod, h2, zpow_two] at hθ
    rw [sq]
    exact hθ
  have he2 : e ^ 2 = 1 := by
    funext j
    rw [Pi.pow_apply, Pi.one_apply]
    by_cases hj : j = ⟨1, by decide⟩
    · rw [hj]
      exact he1
    · rw [hne1 j hj, one_pow]
  have hsq : rootDiagAut TwistTag.E6.tag K e ^ 2 = 1 := by
    change rootDiagAutHom TwistTag.E6.tag K e ^ 2 = 1
    rw [← map_pow, he2, map_one]
  exact Exc.eq_one_of_odd_of_mem_zpowers hsq (mem_zpowers _) hβ

end SignedGraph

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Assembly.LowTwoRank

theorem outerCoreTrivAt_diagramConjAut_E6
    {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2) :
    OuterCoreTrivAt (diagramConjAut TwistTag.E6 K) := by
  classical
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have h1 : ∀ x : ModGL TwistTag.E6.tag K,
      Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x := fun x => Units.ext (entrywise_id _)
  obtain ⟨hJs0, hJna0, -⟩ := odd_diagram_field_fixed_p_components TwistTag.E6 K hK 1
  set C₀ := graphFixedRootGroup TwistTag.E6 K (1 : K ≃+* K).toRingHom with hC₀
  have hC₀Γ := graphFixedRootGroup_le TwistTag.E6 K (1 : K ≃+* K).toRingHom
  have hC₀C : C₀ ≤ adjointGroup TwistTag.E6.tag K :=
    hC₀Γ.trans (twistedFixedGroup_le_adjointGroup TwistTag.E6 K _)
  have hfixΓ : ∀ s : adjointGroup TwistTag.E6.tag K, diagramConjAut TwistTag.E6 K s = s ↔
      (s : ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K (1 : K ≃+* K).toRingHom := by
    intro s
    rw [mem_twistedFixedGroup_iff_twistHom, twistHom_apply, h1, ← coe_diagramConjAut,
      Subtype.coe_inj]
    exact ⟨fun h => ⟨s.2, h⟩, fun h => h.2⟩
  have hJq : CFSG.IsQuasisimple (C₀.subgroupOf (adjointGroup TwistTag.E6.tag K)) := by
    have := hJs0
    have hnab : ∃ a b : C₀, a * b ≠ b * a := hJna0
    exact LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hC₀C).symm
      (LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
  have hP2 : diagramMap TwistTag.E6 K * diagramMap TwistTag.E6 K = 1 := by
    have h := diagramMap_pow_order TwistTag.E6 K
    rwa [show TwistTag.E6.order = 2 from rfl, sq] at h
  have hγ2 : diagramConjAut TwistTag.E6 K ^ 2 = 1 := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [sq, MulAut.mul_apply, coe_diagramConjAut, coe_diagramConjAut, MulAut.one_apply]
    calc diagramMap TwistTag.E6 K * (diagramMap TwistTag.E6 K * (h : ModGL TwistTag.E6.tag K) *
          (diagramMap TwistTag.E6 K)⁻¹) * (diagramMap TwistTag.E6 K)⁻¹ =
        (diagramMap TwistTag.E6 K * diagramMap TwistTag.E6 K) * h *
          (diagramMap TwistTag.E6 K * diagramMap TwistTag.E6 K)⁻¹ := by group
      _ = h := by rw [hP2, one_mul, inv_one, mul_one]
  refine outerCoreTrivAt_of_normal_quasisimple center_adjointGroup_eq_bot
    (fun j hj => (hfixΓ j).2 (hC₀Γ hj)) (fun s hs j hj => ?_) hJq fun β hβ hfix => ?_
  ·
    have hsN := twistedFixedGroup_le_normalizer (t := TwistTag.E6)
      (σ := (1 : K ≃+* K).toRingHom) (1 : K ≃+* K).surjective ((hfixΓ s).1 hs)
    rw [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.1 hsN (j : ModGL TwistTag.E6.tag K)).1 hj
  ·
    have hmem := FieldGraphFieldPointwise.mem_zpowers_of_forall_graphFixedRootGroup
      (1 : K ≃+* K) (fun _ => rfl) (fun j hj => hfix j hj)
    rw [entrywiseAdjointAut_one, mul_one] at hmem
    exact Exc.eq_one_of_odd_of_mem_zpowers hγ2 hmem hβ

theorem outerCoreTrivAt_signedGraph_E6
    {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2) :
    OuterCoreTrivAt (rootDiagAut TwistTag.E6.tag K (Burgoyne.E2.e6GraphSign K) *
      diagramConjAut TwistTag.E6 K) := by
  classical
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hA : E6SignedGraph.twistA K = rootDiagUnit TwistTag.E6.tag (Burgoyne.E2.e6GraphSign K) *
      diagramMap TwistTag.E6 K := rfl
  have hαapp : ∀ g : adjointGroup TwistTag.E6.tag K,
      ((rootDiagAut TwistTag.E6.tag K (Burgoyne.E2.e6GraphSign K) * diagramConjAut TwistTag.E6 K)
        g : ModGL TwistTag.E6.tag K) =
        E6SignedGraph.twistA K * g * (E6SignedGraph.twistA K)⁻¹ := by
    intro g
    rw [MulAut.mul_apply, coe_rootDiagAut, coe_diagramConjAut, hA, mul_inv_rev]
    group
  have hmemF : ∀ g : adjointGroup TwistTag.E6.tag K,
      (rootDiagAut TwistTag.E6.tag K (Burgoyne.E2.e6GraphSign K) * diagramConjAut TwistTag.E6 K)
        g = g ↔ (g : ModGL TwistTag.E6.tag K) ∈ E6SignedGraph.fixedGroup K := by
    intro g
    rw [E6SignedGraph.mem_fixedGroup, ← Subtype.coe_inj, hαapp, mul_inv_eq_iff_eq_mul]
    exact ⟨fun h => ⟨g.2, h.symm⟩, fun h => h.2.symm⟩
  have hSle : E6SignedGraph.rootGenerated K ≤ adjointGroup TwistTag.E6.tag K :=
    E6SignedGraph.rootGenerated_le_fixedGroup.trans inf_le_left
  have hJq : CFSG.IsQuasisimple
      ((E6SignedGraph.rootGenerated K).subgroupOf (adjointGroup TwistTag.E6.tag K)) := by
    obtain ⟨-, -, hq, -⟩ := E6_signed_graph_fixed_root_group_quasisimple K hK
    exact LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSle).symm hq
  refine outerCoreTrivAt_of_normal_quasisimple center_adjointGroup_eq_bot
    (fun j hj => (hmemF j).2 (E6SignedGraph.rootGenerated_le_fixedGroup hj))
    (fun s hs j hj => ?_) hJq
    fun β hβ hfix => eq_one_of_odd_fix_rootGenerated hK hβ fun u hu => hfix u hu
  rw [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact (mem_normalizer_iff.1 (E6SignedGraph.fixedGroup_le_normalizer hK ((hmemF s).1 hs)) _).1 hj

theorem e6GraphCoreInput :
    E6GraphCoreInput := by
  intro K _ _ hK α hα g a hαg
  obtain ⟨p, f, hp, hp2, hf, hchar, hcard⟩ := exists_odd_prime_pow_card_of_odd hK
  have hK2 : ringChar K ≠ 2 := hchar ▸ hp2
  obtain ⟨ψ, hψ | hψ⟩ := Burgoyne.E2.exists_conj_eq_graph_of_graphCoset hK hαg hα
  · exact outerCoreAt_of_conj hψ (outerCoreTrivAt_diagramConjAut_E6 hK2).outerCoreAt
  · exact outerCoreAt_of_conj hψ (outerCoreTrivAt_signedGraph_E6 hK2).outerCoreAt

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
