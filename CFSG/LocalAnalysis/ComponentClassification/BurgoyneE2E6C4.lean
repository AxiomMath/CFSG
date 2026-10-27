module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Outer
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Odd
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E6GraphConj

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.LieType.Chevalley.E6SignedGraph
open CFSG.ComponentClassification.CatLeafProof (rootChar_single')
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.HighestRoot (rankOneGroup rankOneGroup_adjDatum)

@[expose] def e6GammaC4 : List ((Fin TwistTag.E6.tag.rank → ℤ) × ℤ) :=
  [(![0, 0, 0, 1, 0, 0], 5), (![0, 0, 1, 1, 1, 0], 3), (![1, 0, 1, 1, 1, 1], 2),
    (![1, 2, 2, 3, 2, 1], 1)]

theorem e6GammaC4_reg : ∀ α ∈ rootFinset TwistTag.E6.tag,
    (∑ j, regCoweight e6GammaC4 j * α j) ≠ 0 ∧
      (∑ j, regCoweight e6GammaC4 j * α j).natAbs < 12 := by
  decide +kernel

theorem e6GammaC4_check : ∀ y ∈ e6GammaC4, ∀ γ ∈ [y.1, -y.1],
    γ ∈ rootFinset TwistTag.E6.tag ∧ keep γ = true ∧ rho γ = γ := by
  decide +kernel

@[expose] def e6Theta : E6Vec :=
  ![1, 2, 2, 3, 2, 1]

theorem e6Theta_check : ∀ γ ∈ [e6Theta, -e6Theta],
    γ ∈ rootFinset TwistTag.E6.tag ∧ keep γ = true ∧ rho γ = γ := by
  decide +kernel

theorem e6Alpha4_check : ∀ γ ∈ [(Pi.single ⟨3, by decide⟩ 1 : E6Vec), -Pi.single ⟨3, by decide⟩ 1],
    γ ∈ rootFinset TwistTag.E6.tag ∧ keep γ = true ∧ rho γ = γ := by
  decide +kernel

theorem e6_pair_cover : ∀ j : Fin TwistTag.E6.tag.rank, j ≠ ⟨1, by decide⟩ → j ≠ ⟨3, by decide⟩ →
    ∃ a : Fin TwistTag.E6.foldedTag.rank,
      TwistTag.E6.perm (TwistTag.E6.orbitMin a) ≠ TwistTag.E6.orbitMin a ∧
        (Pi.single (TwistTag.E6.orbitMin a) 1 : E6Vec) ⟨1, by decide⟩ = 0 ∧
        (j = TwistTag.E6.orbitMin a ∨ j = TwistTag.E6.perm (TwistTag.E6.orbitMin a)) := by
  decide +kernel

theorem orbitSign_one {K : Type} [Field K] {a : Fin TwistTag.E6.foldedTag.rank}
    (ha : (Pi.single (TwistTag.E6.orbitMin a) 1 : E6Vec) ⟨1, by decide⟩ = 0) :
    orbitSign K 1 a = 1 := by
  rw [orbitSign, one_smul, ha, zpow_zero]


theorem rootSubgroup_le_rootGenerated {K : Type} [Field K] {γ : E6Vec}
    (hγ : IsRoot TwistTag.E6.tag γ) (hk : keep γ = true) (hρ : rho γ = γ) :
    rootSubgroup TwistTag.E6.tag K γ ≤ rootGenerated K := by
  have hO : ({γ} : Finset E6Vec) ∈ orbits :=
    mem_orbits.2 ⟨γ, hγ, hk, by rw [diagramOrbit_eq, hρ, Finset.pair_eq_singleton]⟩
  obtain ⟨w, hw, a, he⟩ := exists_orbitImage_eq hO
  rcases orbit_pair_or_single a with ⟨h, ho, -⟩ | ⟨h, -, hword⟩
  · exfalso
    have hc := congrArg Finset.card he
    rw [orbitImage_pair ho, Finset.card_pair (smul_single_ne h w), Finset.card_singleton] at hc
    exact absurd hc (by decide)
  · intro g hg
    have hg' : g ∈ rootSpan TwistTag.E6.tag K (orbitImage w a : Set E6Vec) := by
      rw [he, Finset.coe_singleton, CFSG.LieType.Chevalley.rootSpan_singleton]
      exact hg
    rw [rootSpan_orbitImage] at hg'
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hg'
    obtain ⟨c, rfl⟩ := exists_eq_single hword hu
    refine range_orbitSL2_le_rootGenerated hw (he ▸ hO) ⟨uSL c, ?_⟩
    rw [orbitSL2_uSL_single w h c]
    rfl

theorem rootPair_le_rootGenerated {K : Type} [Field K] {γ : E6Vec}
    (h : ∀ v ∈ [γ, -γ], v ∈ rootFinset TwistTag.E6.tag ∧ keep v = true ∧ rho v = v) :
    rootSubgroup TwistTag.E6.tag K γ ⊔ rootSubgroup TwistTag.E6.tag K (-γ) ≤ rootGenerated K := by
  have h1 := h γ (by simp)
  have h2 := h (-γ) (by simp)
  exact sup_le (rootSubgroup_le_rootGenerated (mem_rootFinset.1 h1.1) h1.2.1 h1.2.2)
    (rootSubgroup_le_rootGenerated (mem_rootFinset.1 h2.1) h2.2.1 h2.2.2)

theorem xUnit_mul_xUnit_mem_rootGenerated {K : Type} [Field K]
    (a : Fin TwistTag.E6.foldedTag.rank)
    (h : TwistTag.E6.perm (TwistTag.E6.orbitMin a) ≠ TwistTag.E6.orbitMin a)
    (hs : orbitSign K 1 a = 1) (c : K) :
    xUnit TwistTag.E6.tag K (TwistTag.E6.orbitMin a) c *
      xUnit TwistTag.E6.tag K (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) c ∈
        rootGenerated K := by
  have hw : (1 : WeylGroup TwistTag.E6.tag) ∈ relWeylTwist TwistTag.E6 := one_mem _
  have hrange := (orbitFixed_orbitImage_upper (K := K) hw (a := a) fun h' => absurd h' h).2
  have hmem : orbitSL2 K 1 a (uSL c) ∈ orbitFixed K (orbitImage 1 a) := by
    rw [← SetLike.mem_coe, ← hrange]
    exact ⟨c, rfl⟩
  have hS := orbitFixed_le_rootGenerated (orbitImage_sign hw a) hmem
  rwa [orbitSL2_uSL_pair 1 h c, canonicalRep_one, hs, Units.val_one, one_mul, one_mul, inv_one,
    mul_one] at hS

theorem eq_one_of_rootDiagAut_fix_pair {K : Type} [Field K]
    {e : Fin TwistTag.E6.tag.rank → Kˣ} (a : Fin TwistTag.E6.foldedTag.rank)
    (h : TwistTag.E6.perm (TwistTag.E6.orbitMin a) ≠ TwistTag.E6.orbitMin a)
    (hs : orbitSign K 1 a = 1)
    (hfix : ∀ u : adjointGroup TwistTag.E6.tag K, (u : ModGL TwistTag.E6.tag K) ∈ rootGenerated K →
      rootDiagAut TwistTag.E6.tag K e u = u) :
    e (TwistTag.E6.orbitMin a) = 1 ∧ e (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) = 1 := by
  set i := TwistTag.E6.orbitMin a with hi
  set j := TwistTag.E6.perm i with hj
  have hS := xUnit_mul_xUnit_mem_rootGenerated (K := K) a h hs 1
  have hC : xUnit TwistTag.E6.tag K i 1 * xUnit TwistTag.E6.tag K j 1 ∈
      adjointGroup TwistTag.E6.tag K := (rootGenerated_le_fixedGroup.trans inf_le_left) hS
  have h1 := congrArg Subtype.val (hfix ⟨_, hC⟩ hS)
  rw [coe_rootDiagAut] at h1
  set d := rootDiagUnit TwistTag.E6.tag e with hd
  have hconj : d * (xUnit TwistTag.E6.tag K i 1 * xUnit TwistTag.E6.tag K j 1) * d⁻¹ =
      xUnit TwistTag.E6.tag K i (e i : K) * xUnit TwistTag.E6.tag K j (e j : K) := by
    calc d * (xUnit TwistTag.E6.tag K i 1 * xUnit TwistTag.E6.tag K j 1) * d⁻¹ =
        (d * pinnedX TwistTag.E6.tag K (Pi.single i 1) 1 * d⁻¹) *
          (d * pinnedX TwistTag.E6.tag K (Pi.single j 1) 1 * d⁻¹) := by
          rw [pinnedX_single, pinnedX_single]
          group
      _ = _ := by
          rw [hd, rootDiagUnit_conj_pinnedX e (isRoot_single _ i),
            rootDiagUnit_conj_pinnedX e (isRoot_single _ j), rootChar_single', rootChar_single',
            mul_one, mul_one, pinnedX_single, pinnedX_single]
  rw [hconj] at h1
  rcases orbit_pair_or_single a with ⟨-, -, hword⟩ | ⟨h', -, -⟩
  · have hp := pair_eq_pair hword (Ne.symm h) h1
    exact ⟨Units.ext hp.1, Units.ext hp.2⟩
  · exact absurd h' h

theorem burgCoreFor_E6_signedGraph {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2) :
    BurgCoreFor (rootDiagAut TwistTag.E6.tag K (e6GraphSign K) * diagramConjAut TwistTag.E6 K) := by
  classical
  set α := rootDiagAut TwistTag.E6.tag K (e6GraphSign K) * diagramConjAut TwistTag.E6 K
    with hαdef
  have hA : twistA K =
      rootDiagUnit TwistTag.E6.tag (e6GraphSign K) * diagramMap TwistTag.E6 K := rfl
  have hαapp : ∀ g : adjointGroup TwistTag.E6.tag K,
      (α g : ModGL TwistTag.E6.tag K) = twistA K * g * (twistA K)⁻¹ := by
    intro g
    rw [hαdef, MulAut.mul_apply, coe_rootDiagAut, coe_diagramConjAut, hA, mul_inv_rev]
    group
  have hmemF : ∀ g : adjointGroup TwistTag.E6.tag K,
      g ∈ fixedSubgroup α ↔ (g : ModGL TwistTag.E6.tag K) ∈ fixedGroup K := by
    intro g
    rw [mem_fixedGroup]
    change α g = g ↔ _
    rw [← Subtype.coe_inj, hαapp, mul_inv_eq_iff_eq_mul]
    exact ⟨fun h => ⟨g.2, h.symm⟩, fun h => h.2.symm⟩
  have hSle : rootGenerated K ≤ adjointGroup TwistTag.E6.tag K :=
    rootGenerated_le_fixedGroup.trans inf_le_left
  set J := (rootGenerated K).subgroupOf (adjointGroup TwistTag.E6.tag K) with hJ
  have hJq : IsQuasisimple J := by
    obtain ⟨-, -, hq, -⟩ := E6_signed_graph_fixed_root_group_quasisimple K hK
    exact LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSle).symm hq
  refine burgCoreFor_of_normal_quasisimple (center_adjointGroup_eq_bot_field _ K) (J := J)
    (fun j hj => (hmemF j).2 (rootGenerated_le_fixedGroup hj)) (fun g hg j hj => ?_) hJq
    fun β hβ hfix => ?_
  ·
    rw [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (mem_normalizer_iff.1 (fixedGroup_le_normalizer hK ((hmemF g).1 hg)) _).1 hj
  have hfixS : ∀ u : adjointGroup TwistTag.E6.tag K, (u : ModGL TwistTag.E6.tag K) ∈
      rootGenerated K → β u = u := fun u hu => hfix u hu
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
  have hd2 : orderOf (rootDiagAut TwistTag.E6.tag K e) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have h1 : orderOf (rootDiagAut TwistTag.E6.tag K e) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hd2 with h | h
    · exact h
    · rw [h] at hβ
      exact absurd hβ (by decide)
  exact orderOf_eq_one_iff.1 h1

end CFSG.ComponentClassification.Burgoyne.E2
