module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ReeResidual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6LargeRee
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Residual

public section

namespace CFSG.QuasithinUnique.Setup.X6

open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.ABGLocalTools
open scoped Pointwise commutatorElement

section ReePos

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

variable (a K) in
@[expose] noncomputable def reePosWeylGroup
    (j : Fin F4.fixedOrbitCount) :
    Subgroup (ModGL F4.tag K) :=
  F4.reeFixedPosUnipotent K a ⊔
    Subgroup.closure {canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j)}

theorem reeFixedPosUnipotent_le_reePosWeylGroup
    (j : Fin F4.fixedOrbitCount) :
    F4.reeFixedPosUnipotent K a ≤ reePosWeylGroup K a j :=
  le_sup_left

theorem canonicalRep_mem_reePosWeylGroup
    (j : Fin F4.fixedOrbitCount) :
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈ reePosWeylGroup K a j :=
  Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_singleton _))

theorem reeLocalBlock_le_reePosWeylGroup
    (j : Fin F4.fixedOrbitCount) :
    F4.reeLocalBlock K a j ≤ reePosWeylGroup K a j :=
  sup_le ((reeFixedOrbitUnipotent_le_reeFixedPosUnipotent j).trans le_sup_left)
    (reeFixedOrbitNegUnipotent_le_of_posUnipotent (A := reePosWeylGroup K a j)
      (reeFixedPosUnipotent_le_reePosWeylGroup j) (fixedOrbitElement_mem j) (h := 1) (one_mem _)
      (by rw [one_mul]; exact canonicalRep_mem_reePosWeylGroup j) (fun α hα => by
        rw [fixedOrbitElement_inv]
        exact height_fixedOrbitElement_smul_neg hα))

theorem map_conj_reePosWeylGroup_le
    (j : Fin F4.fixedOrbitCount) {h : ModGL F4.tag K}
    (hh : h ∈ F4.reeFixedTorus K a) :
    (reePosWeylGroup K a j).map (MulAut.conj h).toMonoidHom ≤ reePosWeylGroup K a j := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sup_le (fun u hu => ?_) ((Subgroup.closure_le _).2 ?_)
  · have hU : h * u * h⁻¹ ∈ F4.reeFixedPosUnipotent K a :=
      (Subgroup.mem_normalizer_iff.1
        (reeFixedBorel_le_normalizer_reeFixedPosUnipotent (reeFixedTorus_le_reeFixedBorel hh))
          u).1 hu
    exact reeFixedPosUnipotent_le_reePosWeylGroup j hU
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    show h * canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) * h⁻¹ ∈
      reePosWeylGroup K a j
    exact reeLocalBlock_le_reePosWeylGroup j
      ((Subgroup.mem_normalizer_iff.1 (reeFixedTorus_le_normalizer_reeLocalBlock j hh) _).1
        (canonicalRep_fixedOrbitElement_mem_reeLocalBlock j))

theorem reeFixedTorus_le_normalizer_reePosWeylGroup
    (j : Fin F4.fixedOrbitCount) :
    F4.reeFixedTorus K a ≤ Subgroup.normalizer (reePosWeylGroup K a j : Set (ModGL F4.tag K)) := by
  intro h hh
  refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · exact map_conj_reePosWeylGroup_le j hh ⟨x, hx, rfl⟩
  · have h2 : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ ∈ reePosWeylGroup K a j :=
      map_conj_reePosWeylGroup_le j (inv_mem hh) ⟨h * x * h⁻¹, hx, rfl⟩
    have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
    rwa [e] at h2

theorem reeFixedBorel_eq_sup
    :
    F4.reeFixedBorel K a = F4.reeFixedTorus K a ⊔ F4.reeFixedPosUnipotent K a := by
  refine le_antisymm (fun b hb => ?_)
    (sup_le reeFixedTorus_le_reeFixedBorel reeFixedPosUnipotent_le_reeFixedBorel)
  have hb' : b ∈ (F4.reeFixedBorel K a : Set (ModGL F4.tag K)) := hb
  rw [reeFixedBorel_eq_mul] at hb'
  obtain ⟨h, hh, u, hu, rfl⟩ := hb'
  exact mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hu)

theorem reeParabolic_singleton_eq_sup
    (j : Fin F4.fixedOrbitCount) :
    F4.reeParabolic K a {j} = F4.reeFixedTorus K a ⊔ reePosWeylGroup K a j := by
  show F4.reeFixedBorel K a ⊔ Subgroup.closure
      ((fun j => canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j)) '' {j}) =
    F4.reeFixedTorus K a ⊔ (F4.reeFixedPosUnipotent K a ⊔
      Subgroup.closure {canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j)})
  rw [Set.image_singleton, reeFixedBorel_eq_sup]
  exact sup_assoc _ _ _

theorem reePosWeylGroup_le_reeParabolic
    (j : Fin F4.fixedOrbitCount) :
    reePosWeylGroup K a j ≤ F4.reeParabolic K a {j} := by
  rw [reeParabolic_singleton_eq_sup]
  exact le_sup_right

theorem reePosWeylGroup_normal
    (j : Fin F4.fixedOrbitCount) :
    ((reePosWeylGroup K a j).subgroupOf (F4.reeParabolic K a {j})).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (reePosWeylGroup_le_reeParabolic j)).2 ?_
  rw [reeParabolic_singleton_eq_sup]
  exact sup_le (reeFixedTorus_le_normalizer_reePosWeylGroup j) Subgroup.le_normalizer

theorem commutator_reeParabolic_le_reePosWeylGroup
    (j : Fin F4.fixedOrbitCount) :
    ⁅F4.reeParabolic K a {j}, F4.reeParabolic K a {j}⁆ ≤ reePosWeylGroup K a j := by
  rw [reeParabolic_singleton_eq_sup]
  exact commutator_le_of_sup_normalizer (reeFixedTorus_le_normalizer_reePosWeylGroup j)
    fun x hx y hy => reeFixedTorus_mul_comm hx hy

theorem reePosWeylGroup_le_of_nonsolvable
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    {j : Fin F4.fixedOrbitCount} {A : Subgroup (ModGL F4.tag K)} (hAΓ : A ≤ F4.reeGamma K a)
    (hUA : F4.reeFixedPosUnipotent K a ≤ A) (hAP : A ≤ F4.reeParabolic K a {j})
    (hA : ¬ Group.IsSolvable ↥A) : reePosWeylGroup K a j ≤ A := by
  have hB : Group.IsSolvable ↥(F4.reeFixedBorel K a) := isSolvable_reeFixedBorel
  have hn : canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈ A := by
    by_contra hnj
    apply hA
    have hle := (large_Ree_positive_root_overgroup_parabolic_containment hK hAΓ hUA).1
    have hJ : {k | canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement k) ∈ A} = ∅ := by
      ext k
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hk
      have hkj : k ∈ ({j} : Set (Fin F4.fixedOrbitCount)) :=
        (canonicalRep_mem_reeParabolic_iff (t := F4) (K := K) (a := a)).1 (hAP hk)
      rw [Set.mem_singleton_iff] at hkj
      subst hkj
      exact hnj hk
    rw [hJ, reeParabolic_empty] at hle
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  exact sup_le hUA ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hn))

end ReePos

section LargeReeResidual

def f4Index (j : Fin 2) : Fin F4.fixedOrbitCount := Fin.cast (by decide) j

theorem f4Index_surjective : Function.Surjective f4Index := fun i =>
  ⟨Fin.cast (by decide) i, by simp [f4Index]⟩

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem large_Ree_residualOvergroupsAt
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ResidualOvergroupsAt ↥(F4.reeGamma K a)
      ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a))
      (fun j => (F4.reeParabolic K a {f4Index j}).subgroupOf (F4.reeGamma K a)) := by
  classical
  have : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  obtain ⟨hmin, hne, -⟩ := large_Ree_minimal_Borel_intersections a K w₀ hw₀
  have hUC : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a := reeFixedPosUnipotent_le_reeGamma
  have hPC : ∀ j, F4.reeParabolic K a {f4Index j} ≤ F4.reeGamma K a := fun j =>
    reeParabolic_le F4 K a _
  have hUP : ∀ j, F4.reeFixedPosUnipotent K a ≤ F4.reeParabolic K a {f4Index j} := fun j =>
    reeFixedPosUnipotent_le_reeFixedBorel.trans (reeFixedBorel_le_reeParabolic F4 K a _)
  have hQP : ∀ j, F4.reeLocalParabolic K a (f4Index j) = F4.reeParabolic K a {f4Index j} :=
    fun j => (reeParabolic_singleton (t := F4) (K := K) (a := a) (f4Index j)).symm
  have hcovQ : ∀ A : Subgroup (ModGL F4.tag K), A ≤ F4.reeGamma K a →
      (F4.reeFixedBorel K a ⋖ A ↔ A = F4.reeLocalParabolic K a ⟨0, by decide⟩ ∨
        A = F4.reeLocalParabolic K a ⟨1, by decide⟩) := by
    intro A hA
    rw [covBy_iff_minimal_of_le hA]
    exact hmin A
  have hcov : ∀ j, F4.reeFixedBorel K a ⋖ F4.reeParabolic K a {f4Index j} := by
    intro j
    refine (hcovQ _ (hPC j)).2 ?_
    rw [← hQP j]
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hne' : F4.reeParabolic K a {f4Index 0} ≠ F4.reeParabolic K a {f4Index 1} := by
    rw [← hQP 0, ← hQP 1]
    exact hne
  have hcont : ∀ A : Subgroup (ModGL F4.tag K), F4.reeFixedPosUnipotent K a ≤ A →
      A ≤ F4.reeGamma K a → A ≠ F4.reeGamma K a →
      A ≤ F4.reeParabolic K a {f4Index 0} ∨ A ≤ F4.reeParabolic K a {f4Index 1} := by
    intro A hUA hAΓ hAne
    obtain ⟨J, hJ, hAJ, -⟩ :=
      (large_Ree_positive_root_overgroup_parabolic_containment hK hAΓ hUA).2.2 hAne
    obtain ⟨i, hi⟩ : ∃ i, i ∉ J := by
      by_contra h
      exact hJ (Set.eq_univ_of_forall fun i => not_not.1 fun hi => h ⟨i, hi⟩)
    have hle : ∀ (J' : Set (Fin F4.fixedOrbitCount)) (j' : Fin 2), J' ⊆ {f4Index j'} →
        F4.reeParabolic K a J' ≤ F4.reeParabolic K a {f4Index j'} := fun J' j' h =>
      sup_le_sup_left (Subgroup.closure_mono (Set.image_mono h)) _
    obtain ⟨j, rfl⟩ := f4Index_surjective i
    fin_cases j
    · right
      refine hAJ.trans (hle J 1 fun k hk => ?_)
      obtain ⟨k', rfl⟩ := f4Index_surjective k
      fin_cases k'
      · exact absurd hk hi
      · exact Set.mem_singleton _
    · left
      refine hAJ.trans (hle J 0 fun k hk => ?_)
      obtain ⟨k', rfl⟩ := f4Index_surjective k
      fin_cases k'
      · exact Set.mem_singleton _
      · exact absurd hk hi
  exact residualOvergroupsAt_of_two_covers hUC hPC hUP hne' hcov hcont isSolvable_reeFixedBorel
    (fun j => commutator_reeParabolic_le_reePosWeylGroup (f4Index j))
    (fun j A hUA hAP hA => reePosWeylGroup_le_of_nonsolvable hK (hAP.trans (hPC j)) hUA hAP hA)

theorem even_rank_two_residual_largeRee
    {X : Type} [Group X] [Finite X] {f : ℕ}
    (hX : ReeTitsModel X .twistedF4 2 f) {U : Subgroup X}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K F4.prime)
      (φ : X ≃* F4.reeGamma K a), 1 ≤ a ∧ f = 2 * a + 1 ∧ Nat.card K = 2 ^ f ∧
      U.map φ.toMonoidHom = (F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a) ∧
      ResidualOvergroupsAt X U (fun j =>
        ((F4.reeParabolic K a {f4Index j}).subgroupOf (F4.reeGamma K a)).map φ.symm.toMonoidHom) ∧
      ∀ j : Fin 2,
        ((reePosWeylGroup K a (f4Index j)).subgroupOf (F4.reeParabolic K a {f4Index j})).Normal ∧
        ⁅F4.reeParabolic K a {f4Index j}, F4.reeParabolic K a {f4Index j}⁆ ≤
          reePosWeylGroup K a (f4Index j) ∧
        ∀ A : Subgroup (ModGL F4.tag K), F4.reeFixedPosUnipotent K a ≤ A →
          A ≤ F4.reeParabolic K a {f4Index j} → ¬ Group.IsSolvable ↥A →
            reePosWeylGroup K a (f4Index j) ≤ A := by
  obtain ⟨a, K, hKF, hKFin, hcp, ha, hfa, hK, ⟨e⟩⟩ := exists_mulEquiv_largeRee_model hX
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  obtain ⟨PU, hPU⟩ := (large_Ree_Sylow_opposition F4 a K w₀ hw₀).1
  have hUC : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a := reeFixedPosUnipotent_le_reeGamma
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf (F4.reeFixedPosUnipotent K a)
      (F4.reeGamma K a) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  obtain ⟨φ, hφ, hP⟩ := (large_Ree_residualOvergroupsAt (K := K) (a := a) hK').exists_iso_of_isSylow
    e (isSylowTwoOf_subgroupOf_top hUsyl) hU
  exact ⟨a, K, hKF, hKFin, hcp, φ, ha, hfa, hK, hφ, hP, fun j =>
    ⟨reePosWeylGroup_normal _, commutator_reeParabolic_le_reePosWeylGroup _,
      fun A hUA hAP hA => reePosWeylGroup_le_of_nonsolvable hK' ((hAP.trans (reeParabolic_le F4 K a _)))
        hUA hAP hA⟩⟩

end LargeReeResidual

end CFSG.QuasithinUnique.Setup.X6
