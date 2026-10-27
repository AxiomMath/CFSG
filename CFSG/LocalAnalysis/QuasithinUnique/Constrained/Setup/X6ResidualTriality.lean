module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Residual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6FixedContainment
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Triality

public section

namespace CFSG.QuasithinUnique.Setup.X6

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)
open scoped commutatorElement Pointwise

section FixedParabolic

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

variable (t K σ) in
@[expose] noncomputable def fixedPosWeylGroup
    (a : Fin t.foldedTag.rank) :
    Subgroup (ModGL t.tag K) :=
  graphFixedPosUnipotent t K σ ⊔
    Subgroup.closure {canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)}

theorem graphFixedPosUnipotent_le_fixedPosWeylGroup
    (a : Fin t.foldedTag.rank) :
    graphFixedPosUnipotent t K σ ≤ fixedPosWeylGroup t K σ a :=
  le_sup_left

theorem canonicalRep_orbitReflection_mem_fixedPosWeylGroup
    (a : Fin t.foldedTag.rank) :
    canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ fixedPosWeylGroup t K σ a :=
  Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_singleton _))

theorem orbitY_mem_fixedPosWeylGroup
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    (orbitY t K σ a c : ModGL t.tag K) ∈ fixedPosWeylGroup t K σ a :=
  orbitY_mem_of_posUnipotent (M := fixedPosWeylGroup t K σ a)
    (graphFixedPosUnipotent_le_fixedPosWeylGroup a) (w := t.orbitReflection a)
    (t.orbitReflection_mem a) (h := 1) (one_mem _)
    (by rw [one_mul]; exact canonicalRep_orbitReflection_mem_fixedPosWeylGroup a) (a := a)
    (fun i hi => by
      rw [t.orbitReflection_inv, t.orbitReflection_smul_single hi, height_neg, height_single]
      omega) c

theorem orbitXSubgroup_le_graphFixedPosUnipotent
    (a : Fin t.foldedTag.rank) :
    orbitXSubgroup t K σ a ≤ graphFixedPosUnipotent t K σ := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  exact orbitX_mem_graphFixedPosUnipotent t σ a c

theorem canonicalRep_orbitReflection_eq_mul
    (a : Fin t.foldedTag.rank) :
    ∃ c d : orbitField t K σ a, canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) =
      (orbitX t K σ a c : ModGL t.tag K) * (orbitY t K σ a d : ModGL t.tag K) *
        (orbitX t K σ a c : ModGL t.tag K) :=
  ⟨((1 : (orbitField t K σ a)ˣ) : orbitField t K σ a),
    -(((1 : (orbitField t K σ a)ˣ)⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a), by
    rw [canonicalRep_orbitReflection_eq_orbitN t σ a, orbitN, Subgroup.coe_mul,
      Subgroup.coe_mul]⟩

theorem orbitYSubgroup_le_fixedPosWeylGroup
    (a : Fin t.foldedTag.rank) :
    orbitYSubgroup t K σ a ≤ fixedPosWeylGroup t K σ a := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  exact orbitY_mem_fixedPosWeylGroup a c

theorem conj_mem_orbitYSubgroup
    {a : Fin t.foldedTag.rank} {h y : ModGL t.tag K}
    (hh : h ∈ graphFixedRootTorus t K σ) (hy : y ∈ orbitYSubgroup t K σ a) :
    h * y * h⁻¹ ∈ orbitYSubgroup t K σ a := by
  rw [orbitYSubgroup_eq] at hy ⊢
  obtain ⟨hyS, hyΓ⟩ := Subgroup.mem_inf.1 hy
  have hhT : h ∈ torusGroup t.tag K := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh).1).1
  have hhΓ : h ∈ twistedFixedGroup t K σ := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh).1).2
  have hSr : ∀ α ∈ (fun i => -(Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a),
      IsRoot t.tag α := by
    rintro _ ⟨i, -, rfl⟩
    exact isRoot_neg_single _ i
  refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem hhΓ hyΓ) (inv_mem hhΓ)⟩
  exact (Subgroup.mem_normalizer_iff.1
    (torusGroup_le_normalizer_rootSpan (K := K) hSr hhT) y).1 hyS

theorem map_conj_fixedPosWeylGroup_le
    (a : Fin t.foldedTag.rank) {h : ModGL t.tag K}
    (hh : h ∈ graphFixedRootTorus t K σ) :
    (fixedPosWeylGroup t K σ a).map (MulAut.conj h).toMonoidHom ≤ fixedPosWeylGroup t K σ a := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sup_le (fun u hu => ?_) ((Subgroup.closure_le _).2 ?_)
  · have hU : h * u * h⁻¹ ∈ graphFixedPosUnipotent t K σ :=
      (Subgroup.mem_normalizer_iff.1 (graphFixedRootTorus_le_normalizer_graphFixedPosUnipotent hh)
        u).1 hu
    exact graphFixedPosUnipotent_le_fixedPosWeylGroup a hU
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    show h * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * h⁻¹ ∈
      fixedPosWeylGroup t K σ a
    obtain ⟨c, d, hcd⟩ := canonicalRep_orbitReflection_eq_mul (t := t) (K := K) (σ := σ) a
    set x₁ : ModGL t.tag K := (orbitX t K σ a c : ModGL t.tag K) with hx₁def
    set y₁ : ModGL t.tag K := (orbitY t K σ a d : ModGL t.tag K) with hy₁def
    have hx₁ : x₁ ∈ orbitXSubgroup t K σ a := orbitX_mem_orbitXSubgroup a c
    have hy₁ : y₁ ∈ orbitYSubgroup t K σ a := orbitY_mem_orbitYSubgroup a d
    have e : h * (x₁ * y₁ * x₁) * h⁻¹ = (h * x₁ * h⁻¹) * (h * y₁ * h⁻¹) * (h * x₁ * h⁻¹) := by
      group
    rw [hcd, e]
    have hX : ∀ x ∈ orbitXSubgroup t K σ a, h * x * h⁻¹ ∈ fixedPosWeylGroup t K σ a := fun x hx =>
      graphFixedPosUnipotent_le_fixedPosWeylGroup a
        ((Subgroup.mem_normalizer_iff.1
          (graphFixedRootTorus_le_normalizer_graphFixedPosUnipotent hh) x).1
          (orbitXSubgroup_le_graphFixedPosUnipotent a hx))
    exact mul_mem (mul_mem (hX x₁ hx₁)
      (orbitYSubgroup_le_fixedPosWeylGroup a (conj_mem_orbitYSubgroup hh hy₁))) (hX x₁ hx₁)

theorem graphFixedRootTorus_le_normalizer_fixedPosWeylGroup
    (a : Fin t.foldedTag.rank) :
    graphFixedRootTorus t K σ ≤
      Subgroup.normalizer (fixedPosWeylGroup t K σ a : Set (ModGL t.tag K)) := by
  intro h hh
  refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · exact map_conj_fixedPosWeylGroup_le a hh ⟨x, hx, rfl⟩
  · have hh' : h⁻¹ ∈ graphFixedRootTorus t K σ := inv_mem hh
    have h2 : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ ∈ fixedPosWeylGroup t K σ a :=
      map_conj_fixedPosWeylGroup_le a hh' ⟨h * x * h⁻¹, hx, rfl⟩
    have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
    rwa [e] at h2

variable (hσ : Function.Surjective σ)
include hσ

theorem graphFixedRootBorel_eq_sup
    : graphFixedRootBorel t K σ =
    graphFixedRootTorus t K σ ⊔ graphFixedPosUnipotent t K σ := by
  refine le_antisymm (fun b hb => ?_)
    (sup_le graphFixedRootTorus_le_graphFixedRootBorel graphFixedPosUnipotent_le_graphFixedRootBorel)
  have hb' : b ∈ (graphFixedRootBorel t K σ : Set (ModGL t.tag K)) := hb
  rw [graphFixedRootBorel_eq_mul hσ] at hb'
  obtain ⟨h, hh, u, hu, rfl⟩ := hb'
  exact mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hu)

theorem graphFixedParabolic_singleton_eq_sup
    (a : Fin t.foldedTag.rank) :
    graphFixedParabolic t K σ {a} = graphFixedRootTorus t K σ ⊔ fixedPosWeylGroup t K σ a := by
  show graphFixedRootBorel t K σ ⊔ Subgroup.closure
      ((fun a => canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)) '' {a}) =
    graphFixedRootTorus t K σ ⊔ (graphFixedPosUnipotent t K σ ⊔
      Subgroup.closure {canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)})
  rw [Set.image_singleton, graphFixedRootBorel_eq_sup hσ]
  exact sup_assoc _ _ _

theorem fixedPosWeylGroup_le_graphFixedParabolic_singleton
    (a : Fin t.foldedTag.rank) :
    fixedPosWeylGroup t K σ a ≤ graphFixedParabolic t K σ {a} := by
  rw [graphFixedParabolic_singleton_eq_sup hσ]
  exact le_sup_right

theorem fixedPosWeylGroup_normal
    (a : Fin t.foldedTag.rank) :
    ((fixedPosWeylGroup t K σ a).subgroupOf (graphFixedParabolic t K σ {a})).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer
    (fixedPosWeylGroup_le_graphFixedParabolic_singleton hσ a)).2 ?_
  rw [graphFixedParabolic_singleton_eq_sup hσ]
  exact sup_le (graphFixedRootTorus_le_normalizer_fixedPosWeylGroup a) Subgroup.le_normalizer

theorem commutator_graphFixedParabolic_le_fixedPosWeylGroup
    (a : Fin t.foldedTag.rank) :
    ⁅graphFixedParabolic t K σ {a}, graphFixedParabolic t K σ {a}⁆ ≤ fixedPosWeylGroup t K σ a := by
  rw [graphFixedParabolic_singleton_eq_sup hσ]
  exact commutator_le_of_sup_normalizer (graphFixedRootTorus_le_normalizer_fixedPosWeylGroup a)
    fun a ha b hb => graphFixedRootTorus_mul_comm ha hb

omit hσ

end FixedParabolic

section Triality

def d4Index (j : Fin 2) : Fin TwistTag.D4.foldedTag.rank := Fin.cast (by decide) j

theorem d4Index_surjective : Function.Surjective d4Index := fun i =>
  ⟨Fin.cast (by decide) i, by simp [d4Index]⟩

theorem d4Index_injective : Function.Injective d4Index := fun a b h => by
  simpa [d4Index] using h

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem fixedPosWeylGroup_le_of_nonsolvable
    {t : TwistTag} (σ : K ≃+* K)
    (hB : Group.IsSolvable ↥(graphFixedRootBorel t K σ.toRingHom)) {a : Fin t.foldedTag.rank}
    {A : Subgroup (ModGL t.tag K)} (hAC : A ≤ graphFixedRootGroup t K σ.toRingHom)
    (hUA : graphFixedPosUnipotent t K σ.toRingHom ≤ A)
    (hAP : A ≤ graphFixedParabolic t K σ.toRingHom {a}) (hA : ¬ Group.IsSolvable ↥A) :
    fixedPosWeylGroup t K σ.toRingHom a ≤ A := by
  have hn : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ A := by
    by_contra hna
    apply hA
    have hle := (fixed_positive_root_overgroup_parabolic_containment t K σ hAC hUA).1
    have hJ : {k | canonicalRep (coxeterSystem t.tag) K (t.orbitReflection k) ∈ A} = ∅ := by
      ext k
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hk
      have hkP := hAP hk
      have hka : k ∈ ({a} : Set (Fin t.foldedTag.rank)) :=
        (canonicalRep_orbitReflection_mem_graphFixedParabolic_iff σ.surjective).1 hkP
      rw [Set.mem_singleton_iff] at hka
      subst hka
      exact hna hk
    rw [hJ, graphFixedParabolic_empty] at hle
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  exact sup_le hUA ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hn))

theorem triality_residualOvergroupsAt
    (σ : K ≃+* K) :
    ResidualOvergroupsAt ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      (fun j => (graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j}).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  classical
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hσs : Function.Surjective σ.toRingHom := σ.surjective
  obtain ⟨hcov, hinj, -⟩ := exceptional_fixed_minimal_Borel_intersections TwistTag.D4 K σ
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hPC : ∀ j, graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j} ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := fun j => graphFixedParabolic_le _ _ _ _
  have hUP : ∀ j, graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j} := fun j =>
    graphFixedPosUnipotent_le_graphFixedRootBorel.trans
      (graphFixedRootBorel_le_graphFixedParabolic _ _ _ _)
  have hne : graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index 0} ≠
      graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index 1} :=
    fun h => absurd (d4Index_injective (hinj h)) (by decide)
  have hcov' : ∀ j, graphFixedRootBorel TwistTag.D4 K σ.toRingHom ⋖
      graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j} := fun j =>
    (hcov _ (hPC j)).2 ⟨_, rfl⟩
  have hcont : ∀ A : Subgroup (ModGL TwistTag.D4.tag K),
      graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ A →
      A ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom →
      A ≠ graphFixedRootGroup TwistTag.D4 K σ.toRingHom →
      A ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index 0} ∨
        A ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index 1} := by
    intro A hUA hAC hAne
    obtain ⟨J, hJ, hAJ, -⟩ :=
      (fixed_positive_root_overgroup_parabolic_containment TwistTag.D4 K σ hAC hUA).2.2 hAne
    obtain ⟨a, ha⟩ : ∃ a, a ∉ J := by
      by_contra h
      exact hJ (Set.eq_univ_of_forall fun a => not_not.1 fun ha => h ⟨a, ha⟩)
    obtain ⟨j, rfl⟩ := d4Index_surjective a
    have hle : ∀ (J' : Set (Fin TwistTag.D4.foldedTag.rank)) (j' : Fin 2), J' ⊆ {d4Index j'} →
        graphFixedParabolic TwistTag.D4 K σ.toRingHom J' ≤
          graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j'} := fun J' j' h =>
      (fixed_standard_parabolic_cells TwistTag.D4 K σ).2.2.2.1 J' _ |>.2 h
    fin_cases j
    · right
      refine hAJ.trans (hle J 1 fun k hk => ?_)
      obtain ⟨k', rfl⟩ := d4Index_surjective k
      fin_cases k'
      · exact absurd hk ha
      · exact Set.mem_singleton _
    · left
      refine hAJ.trans (hle J 0 fun k hk => ?_)
      obtain ⟨k', rfl⟩ := d4Index_surjective k
      fin_cases k'
      · exact Set.mem_singleton _
      · exact absurd hk ha
  exact residualOvergroupsAt_of_two_covers hUC hPC hUP hne hcov' hcont
    (isSolvable_graphFixedRootBorel hσs)
    (fun j => commutator_graphFixedParabolic_le_fixedPosWeylGroup hσs (d4Index j))
    (fun j A hUA hAP hA => fixedPosWeylGroup_le_of_nonsolvable σ (isSolvable_graphFixedRootBorel hσs)
      (hAP.trans (hPC j)) hUA hAP hA)

theorem even_rank_two_residual_triality
    {X : Type} [Group X] [Finite X] {f : ℕ}
    (hX : ChevalleyExceptionalModel X .trialityD4 2 f) {U : Subgroup X}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K)
      (φ : X ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      Nat.card K = (2 ^ f) ^ 3 ∧ (∀ c, σ c = c ^ (2 ^ f)) ∧
      U.map φ.toMonoidHom = (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∧
      ResidualOvergroupsAt X U (fun j =>
        ((graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j}).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.symm.toMonoidHom) ∧
      ∀ j : Fin 2,
        ((fixedPosWeylGroup TwistTag.D4 K σ.toRingHom (d4Index j)).subgroupOf
          (graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j})).Normal ∧
        ⁅graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j},
          graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j}⁆ ≤
          fixedPosWeylGroup TwistTag.D4 K σ.toRingHom (d4Index j) ∧
        ∀ A : Subgroup (ModGL TwistTag.D4.tag K),
          graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ A →
          A ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j} →
          ¬ Group.IsSolvable ↥A →
            fixedPosWeylGroup TwistTag.D4 K σ.toRingHom (d4Index j) ≤ A := by
  obtain ⟨hf, K, hF, hFin, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model hX
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hσs : Function.Surjective σ.toRingHom := σ.surjective
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  obtain ⟨φ, hφ, hP⟩ := (triality_residualOvergroupsAt σ).exists_iso_of_isSylow e
    (isSylowTwoOf_subgroupOf_top hUsyl) hU
  exact ⟨K, hF, hFin, σ, φ, hK, hσ, hφ, hP, fun j =>
    ⟨fixedPosWeylGroup_normal hσs _, commutator_graphFixedParabolic_le_fixedPosWeylGroup hσs _,
      fun A hUA hAP hA => fixedPosWeylGroup_le_of_nonsolvable σ
        (isSolvable_graphFixedRootBorel hσs)
        (hAP.trans (graphFixedParabolic_le _ _ _ _)) hUA hAP hA⟩⟩

end Triality

end CFSG.QuasithinUnique.Setup.X6
