module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Residual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6G2

public section

namespace CFSG.QuasithinUnique.Setup.X6

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.ABGLocalTools
open scoped commutatorElement

section Ordinary

variable {τ : Tag} {K : Type} [Field K]

variable (τ K) in
@[expose] noncomputable def posWeylGroup
    (i : Fin τ.rank) : Subgroup (ModGL τ K) :=
  posUnipotent τ K ⊔ Subgroup.closure {weylElt τ K i 1}

theorem posUnipotent_le_posWeylGroup
    (i : Fin τ.rank) : posUnipotent τ K ≤ posWeylGroup τ K i :=
  le_sup_left

theorem weylElt_mem_posWeylGroup
    (i : Fin τ.rank) : weylElt τ K i 1 ∈ posWeylGroup τ K i :=
  Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_singleton _))

theorem weylElt_one_eq
    (i : Fin τ.rank) :
    weylElt τ K i 1 = xUnit τ K i 1 * yUnit τ K i (-1) * xUnit τ K i 1 := by
  rw [weylElt_eq_xUnit_mul]
  simp

theorem yUnit_mem_posWeylGroup
    (i : Fin τ.rank) (c : K) : yUnit τ K i c ∈ posWeylGroup τ K i := by
  rw [yUnit_eq_weylElt_mul]
  exact mul_mem (mul_mem (weylElt_mem_posWeylGroup i)
    (posUnipotent_le_posWeylGroup i (xUnit_mem_posUnipotent i (-c))))
    (inv_mem (weylElt_mem_posWeylGroup i))

theorem rootSubgroup_neg_single_le_posWeylGroup
    (i : Fin τ.rank) :
    rootSubgroup τ K (-Pi.single i 1) ≤ posWeylGroup τ K i := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  rw [pinnedX_neg_single]
  exact yUnit_mem_posWeylGroup i c

theorem map_conj_posWeylGroup_le
    (i : Fin τ.rank) {h : ModGL τ K} (hh : h ∈ torusGroup τ K) :
    (posWeylGroup τ K i).map (MulAut.conj h).toMonoidHom ≤ posWeylGroup τ K i := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sup_le (fun u hu => ?_) ((Subgroup.closure_le _).2 ?_)
  · have hU : h * u * h⁻¹ ∈ posUnipotent τ K :=
      (Subgroup.mem_normalizer_iff.1
        (torusGroup_le_normalizer_posUnipotent (τ := τ) (R := K) hh) u).1 hu
    exact posUnipotent_le_posWeylGroup i hU
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    show h * weylElt τ K i 1 * h⁻¹ ∈ posWeylGroup τ K i
    have e : h * weylElt τ K i 1 * h⁻¹ = (h * xUnit τ K i 1 * h⁻¹) * (h * yUnit τ K i (-1) * h⁻¹) *
        (h * xUnit τ K i 1 * h⁻¹) := by
      rw [weylElt_one_eq]
      group
    rw [e]
    have hx1 : h * xUnit τ K i 1 * h⁻¹ ∈ posWeylGroup τ K i :=
      posUnipotent_le_posWeylGroup i ((Subgroup.mem_normalizer_iff.1
        (torusGroup_le_normalizer_posUnipotent (τ := τ) (R := K) hh) _).1
        (xUnit_mem_posUnipotent i 1))
    have hy1 : h * yUnit τ K i (-1) * h⁻¹ ∈ posWeylGroup τ K i := by
      refine rootSubgroup_neg_single_le_posWeylGroup i ?_
      have hy : yUnit τ K i (-1) ∈ rootSubgroup τ K (-Pi.single i 1) := by
        rw [← pinnedX_neg_single]
        exact Subgroup.subset_closure ⟨_, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1
        (torusGroup_normalizes_rootSubgroup (K := K) (isRoot_neg_single τ i) hh) _).1 hy
    exact mul_mem (mul_mem hx1 hy1) hx1

theorem torusGroup_le_normalizer_posWeylGroup
    (i : Fin τ.rank) :
    torusGroup τ K ≤ Subgroup.normalizer (posWeylGroup τ K i : Set (ModGL τ K)) := by
  intro h hh
  refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · exact map_conj_posWeylGroup_le i hh ⟨x, hx, rfl⟩
  · have h2 : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ ∈ posWeylGroup τ K i :=
      map_conj_posWeylGroup_le i (inv_mem hh) ⟨h * x * h⁻¹, hx, rfl⟩
    have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
    rwa [e] at h2

theorem parabolicSubgroup_singleton_eq_sup
    (i : Fin τ.rank) :
    parabolicSubgroup τ K {i} = torusGroup τ K ⊔ posWeylGroup τ K i := by
  show borelGroup τ K ⊔ Subgroup.closure ((fun j => weylElt τ K j 1) '' {i}) =
    torusGroup τ K ⊔ (posUnipotent τ K ⊔ Subgroup.closure {weylElt τ K i 1})
  rw [Set.image_singleton]
  exact sup_assoc _ _ _

theorem posWeylGroup_le_parabolicSubgroup_singleton
    (i : Fin τ.rank) :
    posWeylGroup τ K i ≤ parabolicSubgroup τ K {i} := by
  rw [parabolicSubgroup_singleton_eq_sup]
  exact le_sup_right

theorem posWeylGroup_normal
    (i : Fin τ.rank) :
    ((posWeylGroup τ K i).subgroupOf (parabolicSubgroup τ K {i})).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer
    (posWeylGroup_le_parabolicSubgroup_singleton i)).2 ?_
  rw [parabolicSubgroup_singleton_eq_sup]
  exact sup_le (torusGroup_le_normalizer_posWeylGroup i) Subgroup.le_normalizer

theorem commutator_parabolic_le_posWeylGroup
    (i : Fin τ.rank) :
    ⁅parabolicSubgroup τ K {i}, parabolicSubgroup τ K {i}⁆ ≤ posWeylGroup τ K i := by
  rw [parabolicSubgroup_singleton_eq_sup]
  exact commutator_le_of_sup_normalizer (torusGroup_le_normalizer_posWeylGroup i)
    fun a ha b hb => (triangular_borel_structure.{0, 0} τ K).1 a ha b hb

theorem isSolvable_borelGroup
    (hU : Group.IsSolvable ↥(posUnipotent τ K)) :
    Group.IsSolvable ↥(borelGroup τ K) := by
  obtain ⟨hcomm, -, -, -, hHU, -, -, -, hnormal, -⟩ := triangular_borel_structure.{0, 0} τ K
  set U : Subgroup (borelGroup τ K) := (posUnipotent τ K).subgroupOf (borelGroup τ K) with hUdef
  have hUnormal : U.Normal := hnormal
  have hUle : posUnipotent τ K ≤ borelGroup τ K := le_sup_right
  have hUsolv : Group.IsSolvable U := Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.subgroupOfEquivOfLe hUle).toMonoidHom) (MulEquiv.injective _)
  have key : ∀ x : borelGroup τ K, ∃ h ∈ torusGroup τ K,
      ∃ hB : h ∈ borelGroup τ K,
        (QuotientGroup.mk x : borelGroup τ K ⧸ U) = QuotientGroup.mk ⟨h, hB⟩ := by
    rintro ⟨x, hx⟩
    have hx' : x ∈ (borelGroup τ K : Set (ModGL τ K)) := hx
    rw [hHU] at hx'
    obtain ⟨h, hh, u, hu, rfl⟩ := hx'
    refine ⟨h, hh, torusGroup_le_borelGroup hh, ?_⟩
    rw [QuotientGroup.eq, hUdef, Subgroup.mem_subgroupOf]
    change (h * u)⁻¹ * h ∈ posUnipotent τ K
    rw [show (h * u)⁻¹ * h = u⁻¹ by group]
    exact inv_mem hu
  have hquot : Group.IsSolvable (borelGroup τ K ⧸ U) := Group.isSolvable_of_comm fun a b => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨h, hh, hB, hxh⟩ := key x
    obtain ⟨h', hh', hB', hyh⟩ := key y
    rw [hxh, hyh, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (Subtype.ext (hcomm h hh h' hh'))
  exact Group.isSolvable_of_subgroup_quotient U

theorem posWeylGroup_le_of_nonsolvable
    (hB : Group.IsSolvable ↥(borelGroup τ K))
    {i : Fin τ.rank} {A : Subgroup (ModGL τ K)} (hAC : A ≤ adjointGroup τ K)
    (hUA : posUnipotent τ K ≤ A) (hAP : A ≤ parabolicSubgroup τ K {i})
    (hA : ¬ Group.IsSolvable ↥A) : posWeylGroup τ K i ≤ A := by
  have hn : weylElt τ K i 1 ∈ A := by
    by_contra hni
    apply hA
    have hle := (chevalley_positive_root_overgroup_parabolic_containment hAC hUA).1
    have hJ : {k | weylElt τ K k 1 ∈ A} = ∅ := by
      ext k
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hk
      have hkP : weylElt τ K k 1 ∈ parabolicSubgroup τ K {i} := hAP hk
      have hki : k ∈ ({i} : Set (Fin τ.rank)) := weylElt_mem_parabolicSubgroup_iff.1 hkP
      rw [Set.mem_singleton_iff] at hki
      subst hki
      exact hni hk
    rw [hJ, parabolicSubgroup_empty] at hle
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  exact sup_le hUA ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hn))

end Ordinary

section G2

variable {K : Type} [Field K] [Finite K] [CharP K 2]

def g2Index (j : Fin 2) : Fin Tag.G2.rank := Fin.cast (by decide) j

theorem g2Index_surjective : Function.Surjective g2Index := fun i =>
  ⟨Fin.cast (by decide) i, by simp [g2Index]⟩

theorem g2Index_injective : Function.Injective g2Index := fun a b h => by
  simpa [g2Index] using h

theorem G2_isSolvable_borelGroup
    : Group.IsSolvable ↥(borelGroup Tag.G2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hp : IsPGroup 2 ↥(posUnipotent Tag.G2 K) :=
    (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1.isPGroup
  have : Group.IsNilpotent ↥(posUnipotent Tag.G2 K) := hp.isNilpotent
  exact isSolvable_borelGroup inferInstance

theorem G2_residualOvergroupsAt
    :
    ResidualOvergroupsAt ↥(adjointGroup Tag.G2 K)
      ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K))
      (fun j => (parabolicSubgroup Tag.G2 K {g2Index j}).subgroupOf (adjointGroup Tag.G2 K)) := by
  classical
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hUC : posUnipotent Tag.G2 K ≤ adjointGroup Tag.G2 K := posUnipotent_le_adjointGroup
  obtain ⟨hcov, hinj, -⟩ := exceptional_ordinary_minimal_Borel_intersections Tag.G2 K
  have hPC : ∀ j, parabolicSubgroup Tag.G2 K {g2Index j} ≤ adjointGroup Tag.G2 K := fun j =>
    parabolicSubgroup_le_adjointGroup _ _ _
  have hUP : ∀ j, posUnipotent Tag.G2 K ≤ parabolicSubgroup Tag.G2 K {g2Index j} := fun j =>
    le_sup_right.trans (borelGroup_le_parabolicSubgroup _)
  have hne : parabolicSubgroup Tag.G2 K {g2Index 0} ≠ parabolicSubgroup Tag.G2 K {g2Index 1} :=
    fun h => absurd (g2Index_injective (hinj h)) (by decide)
  have hcov' : ∀ j, borelGroup Tag.G2 K ⋖ parabolicSubgroup Tag.G2 K {g2Index j} := fun j =>
    (hcov _ (hPC j)).2 ⟨_, rfl⟩
  have hPne : ∀ j, parabolicSubgroup Tag.G2 K {g2Index j} ≠ adjointGroup Tag.G2 K := by
    intro j h
    have h1 := hcov' (j + 1)
    have h2 := hcov' j
    have hlt : parabolicSubgroup Tag.G2 K {g2Index (j + 1)} <
        parabolicSubgroup Tag.G2 K {g2Index j} := by
      refine lt_of_le_of_ne ((hPC (j + 1)).trans_eq h.symm) ?_
      intro h'
      fin_cases j
      · exact (by decide : (1 : Fin 2) ≠ 0) (g2Index_injective (hinj h'))
      · exact (by decide : (0 : Fin 2) ≠ 1) (g2Index_injective (hinj h'))
    exact h2.2 h1.lt hlt
  have hcont : ∀ A : Subgroup (ModGL Tag.G2 K), posUnipotent Tag.G2 K ≤ A →
      A ≤ adjointGroup Tag.G2 K → A ≠ adjointGroup Tag.G2 K →
      A ≤ parabolicSubgroup Tag.G2 K {g2Index 0} ∨ A ≤ parabolicSubgroup Tag.G2 K {g2Index 1} := by
    intro A hUA hAC hAne
    obtain ⟨J, hJ, hAJ, -⟩ :=
      (chevalley_positive_root_overgroup_parabolic_containment hAC hUA).2.2 hAne
    obtain ⟨i, hi⟩ : ∃ i, i ∉ J := by
      by_contra h
      exact hJ (Set.eq_univ_of_forall fun i => not_not.1 fun hi => h ⟨i, hi⟩)
    obtain ⟨j, rfl⟩ := g2Index_surjective i
    fin_cases j
    · right
      refine hAJ.trans (parabolicSubgroup_le_parabolicSubgroup_iff.2 fun k hk => ?_)
      obtain ⟨k', rfl⟩ := g2Index_surjective k
      fin_cases k'
      · exact absurd hk hi
      · exact Set.mem_singleton _
    · left
      refine hAJ.trans (parabolicSubgroup_le_parabolicSubgroup_iff.2 fun k hk => ?_)
      obtain ⟨k', rfl⟩ := g2Index_surjective k
      fin_cases k'
      · exact Set.mem_singleton _
      · exact absurd hk hi
  have hmax : ∀ A : Subgroup (ModGL Tag.G2 K), posUnipotent Tag.G2 K ≤ A →
      A ≤ adjointGroup Tag.G2 K →
      (A ⋖ adjointGroup Tag.G2 K ↔ ∃ j, A = parabolicSubgroup Tag.G2 K {g2Index j}) := by
    intro A hUA hAC
    rw [maximal_overgroups_of_covers (hcov' 0) (hcov' 1) (hPC 0) (hPC 1) (hPne 0) (hPne 1) hcont
      A hUA hAC]
    constructor
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    · rintro ⟨j, hj⟩
      fin_cases j
      · exact Or.inl hj
      · exact Or.inr hj
  have hsolv : Group.IsSolvable ↥(parabolicSubgroup Tag.G2 K {g2Index 0} ⊓
      parabolicSubgroup Tag.G2 K {g2Index 1}) := by
    rw [inf_eq_of_covBy (hcov' 0) (hcov' 1) hne]
    exact G2_isSolvable_borelGroup
  exact residualOvergroupsAt_of_ambient hUC hPC hUP hne hmax hsolv
    (fun j => commutator_parabolic_le_posWeylGroup (g2Index j))
    (fun j A hUA hAP hA => posWeylGroup_le_of_nonsolvable G2_isSolvable_borelGroup
      (hAP.trans (hPC j)) hUA hAP hA)

theorem even_rank_two_residual_G2
    {X : Type} [Group X] [Finite X] {f : ℕ}
    (hX : ChevalleyExceptionalModel X .G2 2 f) {U : Subgroup X}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (φ : X ≃* adjointGroup Tag.G2 K), Nat.card K = 2 ^ f ∧
      U.map φ.toMonoidHom = (posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) ∧
      ResidualOvergroupsAt X U (fun j =>
        ((parabolicSubgroup Tag.G2 K {g2Index j}).subgroupOf (adjointGroup Tag.G2 K)).map
          φ.symm.toMonoidHom) ∧
      ∀ j : Fin 2,
        ((posWeylGroup Tag.G2 K (g2Index j)).subgroupOf
          (parabolicSubgroup Tag.G2 K {g2Index j})).Normal ∧
        ⁅parabolicSubgroup Tag.G2 K {g2Index j}, parabolicSubgroup Tag.G2 K {g2Index j}⁆ ≤
          posWeylGroup Tag.G2 K (g2Index j) ∧
        ∀ A : Subgroup (ModGL Tag.G2 K), posUnipotent Tag.G2 K ≤ A →
          A ≤ parabolicSubgroup Tag.G2 K {g2Index j} → ¬ Group.IsSolvable ↥A →
            posWeylGroup Tag.G2 K (g2Index j) ≤ A := by
  obtain ⟨-, K, hF, hFin, hcp, hK, ⟨e⟩⟩ := exists_mulEquiv_G2_model hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf
      ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1)
  obtain ⟨φ, hφ, hP⟩ := (G2_residualOvergroupsAt (K := K)).exists_iso_of_isSylow e hU₀ hU
  exact ⟨K, hF, hFin, hcp, φ, hK, hφ, hP, fun j =>
    ⟨posWeylGroup_normal _, commutator_parabolic_le_posWeylGroup _,
      fun A hUA hAP hA => posWeylGroup_le_of_nonsolvable G2_isSolvable_borelGroup
        (hAP.trans (parabolicSubgroup_le_adjointGroup _ _ _)) hUA hAP hA⟩⟩

end G2

end CFSG.QuasithinUnique.Setup.X6
