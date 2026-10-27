module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LieType.Chevalley.G2FieldFourEvenSimplePairs
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier

public section

namespace CFSG.QuasithinUnique.Setup.X6

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)

section G2

variable {τ : Tag} {K : Type} [Field K]

theorem map_subtype_simpleNegSubgroup
    (i : Fin τ.rank) :
    (simpleNegSubgroup τ K i).map (adjointGroup τ K).subtype =
      rootSubgroup τ K (-Pi.single i 1) := by
  apply SetLike.coe_injective
  rw [coe_rootSubgroup_neg_single]
  ext x
  constructor
  · rintro ⟨g, ⟨c, hc⟩, rfl⟩
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨⟨yUnit τ K i c, yUnit_mem_adjointGroup i c⟩, ⟨c, rfl⟩, rfl⟩

theorem parabolicSubgroup_subgroupOf_eq
    (i : Fin τ.rank) :
    (parabolicSubgroup τ K {i}).subgroupOf (adjointGroup τ K) =
      (borelGroup τ K).subgroupOf (adjointGroup τ K) ⊔ simpleNegSubgroup τ K i := by
  apply Subgroup.map_injective (adjointGroup τ K).subtype_injective
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (parabolicSubgroup_le_adjointGroup τ K _),
    Subgroup.map_subgroupOf_eq_of_le borelGroup_le_adjointGroup', map_subtype_simpleNegSubgroup,
    parabolicSubgroup_singleton_eq]

theorem mem_normalizer_of_map_conj_eq {G : Type*} [Group G] {H : Subgroup G} {x : G}
    (h : H.map (MulAut.conj x).toMonoidHom = H) : x ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← h]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← h] at hy
    obtain ⟨y', hy', hyy⟩ := hy
    have : y' = y := by
      have h2 : x * y' * x⁻¹ = x * y * x⁻¹ := hyy
      exact mul_left_cancel (mul_right_cancel h2)
    rw [← this]
    exact hy'

variable [Finite K] [CharP K 2]

theorem G2_invariant_parabolic
    (hK : 4 ≤ Nat.card K)
    {α : MulAut ↥(adjointGroup Tag.G2 K)}
    (hα : ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)).map α.toMonoidHom =
      (posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) (i : Fin Tag.G2.rank) :
    ((parabolicSubgroup Tag.G2 K {i}).subgroupOf (adjointGroup Tag.G2 K)).map α.toMonoidHom =
      (parabolicSubgroup Tag.G2 K {i}).subgroupOf (adjointGroup Tag.G2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.G2).length
  obtain ⟨c, β, hβU, hβV, rfl⟩ :=
    (exceptional_ordinary_Sylow_opposition Tag.G2 K 2 w₀ hw₀).2.2.2.2.2 α
  have hβ : β ∈ unipotentPairAut Tag.G2 K := ⟨hβU, hβV⟩
  have hY := (even_G2_opposite_Sylow_stabilizer_fixes_simple_pairs K hK hβ i).2
  have hUC : posUnipotent Tag.G2 K ≤ adjointGroup Tag.G2 K := posUnipotent_le_adjointGroup
  have hBnorm : Subgroup.normalizer
      (((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) :
        Subgroup ↥(adjointGroup Tag.G2 K)) : Set ↥(adjointGroup Tag.G2 K)) =
      (borelGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) := by
    rw [normalizer_subgroupOf_eq' hUC, (borel_self_normalizers Tag.G2 K).1]
  have hBβ : ((borelGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)).map β.toMonoidHom =
      (borelGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) := by
    rw [← hBnorm, Subgroup.map_equiv_normalizer_eq, hβU]
  have hcU : ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)).map
      (MulAut.conj c).toMonoidHom = (posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) := by
    rw [map_mulAut_mul, hβU] at hα
    exact hα
  have hcB : c ∈ (borelGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) := by
    rw [← hBnorm]
    exact mem_normalizer_of_map_conj_eq hcU
  have hP : (parabolicSubgroup Tag.G2 K {i}).subgroupOf (adjointGroup Tag.G2 K) =
      (borelGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) ⊔ simpleNegSubgroup Tag.G2 K i :=
    parabolicSubgroup_subgroupOf_eq i
  have hcP : c ∈ (parabolicSubgroup Tag.G2 K {i}).subgroupOf (adjointGroup Tag.G2 K) := by
    rw [hP]
    exact Subgroup.mem_sup_left hcB
  have hPβ : ((parabolicSubgroup Tag.G2 K {i}).subgroupOf (adjointGroup Tag.G2 K)).map
      β.toMonoidHom = (parabolicSubgroup Tag.G2 K {i}).subgroupOf (adjointGroup Tag.G2 K) := by
    rw [hP, Subgroup.map_sup, hBβ, hY]
  rw [map_mulAut_mul, hPβ]
  exact map_conj_eq_of_mem' hcP

theorem G2_hasInvariantMaximalOvergroups
    (hK : 4 ≤ Nat.card K) :
    ∃ U : Subgroup ↥(adjointGroup Tag.G2 K), CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ ∧
      HasInvariantMaximalOvergroups ↥(adjointGroup Tag.G2 K) U := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.G2).length
  set C := adjointGroup Tag.G2 K with hC
  have hUC : posUnipotent Tag.G2 K ≤ C := posUnipotent_le_adjointGroup
  obtain ⟨PU, hPU⟩ := (exceptional_ordinary_Sylow_opposition Tag.G2 K 2 w₀ hw₀).1
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf (posUnipotent Tag.G2 K) C := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hBnorm := (borel_self_normalizers Tag.G2 K).1
  obtain ⟨hcov, hinj, -⟩ := exceptional_ordinary_minimal_Borel_intersections Tag.G2 K
  have hcases : ∀ i : Fin Tag.G2.rank, i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by decide
  have hcov' : ∀ A : Subgroup (ModGL Tag.G2 K), A ≤ C →
      (borelGroup Tag.G2 K ⋖ A ↔ A = parabolicSubgroup Tag.G2 K {⟨0, by decide⟩} ∨
        A = parabolicSubgroup Tag.G2 K {⟨1, by decide⟩}) := by
    intro A hA
    rw [hcov A hA]
    constructor
    · rintro ⟨i, rfl⟩
      rcases hcases i with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (h | h)
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
  set P₀ := parabolicSubgroup Tag.G2 K {(⟨0, by decide⟩ : Fin Tag.G2.rank)} with hP₀
  set P₁ := parabolicSubgroup Tag.G2 K {(⟨1, by decide⟩ : Fin Tag.G2.rank)} with hP₁
  have hP₀C : P₀ ≤ C := parabolicSubgroup_le_adjointGroup _ _ _
  have hP₁C : P₁ ≤ C := parabolicSubgroup_le_adjointGroup _ _ _
  have hne : P₀ ≠ P₁ := fun h => by
    have := @hinj ⟨0, by decide⟩ ⟨1, by decide⟩ h
    exact absurd (congrArg Fin.val this) (by decide)
  have hcov₀ : borelGroup Tag.G2 K ⋖ P₀ := (hcov' P₀ hP₀C).2 (Or.inl rfl)
  have hcov₁ : borelGroup Tag.G2 K ⋖ P₁ := (hcov' P₁ hP₁C).2 (Or.inr rfl)
  have hP₀ne : P₀ ≠ C := fun h =>
    hcov₀.2 hcov₁.lt (lt_of_le_of_ne (hP₁C.trans_eq h.symm) hne.symm)
  have hP₁ne : P₁ ≠ C := fun h => hcov₁.2 hcov₀.lt (lt_of_le_of_ne (hP₀C.trans_eq h.symm) hne)
  have hgen : P₀ ⊔ P₁ = C := by
    refine le_antisymm (sup_le hP₀C hP₁C) ?_
    rw [hC, ← (standard_parabolic_cells Tag.G2 K).2.2.2.2.2.1]
    refine sup_le (le_sup_of_le_left (borelGroup_le_parabolicSubgroup _))
      ((Subgroup.closure_le _).2 ?_)
    rintro _ ⟨j, -, rfl⟩
    rcases hcases j with rfl | rfl
    · exact Subgroup.mem_sup_left (weylElt_mem_parabolicSubgroup (Set.mem_singleton _))
    · exact Subgroup.mem_sup_right (weylElt_mem_parabolicSubgroup (Set.mem_singleton _))
  have hcont : ∀ A : Subgroup (ModGL Tag.G2 K), posUnipotent Tag.G2 K ≤ A → A ≤ C → A ≠ C →
      A ≤ P₀ ∨ A ≤ P₁ := by
    intro A hUA hAC hAne
    obtain ⟨J, hJ, hAJ, -⟩ :=
      (chevalley_positive_root_overgroup_parabolic_containment hAC hUA).2.2 hAne
    obtain ⟨i, hi⟩ : ∃ i, i ∉ J := by
      by_contra h
      exact hJ (Set.eq_univ_of_forall fun i => not_not.1 fun hi => h ⟨i, hi⟩)
    rcases hcases i with rfl | rfl
    · right
      refine hAJ.trans (parabolicSubgroup_le_parabolicSubgroup_iff.2 fun j hj => ?_)
      rcases hcases j with rfl | rfl
      · exact absurd hj hi
      · exact Set.mem_singleton _
    · left
      refine hAJ.trans (parabolicSubgroup_le_parabolicSubgroup_iff.2 fun j hj => ?_)
      rcases hcases j with rfl | rfl
      · exact Set.mem_singleton _
      · exact absurd hj hi
  exact ⟨(posUnipotent Tag.G2 K).subgroupOf C, isSylowTwoOf_subgroupOf_top hUsyl,
    hasInvariantMaximalOvergroups_of_ambient hUsyl hBnorm hcov' hP₀C hP₁C hP₀ne hP₁ne hgen hcont
      fun α hα => ⟨G2_invariant_parabolic hK hα _, G2_invariant_parabolic hK hα _⟩⟩

end G2

section Model

theorem exists_mulEquiv_G2_model
    {X : Type} [Group X] {f : ℕ}
    (hX : ChevalleyExceptionalModel X .G2 2 f) :
    2 ≤ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2 ^ f ∧ Nonempty (X ≃* adjointGroup Tag.G2 K) := by
  have h3 : 3 ≤ 2 ^ f := hX.1.2.2.2
  have hf : 2 ≤ f := by
    by_contra h
    have : f ≤ 1 := by omega
    have : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  obtain ⟨K, hF, hFin, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup Tag.G2 hX.2
  have hcp : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  exact ⟨hf, K, hF, hFin, hcp, hK, ⟨e⟩⟩

theorem even_G2_model_two_extensions
    {X : Type} [Group X] [Finite X] {f : ℕ}
    (hX : ChevalleyExceptionalModel X .G2 2 f) :
    Subgroup.center X = ⊥ ∧
    TwoGeneratingSylowOvergroups X ∧
    (∀ D : Subgroup (MulAut X), inner X ≤ D → ∀ R : Subgroup (MulAut X),
      CFSG.QuasithinUnique.IsSylowTwoOf R D →
        ∃ M₁ M₂ : Subgroup (MulAut X), M₁ ≠ M₂ ∧ M₁ ⋖ D ∧ M₂ ⋖ D ∧ R ≤ M₁ ∧ R ≤ M₂) ∧
    ∀ U : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ →
      HasInvariantMaximalOvergroups X U := by
  obtain ⟨hf, K, hF, hFin, hcp, hK, ⟨e⟩⟩ := exists_mulEquiv_G2_model hX
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨U₀, hU₀, hcov⟩ := G2_hasInvariantMaximalOvergroups hK4
  have hZC : Subgroup.center (adjointGroup Tag.G2 K) = ⊥ := center_adjointGroup_eq_bot
  have hgen : TwoGeneratingSylowOvergroups (adjointGroup Tag.G2 K) := hcov.twoGenerating hZC hU₀
  have hgenX : TwoGeneratingSylowOvergroups X := hgen.of_mulEquiv e.symm
  refine ⟨?_, hgenX, fun D hD R hR => (hgenX D hD R hR).exists_two_maximal, fun U hU => ?_⟩
  · have h := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e
    rw [hZC] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h
  · exact hcov.of_isSylow e hU₀ hU

end Model

end CFSG.QuasithinUnique.Setup.X6
