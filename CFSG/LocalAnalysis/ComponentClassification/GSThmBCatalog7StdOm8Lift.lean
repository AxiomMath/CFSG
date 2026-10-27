module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Chain
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalLinearFixedConjugation

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed

section Fitting

variable {H : Type*} [Group H]

theorem perfect_le_of_outer_solvable (G : Subgroup H) [G.Normal]
    [Group.IsSolvable (OuterAutomorphisms.Outer G)] (hC : centralizer (G : Set H) = ⊥)
    (P : Subgroup H) [Group.IsPerfect P] : P ≤ G := by
  intro x hx
  obtain ⟨g, hg⟩ := OuterAutomorphisms.perfect_action_inner
    ((MulAut.conjNormal : H →* MulAut G).comp P.subtype) ⟨x, hx⟩
  have hcent : (g : H)⁻¹ * x ∈ centralizer (G : Set H) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h1 := congrArg (fun φ : MulAut G => ((φ ⟨y, hy⟩ : G) : H)) hg
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply,
      MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc y * ((g : H)⁻¹ * x) = (g : H)⁻¹ * ((g : H) * y * (g : H)⁻¹) * x := by group
      _ = (g : H)⁻¹ * (x * y * x⁻¹) * x := by rw [h1]
      _ = (g : H)⁻¹ * x * y := by group
  rw [hC, mem_bot, inv_mul_eq_one] at hcent
  rw [← hcent]
  exact g.2

theorem pComponent_le_of_outer_solvable (G : Subgroup H) [G.Normal]
    [Group.IsSolvable (OuterAutomorphisms.Outer G)] (hC : centralizer (G : Set H) = ⊥)
    {C L : Subgroup H} (hLC : L ≤ C) (hL : IsPComponent 2 (L.subgroupOf C)) : L ≤ G := by
  have hP : Group.IsPerfect (L.subgroupOf C) := CatalogueBAlternating.pComponent_perfect hL
  have : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hLC).toMonoidHom) (subgroupOfEquivOfLe hLC).surjective
  exact perfect_le_of_outer_solvable G hC L

end Fitting

section Lift

variable {H : Type*} [Group H] (G : Subgroup H) [G.Normal]
  {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
  (Θ : G ≃* projectiveDerived Q) (t : H) (A : V ≃ₗ[K] V) (μ : Kˣ)
  (hsim : ∀ x : V, Q (A x) = (μ : K) * Q x)
  (hconj : ∀ g : G, Θ (MulAut.conjNormal t g) = projectiveConjugation Q A μ hsim (Θ g))

include hconj in
theorem mem_centralizer_iff_fixed (g : G) :
    (g : H) ∈ centralizer ({t} : Set H) ↔ projectiveConjugation Q A μ hsim (Θ g) = Θ g := by
  rw [← hconj, Θ.apply_eq_iff_eq, mem_centralizer_singleton_iff, Subtype.ext_iff,
    MulAut.conjNormal_apply, mul_inv_eq_iff_eq_mul]
  exact eq_comm

@[expose] def centEquiv : G.subgroupOf (centralizer ({t} : Set H)) ≃*
    fixedSubgroup (projectiveConjugation Q A μ hsim) where
  toFun x := ⟨Θ ⟨x.val.val, x.property⟩, (mem_centralizer_iff_fixed G Q Θ t A μ hsim hconj
    ⟨x.val.val, x.property⟩).mp x.val.property⟩
  invFun y := ⟨⟨(Θ.symm y.val : H), (mem_centralizer_iff_fixed G Q Θ t A μ hsim hconj
    (Θ.symm y.val)).mpr (by rw [MulEquiv.apply_symm_apply]; exact y.property)⟩,
    mem_subgroupOf.mpr (Θ.symm y.val).property⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change ((Θ.symm (Θ ⟨x.val.val, x.property⟩) : G) : H) = x.val.val
    rw [MulEquiv.symm_apply_apply]
  right_inv y := by
    apply Subtype.ext
    change Θ ⟨((Θ.symm y.val : G) : H), (Θ.symm y.val).property⟩ = y.val
    exact Θ.apply_symm_apply y.val
  map_mul' x y := by
    apply Subtype.ext
    change Θ (⟨x.val.val, x.property⟩ * ⟨y.val.val, y.property⟩) = _
    rw [map_mul]
    rfl

theorem centEquiv_val (x : G.subgroupOf (centralizer ({t} : Set H))) :
    (centEquiv G Q Θ t A μ hsim hconj x).val = Θ ⟨x.val.val, x.property⟩ := rfl

theorem centEquiv_symm_val (y : fixedSubgroup (projectiveConjugation Q A μ hsim)) :
    ((centEquiv G Q Θ t A μ hsim hconj).symm y).val.val = (Θ.symm y.val : H) := rfl

@[expose] def projChain : (orthogonalDerived Q).subgroupOf
    (fixedSubgroup (similarityConjugation Q A μ hsim)) →*
      fixedSubgroup (projectiveConjugation Q A μ hsim) :=
  chainHom (orthogonalDerived Q) (scalarSigns Q) (similarityConjugation Q A μ hsim)
    (orthogonalDerived_invariant Q A μ hsim) (scalarSigns_invariant Q A μ hsim)

theorem projChain_eq_one_iff (x : (orthogonalDerived Q).subgroupOf
    (fixedSubgroup (similarityConjugation Q A μ hsim))) :
    projChain Q A μ hsim x = 1 ↔ x.val.val ∈ scalarSigns Q :=
  chainHom_eq_one_iff (orthogonalDerived Q) (scalarSigns Q) (similarityConjugation Q A μ hsim)
    (orthogonalDerived_invariant Q A μ hsim) (scalarSigns_invariant Q A μ hsim) x

@[expose] def outerH : fixedSubgroup (projectiveConjugation Q A μ hsim) →* H :=
  (centralizer ({t} : Set H)).subtype.comp
    ((G.subgroupOf (centralizer ({t} : Set H))).subtype.comp
      (centEquiv G Q Θ t A μ hsim hconj).symm.toMonoidHom)

theorem outerH_injective : Function.Injective (outerH G Q Θ t A μ hsim hconj) :=
  (subtype_injective _).comp ((subtype_injective _).comp (MulEquiv.injective _))

@[expose] def toH : (orthogonalDerived Q).subgroupOf
    (fixedSubgroup (similarityConjugation Q A μ hsim)) →* H :=
  (outerH G Q Θ t A μ hsim hconj).comp (projChain Q A μ hsim)

theorem toH_apply (x : (orthogonalDerived Q).subgroupOf
    (fixedSubgroup (similarityConjugation Q A μ hsim))) :
    toH G Q Θ t A μ hsim hconj x = (Θ.symm (QuotientGroup.mk'
      ((scalarSigns Q).subgroupOf (orthogonalDerived Q)) ⟨x.val.val, x.property⟩) : H) := rfl

theorem toH_mem_G (x : (orthogonalDerived Q).subgroupOf
    (fixedSubgroup (similarityConjugation Q A μ hsim))) :
    toH G Q Θ t A μ hsim hconj x ∈ G := (Θ.symm _).property

theorem toH_mem_centralizer (x : (orthogonalDerived Q).subgroupOf
    (fixedSubgroup (similarityConjugation Q A μ hsim))) :
    toH G Q Θ t A μ hsim hconj x ∈ centralizer ({t} : Set H) :=
  ((centEquiv G Q Θ t A μ hsim hconj).symm _).val.property

theorem toH_eq_one_iff (x : (orthogonalDerived Q).subgroupOf
    (fixedSubgroup (similarityConjugation Q A μ hsim))) :
    toH G Q Θ t A μ hsim hconj x = 1 ↔ x.val.val ∈ scalarSigns Q := by
  rw [toH, MonoidHom.comp_apply, map_eq_one_iff _ (outerH_injective G Q Θ t A μ hsim hconj),
    projChain_eq_one_iff]

theorem pComponent_centralizer_iff (L : Subgroup H) (hLG : L ≤ G) [Finite H] :
    IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set H))) ↔
      IsPComponent 2 ((L.subgroupOf (centralizer ({t} : Set H))).subgroupOf
        (G.subgroupOf (centralizer ({t} : Set H)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : L.subgroupOf (centralizer ({t} : Set H)) ≤
      G.subgroupOf (centralizer ({t} : Set H)) := fun x hx => hLG hx
  exact (pComponent_normal_iff 2 _ _ hle).symm

variable [Finite H] [Finite (TauCeti.QuadraticMap.orthogonalGroup Q)]

theorem toH_up (M : Subgroup ((orthogonalDerived Q).subgroupOf
      (fixedSubgroup (similarityConjugation Q A μ hsim))))
    (hM : IsPComponent 2 M) :
    M.map (toH G Q Θ t A μ hsim hconj) ≤ centralizer ({t} : Set H) ∧
      M.map (toH G Q Θ t A μ hsim hconj) ≤ G ∧
      IsPComponent 2 ((M.map (toH G Q Θ t A μ hsim hconj)).subgroupOf
        (centralizer ({t} : Set H))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({t} : Set H)
  have h1 : IsPComponent 2 (M.map (projChain Q A μ hsim)) :=
    chain_up (orthogonalDerived Q) (scalarSigns Q) (similarityConjugation Q A μ hsim)
      (orthogonalDerived_invariant Q A μ hsim) (scalarSigns_invariant Q A μ hsim)
      (scalarSigns_central Q) M hM
  have h2 := CatalogueBAlternating.pComponent_map_equiv 2
    (centEquiv G Q Θ t A μ hsim hconj).symm _ h1
  have h3 := CatalogueBAlternating.pComponent_of_normal_subgroup 2 (G.subgroupOf C) _ h2
  set M₃ := ((M.map (projChain Q A μ hsim)).map
      (centEquiv G Q Θ t A μ hsim hconj).symm.toMonoidHom).map (G.subgroupOf C).subtype
  have heq : M.map (toH G Q Θ t A μ hsim hconj) = M₃.map C.subtype := by
    rw [map_map, map_map, map_map]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact toH_mem_centralizer G Q Θ t A μ hsim hconj x
  · rintro _ ⟨x, -, rfl⟩
    exact toH_mem_G G Q Θ t A μ hsim hconj x
  · have hM₃ : (M₃.map C.subtype).subgroupOf C = M₃ :=
      comap_map_eq_self_of_injective (subtype_injective _) M₃
    rw [heq, hM₃]
    exact h3

theorem toH_down (L : Subgroup H) (hLC : L ≤ centralizer ({t} : Set H)) (hLG : L ≤ G)
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set H)))) :
    ∃ M : Subgroup ((orthogonalDerived Q).subgroupOf
        (fixedSubgroup (similarityConjugation Q A μ hsim))),
      IsPComponent 2 M ∧ M.map (toH G Q Θ t A μ hsim hconj) = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({t} : Set H)
  have h1 := (pComponent_centralizer_iff G t L hLG).mp hL
  have h2 := CatalogueBAlternating.pComponent_map_equiv 2 (centEquiv G Q Θ t A μ hsim hconj) _ h1
  obtain ⟨M, hM, hmap⟩ : ∃ M : Subgroup ((orthogonalDerived Q).subgroupOf
      (fixedSubgroup (similarityConjugation Q A μ hsim))), IsPComponent 2 M ∧
        M.map (projChain Q A μ hsim) = _ :=
    chain_down (orthogonalDerived Q) (scalarSigns Q)
      (similarityConjugation Q A μ hsim) (orthogonalDerived_invariant Q A μ hsim)
      (scalarSigns_invariant Q A μ hsim) (scalarSigns_central Q) _ h2
  refine ⟨M, hM, ?_⟩
  have hle : L.subgroupOf C ≤ G.subgroupOf C := fun x hx => hLG hx
  have hcancel : ∀ X : Subgroup (G.subgroupOf C),
      (X.map (centEquiv G Q Θ t A μ hsim hconj).toMonoidHom).map
        (centEquiv G Q Θ t A μ hsim hconj).symm.toMonoidHom = X := by
    intro X
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨centEquiv G Q Θ t A μ hsim hconj x, ⟨x, hx, rfl⟩, by simp⟩
  rw [toH, outerH, ← map_map, hmap, ← map_map, ← map_map, hcancel,
    map_subgroupOf_eq_of_le hle, map_subgroupOf_eq_of_le hLC]

omit [Finite H] [Finite (TauCeti.QuadraticMap.orthogonalGroup Q)] in
theorem toH_inj (M₁ M₂ : Subgroup ((orthogonalDerived Q).subgroupOf
      (fixedSubgroup (similarityConjugation Q A μ hsim))))
    (h₁ : IsPComponent 2 M₁) (h₂ : IsPComponent 2 M₂)
    (h : M₁.map (toH G Q Θ t A μ hsim hconj) = M₂.map (toH G Q Θ t A μ hsim hconj)) :
    M₁ = M₂ := by
  refine chain_inj (orthogonalDerived Q) (scalarSigns Q) (similarityConjugation Q A μ hsim)
    (orthogonalDerived_invariant Q A μ hsim) (scalarSigns_invariant Q A μ hsim)
    (scalarSigns_central Q) M₁ M₂ h₁ h₂ ?_
  change M₁.map (projChain Q A μ hsim) = M₂.map (projChain Q A μ hsim)
  apply map_injective (outerH_injective G Q Θ t A μ hsim hconj)
  rw [map_map, map_map]
  exact h

end Lift

end CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8
