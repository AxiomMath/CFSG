module

public import CFSG.LieType.Chevalley.GraphFixedRootNormal
public import CFSG.LieType.Chevalley.FoldedLengthSigns
public import CFSG.LieType.Chevalley.FixedCollection

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem canonicalRep_mul_of_length_eq
    {τ : Tag} {v v' : WeylGroup τ}
    (h : (coxeterSystem τ).length (v * v') =
      (coxeterSystem τ).length v + (coxeterSystem τ).length v') :
    canonicalRep (coxeterSystem τ) K (v * v') =
      canonicalRep (coxeterSystem τ) K v * canonicalRep (coxeterSystem τ) K v' :=
  congrArg Subtype.val (nrep_mul K h)

theorem length_orbitReflection
    (a : Fin t.foldedTag.rank) :
    (coxeterSystem t.tag).length (t.orbitReflection a) = (t.orbit a).card := by
  rw [← t.length_orbitWord]
  exact isReduced_orbitWord t a

theorem canonicalRep_mem_graphFixedRootGroup
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) :
    canonicalRep (coxeterSystem t.tag) K w ∈ graphFixedRootGroup t K σ := by
  suffices h : ∀ n, ∀ w ∈ relWeylTwist t, (coxeterSystem t.tag).length w = n →
      canonicalRep (coxeterSystem t.tag) K w ∈ graphFixedRootGroup t K σ from h _ w hw rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hw hn
    by_cases h1 : w = 1
    · rw [h1, canonicalRep_one]
      exact one_mem _
    obtain ⟨a, ha⟩ := exists_forall_height_smul_single_neg t hw h1
    have hlen := (length_mul_orbitReflection_of_neg t hw ha).2
    have hv : w * t.orbitReflection a ∈ relWeylTwist t := mul_mem hw (t.orbitReflection_mem a)
    have hcard := t.card_orbit_pos a
    have hwv : w = w * t.orbitReflection a * t.orbitReflection a := by
      rw [mul_assoc, t.orbitReflection_mul_self, mul_one]
    have hadd : (coxeterSystem t.tag).length
        (w * t.orbitReflection a * t.orbitReflection a) =
        (coxeterSystem t.tag).length (w * t.orbitReflection a) +
          (coxeterSystem t.tag).length (t.orbitReflection a) := by
      rw [← hwv, length_orbitReflection]
      omega
    rw [hwv, canonicalRep_mul_of_length_eq hadd]
    exact mul_mem (ih _ (by omega) _ hv rfl)
      (canonicalRep_orbitReflection_mem_graphFixedRootGroup a)

variable (t K σ)

theorem canonicalRep_mem_graphFixedRootMonomial
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) :
    canonicalRep (coxeterSystem t.tag) K w ∈ graphFixedRootMonomial t K σ :=
  Subgroup.mem_inf.2 ⟨canonicalRep_mem_graphFixedMonomial t K σ hw,
    canonicalRep_mem_graphFixedRootGroup hw⟩

@[expose] def graphFixedRootWeylHom :
    graphFixedRootMonomial t K σ →* WeylGroup t.tag :=
  (graphFixedWeylHom t K σ).comp (Subgroup.inclusion inf_le_left)

theorem graphFixedRootWeylHom_canonicalRep
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) :
    graphFixedRootWeylHom t K σ ⟨_, canonicalRep_mem_graphFixedRootMonomial t K σ hw⟩ = w :=
  graphFixedWeylHom_canonicalRep t K σ hw

theorem graphFixedRootWeylHom_range
    : (graphFixedRootWeylHom t K σ).range = relWeylTwist t := by
  ext w
  constructor
  · rintro ⟨g, rfl⟩
    exact graphFixedWeylHom_mem t K σ _
  · intro hw
    exact ⟨_, graphFixedRootWeylHom_canonicalRep t K σ hw⟩

theorem graphFixedRootWeylHom_ker :
    (graphFixedRootWeylHom t K σ).ker =
      (graphFixedRootTorus t K σ).subgroupOf (graphFixedRootMonomial t K σ) := by
  ext g
  have hg := Subgroup.mem_inf.1 g.2
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  change graphFixedWeylHom t K σ (Subgroup.inclusion inf_le_left g) = 1 ↔ _
  rw [← MonoidHom.mem_ker, graphFixedWeylHom_ker, Subgroup.mem_subgroupOf]
  exact ⟨fun h => Subgroup.mem_inf.2 ⟨h, hg.2⟩, fun h => (Subgroup.mem_inf.1 h).1⟩

instance graphFixedRootTorus_subgroupOf_normal :
    ((graphFixedRootTorus t K σ).subgroupOf (graphFixedRootMonomial t K σ)).Normal :=
  graphFixedRootWeylHom_ker t K σ ▸ MonoidHom.normal_ker _

@[expose] def graphFixedRootMonomialQuotientEquiv :
    graphFixedRootMonomial t K σ ⧸
        (graphFixedRootTorus t K σ).subgroupOf (graphFixedRootMonomial t K σ) ≃*
      relWeylTwist t :=
  (QuotientGroup.quotientMulEquivOfEq (graphFixedRootWeylHom_ker t K σ).symm).trans
    ((QuotientGroup.quotientKerEquivRange _).trans
      (MulEquiv.subgroupCongr (graphFixedRootWeylHom_range t K σ)))

theorem coe_graphFixedRootMonomialQuotientEquiv_mk
    (g : graphFixedRootMonomial t K σ) :
    (graphFixedRootMonomialQuotientEquiv t K σ (QuotientGroup.mk g) : WeylGroup t.tag) =
      graphFixedRootWeylHom t K σ g :=
  rfl

theorem graphFixedRootMonomial_eq_sup :
    graphFixedRootMonomial t K σ = graphFixedRootTorus t K σ ⊔ Subgroup.closure
      (Set.range fun a => canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)) := by
  set C := Subgroup.closure
    (Set.range fun a => canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a))
  have hC : C ≤ graphFixedRootMonomial t K σ := (Subgroup.closure_le _).2 (by
    rintro _ ⟨a, rfl⟩
    exact canonicalRep_mem_graphFixedRootMonomial t K σ (t.orbitReflection_mem a))
  have hH : graphFixedRootTorus t K σ ≤ graphFixedRootMonomial t K σ :=
    inf_le_inf_right _ (graphFixedTorus_le_graphFixedMonomial t K σ)
  refine le_antisymm (fun g hg => ?_) (sup_le hH hC)
  have himg : relWeylTwist t ≤
      (C.subgroupOf (graphFixedRootMonomial t K σ)).map (graphFixedRootWeylHom t K σ) := by
    rw [relWeylTwist_eq_closure, Subgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨_, Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure ⟨a, rfl⟩),
      graphFixedRootWeylHom_canonicalRep t K σ (t.orbitReflection_mem a)⟩
  obtain ⟨x, hx, hxg⟩ := himg ((graphFixedRootWeylHom_range t K σ) ▸ ⟨⟨g, hg⟩, rfl⟩ :
    graphFixedRootWeylHom t K σ ⟨g, hg⟩ ∈ relWeylTwist t)
  have hker : x⁻¹ * ⟨g, hg⟩ ∈ (graphFixedRootWeylHom t K σ).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxg, inv_mul_cancel]
  rw [graphFixedRootWeylHom_ker, Subgroup.mem_subgroupOf] at hker
  have hg' : g = (x : ModGL t.tag K) *
      ((x⁻¹ * ⟨g, hg⟩ : graphFixedRootMonomial t K σ) : ModGL t.tag K) := by
    simp
  rw [hg']
  exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.1 hx))
    (Subgroup.mem_sup_left hker)

theorem fixed_root_monomial_quotient
    (t : TwistTag) (K : Type) [Field K] (σ : K →+* K) :
    (∀ w ∈ relWeylTwist t,
      canonicalRep (coxeterSystem t.tag) K w ∈ graphFixedRootMonomial t K σ) ∧
    (graphFixedRootWeylHom t K σ).range = relWeylTwist t ∧
    (graphFixedRootWeylHom t K σ).ker =
      (graphFixedRootTorus t K σ).subgroupOf (graphFixedRootMonomial t K σ) ∧
    ((graphFixedRootTorus t K σ).subgroupOf (graphFixedRootMonomial t K σ)).Normal ∧
    (∃ e : graphFixedRootMonomial t K σ ⧸ (graphFixedRootTorus t K σ).subgroupOf
        (graphFixedRootMonomial t K σ) ≃* relWeylTwist t,
      ∀ g, (e (QuotientGroup.mk g) : WeylGroup t.tag) = graphFixedRootWeylHom t K σ g) ∧
    Nonempty (relWeylTwist t ≃* WeylGroup t.foldedTag) ∧
    graphFixedRootMonomial t K σ = graphFixedRootTorus t K σ ⊔ Subgroup.closure
      (Set.range fun a => canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)) :=
  ⟨fun _ hw => canonicalRep_mem_graphFixedRootMonomial t K σ hw,
    graphFixedRootWeylHom_range t K σ, graphFixedRootWeylHom_ker t K σ, inferInstance,
    ⟨graphFixedRootMonomialQuotientEquiv t K σ, coe_graphFixedRootMonomialQuotientEquiv_mk t K σ⟩,
    ⟨foldedWeylEquiv t⟩, graphFixedRootMonomial_eq_sup t K σ⟩

end CFSG.LieType.Chevalley
