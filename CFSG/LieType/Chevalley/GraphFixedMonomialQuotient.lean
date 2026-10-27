module

public import CFSG.LieType.Chevalley.GraphFixedBruhatEquivariance
public import CFSG.LieType.Chevalley.WeylNormalizerQuotient
public import CFSG.LieType.Chevalley.FoldedWeylIdentification

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem mapsRootLines_mul_canonicalRep
    {τ : Tag} {R : Type} [CommRing R]
    {k : (Module.End R (RootModule τ R))ˣ} (hk : k ∈ torusGroup τ R) (w : WeylGroup τ) :
    MapsRootLines (k * canonicalRep (coxeterSystem τ) R w) w := by
  simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w)

theorem canonicalRep_mem_monomialSubgroup
    {τ : Tag} (R : Type) [CommRing R] (w : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) R w ∈ monomialSubgroup τ R :=
  Subgroup.mem_sup_right (canonicalRep_mem_closure _ R w)

variable (t : TwistTag) (K : Type) [Field K] (σ : K →+* K)

theorem twistHom_mem_torusGroup
    {h : ModGL t.tag K} (hh : h ∈ torusGroup t.tag K) :
    twistHom t K σ h ∈ torusGroup t.tag K := by
  have hle : torusGroup t.tag K ≤ (torusGroup t.tag K).comap (twistHom t K σ) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, u⟩, rfl⟩
    change twistHom t K σ (torusElt t.tag K i u) ∈ torusGroup t.tag K
    rw [twistHom_torusElt]
    exact torusElt_mem_torusGroup _ _
  exact hle hh

theorem graphFixedMonomial_le_monomialSubgroup :
    graphFixedMonomial t K σ ≤ monomialSubgroup t.tag K :=
  inf_le_left

theorem graphFixedTorus_le_graphFixedMonomial :
    graphFixedTorus t K σ ≤ graphFixedMonomial t K σ :=
  inf_le_inf_right _ le_sup_left

theorem canonicalRep_mem_graphFixedMonomial
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) :
    canonicalRep (coxeterSystem t.tag) K w ∈ graphFixedMonomial t K σ :=
  ⟨canonicalRep_mem_monomialSubgroup K w, canonicalRep_mem_twistedFixedGroup t K σ hw⟩

@[expose] def graphFixedWeylHom :
    graphFixedMonomial t K σ →* WeylGroup t.tag :=
  (weylQuotientHom t.tag K).comp
    (Subgroup.inclusion (graphFixedMonomial_le_monomialSubgroup t K σ))

variable {t K σ}

theorem mapsRootLines_graphFixedWeylHom
    (g : graphFixedMonomial t K σ) :
    MapsRootLines (g : ModGL t.tag K) (graphFixedWeylHom t K σ g) :=
  mapsRootLines_weylQuotientHom
    (Subgroup.inclusion (graphFixedMonomial_le_monomialSubgroup t K σ) g)

theorem graphFixedWeylHom_eq
    {g : graphFixedMonomial t K σ} {w : WeylGroup t.tag}
    (h : MapsRootLines (g : ModGL t.tag K) w) : graphFixedWeylHom t K σ g = w :=
  weylQuotientHom_eq h

variable (t K σ)

theorem graphFixedWeylHom_mem
    (g : graphFixedMonomial t K σ) :
    graphFixedWeylHom t K σ g ∈ relWeylTwist t := by
  obtain ⟨w, k, hk, hgk⟩ := monomialSubgroup_le_torusWeylCosets
    (graphFixedMonomial_le_monomialSubgroup t K σ g.2)
  have h1 : graphFixedWeylHom t K σ g = w :=
    graphFixedWeylHom_eq (hgk ▸ mapsRootLines_mul_canonicalRep hk w)
  have hfix : twistHom t K σ (g : ModGL t.tag K) = g :=
    ((mem_twistedFixedGroup_iff_twistHom t K σ).1 (Subgroup.mem_inf.1 g.2).2).2
  have h2 : MapsRootLines (g : ModGL t.tag K) (weylTwist t w) := by
    rw [← hfix, hgk, map_mul, twistHom_canonicalRep]
    exact mapsRootLines_mul_canonicalRep (twistHom_mem_torusGroup t K σ hk) _
  rw [h1, mem_relWeylTwist]
  exact h2.unique (hgk ▸ mapsRootLines_mul_canonicalRep hk w)

theorem graphFixedWeylHom_canonicalRep
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) :
    graphFixedWeylHom t K σ ⟨_, canonicalRep_mem_graphFixedMonomial t K σ hw⟩ = w :=
  graphFixedWeylHom_eq (mapsRootLines_canonicalRep w)

theorem graphFixedWeylHom_range :
    (graphFixedWeylHom t K σ).range = relWeylTwist t := by
  ext w
  constructor
  · rintro ⟨g, rfl⟩
    exact graphFixedWeylHom_mem t K σ g
  · intro hw
    exact ⟨_, graphFixedWeylHom_canonicalRep t K σ hw⟩

theorem graphFixedWeylHom_ker :
    (graphFixedWeylHom t K σ).ker =
      (graphFixedTorus t K σ).subgroupOf (graphFixedMonomial t K σ) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hg
    obtain ⟨w, k, hk, hgk⟩ := monomialSubgroup_le_torusWeylCosets
      (graphFixedMonomial_le_monomialSubgroup t K σ g.2)
    have hw : w = 1 :=
      (graphFixedWeylHom_eq (hgk ▸ mapsRootLines_mul_canonicalRep hk w)).symm.trans hg
    refine Subgroup.mem_inf.2 ⟨?_, (Subgroup.mem_inf.1 g.2).2⟩
    rw [hgk, hw, canonicalRep_one, mul_one]
    exact hk
  · intro hg
    exact graphFixedWeylHom_eq (mapsRootLines_of_mem_torusGroup (Subgroup.mem_inf.1 hg).1)

instance graphFixedTorus_subgroupOf_normal :
    ((graphFixedTorus t K σ).subgroupOf (graphFixedMonomial t K σ)).Normal :=
  graphFixedWeylHom_ker t K σ ▸ MonoidHom.normal_ker _

@[expose] def graphFixedMonomialQuotientEquiv :
    graphFixedMonomial t K σ ⧸ (graphFixedTorus t K σ).subgroupOf (graphFixedMonomial t K σ) ≃*
      relWeylTwist t :=
  (QuotientGroup.quotientMulEquivOfEq (graphFixedWeylHom_ker t K σ).symm).trans
    ((QuotientGroup.quotientKerEquivRange _).trans
      (MulEquiv.subgroupCongr (graphFixedWeylHom_range t K σ)))

theorem coe_graphFixedMonomialQuotientEquiv_mk
    (g : graphFixedMonomial t K σ) :
    (graphFixedMonomialQuotientEquiv t K σ (QuotientGroup.mk g) : WeylGroup t.tag) =
      graphFixedWeylHom t K σ g :=
  rfl

theorem graphFixedMonomial_eq_sup :
    graphFixedMonomial t K σ = graphFixedTorus t K σ ⊔ Subgroup.closure
      (Set.range fun a => canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)) := by
  set C := Subgroup.closure
    (Set.range fun a => canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a))
  have hC : C ≤ graphFixedMonomial t K σ := (Subgroup.closure_le _).2 (by
    rintro _ ⟨a, rfl⟩
    exact canonicalRep_mem_graphFixedMonomial t K σ (t.orbitReflection_mem a))
  refine le_antisymm (fun g hg => ?_) (sup_le (graphFixedTorus_le_graphFixedMonomial t K σ) hC)
  have himg : relWeylTwist t ≤
      (C.subgroupOf (graphFixedMonomial t K σ)).map (graphFixedWeylHom t K σ) := by
    rw [relWeylTwist_eq_closure, Subgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨_, Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure ⟨a, rfl⟩),
      graphFixedWeylHom_canonicalRep t K σ (t.orbitReflection_mem a)⟩
  obtain ⟨x, hx, hxg⟩ := himg (graphFixedWeylHom_mem t K σ ⟨g, hg⟩)
  have hker : x⁻¹ * ⟨g, hg⟩ ∈ (graphFixedWeylHom t K σ).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxg, inv_mul_cancel]
  rw [graphFixedWeylHom_ker, Subgroup.mem_subgroupOf] at hker
  have hg' : g = (x : ModGL t.tag K) * ((x⁻¹ * ⟨g, hg⟩ : graphFixedMonomial t K σ) :
      ModGL t.tag K) := by
    simp
  rw [hg']
  exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.1 hx))
    (Subgroup.mem_sup_left hker)

theorem fixed_monomial_quotient
    (t : TwistTag) (K : Type) [Field K] (σ : K →+* K) :
    (graphFixedWeylHom t K σ).range = relWeylTwist t ∧
    (graphFixedWeylHom t K σ).ker =
      (graphFixedTorus t K σ).subgroupOf (graphFixedMonomial t K σ) ∧
    ((graphFixedTorus t K σ).subgroupOf (graphFixedMonomial t K σ)).Normal ∧
    (∃ e : graphFixedMonomial t K σ ⧸ (graphFixedTorus t K σ).subgroupOf
        (graphFixedMonomial t K σ) ≃* relWeylTwist t,
      ∀ g, (e (QuotientGroup.mk g) : WeylGroup t.tag) = graphFixedWeylHom t K σ g) ∧
    Nonempty (relWeylTwist t ≃* WeylGroup t.foldedTag) ∧
    graphFixedMonomial t K σ = graphFixedTorus t K σ ⊔ Subgroup.closure
      (Set.range fun a => canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)) ∧
    ∀ w ∈ relWeylTwist t,
      ∃ h : canonicalRep (coxeterSystem t.tag) K w ∈ graphFixedMonomial t K σ,
        graphFixedWeylHom t K σ ⟨_, h⟩ = w :=
  ⟨graphFixedWeylHom_range t K σ, graphFixedWeylHom_ker t K σ, inferInstance,
    ⟨graphFixedMonomialQuotientEquiv t K σ, coe_graphFixedMonomialQuotientEquiv_mk t K σ⟩,
    ⟨foldedWeylEquiv t⟩, graphFixedMonomial_eq_sup t K σ,
    fun _ hw => ⟨_, graphFixedWeylHom_canonicalRep t K σ hw⟩⟩

end CFSG.LieType.Chevalley
