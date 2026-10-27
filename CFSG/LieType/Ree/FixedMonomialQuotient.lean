module

public import CFSG.LieType.Ree.RootBruhatEquivariance
public import CFSG.LieType.Ree.FixedWeylStructure
public import CFSG.LieType.Chevalley.GraphFixedMonomialQuotient

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace ReeTag

variable (t : ReeTag) (K : Type) [Field K] [Finite K] [CharP K t.prime] (a : ℕ)

omit [Finite K] [CharP K t.prime] in
theorem torusGroup_le_adjointGroup
    : torusGroup t.tag K ≤ adjointGroup t.tag K :=
  (Subgroup.closure_le _).2 fun _ ⟨p, hp⟩ => hp ▸ torusElt_mem_adjointGroup p.1 p.2

theorem reeFixedMonomial_le_monomialSubgroup :
    t.reeFixedMonomial K a ≤ monomialSubgroup t.tag K :=
  inf_le_left

theorem reeFixedTorus_le_reeFixedMonomial :
    t.reeFixedTorus K a ≤ t.reeFixedMonomial K a :=
  inf_le_inf_right _ le_sup_left

theorem canonicalRep_mem_reeFixedMonomial
    {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee) :
    canonicalRep (coxeterSystem t.tag) K w ∈ t.reeFixedMonomial K a :=
  (ree_root_Bruhat_equivariance t a K).2.2.2.2.2.2.2 w hw

@[expose] def reeFixedWeylHom :
    t.reeFixedMonomial K a →* WeylGroup t.tag :=
  (weylQuotientHom t.tag K).comp
    (Subgroup.inclusion (reeFixedMonomial_le_monomialSubgroup t K a))

variable {t K a}

theorem reeFixedWeylHom_eq
    {g : t.reeFixedMonomial K a} {w : WeylGroup t.tag}
    (h : MapsRootLines (g : ModGL t.tag K) w) : t.reeFixedWeylHom K a g = w :=
  weylQuotientHom_eq h

theorem finiteReeAut_mem_torusGroup
    {k : ModGL t.tag K} (hk : k ∈ torusGroup t.tag K)
    (hka : k ∈ adjointGroup t.tag K) :
    ((t.finiteReeAut K a ⟨k, hka⟩ : adjointGroup t.tag K) : ModGL t.tag K) ∈
      torusGroup t.tag K := by
  have h := (ree_root_Bruhat_equivariance t a K).2.1
  have hmem : t.finiteReeAut K a ⟨k, hka⟩ ∈
      ((torusGroup t.tag K).subgroupOf (adjointGroup t.tag K)).map
        (t.finiteReeAut K a).toMonoidHom :=
    ⟨⟨k, hka⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩
  rw [h] at hmem
  exact Subgroup.mem_subgroupOf.1 hmem

variable (t K a)

theorem reeFixedWeylHom_mem
    (g : t.reeFixedMonomial K a) :
    t.reeFixedWeylHom K a g ∈ t.relWeylRee := by
  obtain ⟨w, k, hk, hgk⟩ := monomialSubgroup_le_torusWeylCosets
    (reeFixedMonomial_le_monomialSubgroup t K a g.2)
  have h1 : t.reeFixedWeylHom K a g = w :=
    reeFixedWeylHom_eq (hgk ▸ mapsRootLines_mul_canonicalRep hk w)
  obtain ⟨hga, hfix⟩ := mem_reeGamma.1 (Subgroup.mem_inf.1 g.2).2
  have hka : k ∈ adjointGroup t.tag K := torusGroup_le_adjointGroup t K hk
  have hdec : (⟨g, hga⟩ : adjointGroup t.tag K) = ⟨k, hka⟩ * nrep t.tag K w :=
    Subtype.ext hgk
  have hF := (ree_root_Bruhat_equivariance t a K).2.2.2.2.2.2.1 w
  have h2 : MapsRootLines (g : ModGL t.tag K) (t.weylPerm w) := by
    have hg : (g : ModGL t.tag K) =
        ((t.finiteReeAut K a ⟨k, hka⟩ : adjointGroup t.tag K) : ModGL t.tag K) *
          canonicalRep (coxeterSystem t.tag) K (t.weylPerm w) := by
      have := congrArg (fun x : adjointGroup t.tag K => (x : ModGL t.tag K)) hfix
      simp only at this
      rw [← this, hdec, map_mul, hF]
      rfl
    rw [hg]
    exact mapsRootLines_mul_canonicalRep (finiteReeAut_mem_torusGroup hk hka) _
  rw [h1, mem_relWeylRee]
  exact h2.unique (hgk ▸ mapsRootLines_mul_canonicalRep hk w)

theorem reeFixedWeylHom_canonicalRep
    {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee) :
    t.reeFixedWeylHom K a ⟨_, canonicalRep_mem_reeFixedMonomial t K a hw⟩ = w :=
  reeFixedWeylHom_eq (mapsRootLines_canonicalRep w)

theorem reeFixedWeylHom_range :
    (t.reeFixedWeylHom K a).range = t.relWeylRee := by
  ext w
  constructor
  · rintro ⟨g, rfl⟩
    exact reeFixedWeylHom_mem t K a g
  · intro hw
    exact ⟨_, reeFixedWeylHom_canonicalRep t K a hw⟩

theorem reeFixedWeylHom_ker :
    (t.reeFixedWeylHom K a).ker = (t.reeFixedTorus K a).subgroupOf (t.reeFixedMonomial K a) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hg
    obtain ⟨w, k, hk, hgk⟩ := monomialSubgroup_le_torusWeylCosets
      (reeFixedMonomial_le_monomialSubgroup t K a g.2)
    have hw : w = 1 :=
      (reeFixedWeylHom_eq (hgk ▸ mapsRootLines_mul_canonicalRep hk w)).symm.trans hg
    refine Subgroup.mem_inf.2 ⟨?_, (Subgroup.mem_inf.1 g.2).2⟩
    rw [hgk, hw, canonicalRep_one, mul_one]
    exact hk
  · intro hg
    exact reeFixedWeylHom_eq (mapsRootLines_of_mem_torusGroup (Subgroup.mem_inf.1 hg).1)

instance reeFixedTorus_subgroupOf_normal :
    ((t.reeFixedTorus K a).subgroupOf (t.reeFixedMonomial K a)).Normal :=
  reeFixedWeylHom_ker t K a ▸ MonoidHom.normal_ker _

@[expose] def reeFixedMonomialQuotientEquiv :
    t.reeFixedMonomial K a ⧸ (t.reeFixedTorus K a).subgroupOf (t.reeFixedMonomial K a) ≃*
      t.relWeylRee :=
  (QuotientGroup.quotientMulEquivOfEq (reeFixedWeylHom_ker t K a).symm).trans
    ((QuotientGroup.quotientKerEquivRange _).trans
      (MulEquiv.subgroupCongr (reeFixedWeylHom_range t K a)))

theorem coe_reeFixedMonomialQuotientEquiv_mk
    (g : t.reeFixedMonomial K a) :
    (t.reeFixedMonomialQuotientEquiv K a (QuotientGroup.mk g) : WeylGroup t.tag) =
      t.reeFixedWeylHom K a g :=
  rfl

theorem reeFixedMonomial_eq_sup :
    t.reeFixedMonomial K a = t.reeFixedTorus K a ⊔ Subgroup.closure
      (Set.range fun j => canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j)) := by
  set C := Subgroup.closure
    (Set.range fun j => canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))
  have hC : C ≤ t.reeFixedMonomial K a := (Subgroup.closure_le _).2 (by
    rintro _ ⟨j, rfl⟩
    exact canonicalRep_mem_reeFixedMonomial t K a (fixedOrbitElement_mem j))
  refine le_antisymm (fun g hg => ?_) (sup_le (reeFixedTorus_le_reeFixedMonomial t K a) hC)
  have himg : t.relWeylRee ≤
      (C.subgroupOf (t.reeFixedMonomial K a)).map (t.reeFixedWeylHom K a) := by
    rw [relWeylRee_eq_closure, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨_, Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure ⟨j, rfl⟩),
      reeFixedWeylHom_canonicalRep t K a (fixedOrbitElement_mem j)⟩
  obtain ⟨x, hx, hxg⟩ := himg (reeFixedWeylHom_mem t K a ⟨g, hg⟩)
  have hker : x⁻¹ * ⟨g, hg⟩ ∈ (t.reeFixedWeylHom K a).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxg, inv_mul_cancel]
  rw [reeFixedWeylHom_ker, Subgroup.mem_subgroupOf] at hker
  have hg' : g = (x : ModGL t.tag K) * ((x⁻¹ * ⟨g, hg⟩ : t.reeFixedMonomial K a) :
      ModGL t.tag K) := by
    simp
  rw [hg']
  exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.1 hx))
    (Subgroup.mem_sup_left hker)

theorem ree_fixed_monomial_quotient
    (t : ReeTag) (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K t.prime] :
    (t.reeFixedWeylHom K a).range = t.relWeylRee ∧
    (t.reeFixedWeylHom K a).ker =
      (t.reeFixedTorus K a).subgroupOf (t.reeFixedMonomial K a) ∧
    ((t.reeFixedTorus K a).subgroupOf (t.reeFixedMonomial K a)).Normal ∧
    (∃ e : t.reeFixedMonomial K a ⧸ (t.reeFixedTorus K a).subgroupOf (t.reeFixedMonomial K a) ≃*
        t.relWeylRee,
      ∀ g, (e (QuotientGroup.mk g) : WeylGroup t.tag) = t.reeFixedWeylHom K a g) ∧
    t.reeFixedMonomial K a = t.reeFixedTorus K a ⊔ Subgroup.closure
      (Set.range fun j => canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j)) ∧
    ∀ w ∈ t.relWeylRee,
      ∃ h : canonicalRep (coxeterSystem t.tag) K w ∈ t.reeFixedMonomial K a,
        t.reeFixedWeylHom K a ⟨_, h⟩ = w :=
  ⟨reeFixedWeylHom_range t K a, reeFixedWeylHom_ker t K a, inferInstance,
    ⟨t.reeFixedMonomialQuotientEquiv K a, coe_reeFixedMonomialQuotientEquiv_mk t K a⟩,
    reeFixedMonomial_eq_sup t K a,
    fun _ hw => ⟨_, reeFixedWeylHom_canonicalRep t K a hw⟩⟩

end ReeTag

end CFSG.LieType.Ree
