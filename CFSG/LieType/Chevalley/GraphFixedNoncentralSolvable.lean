module

public import CFSG.LieType.Chevalley.GraphFixedNormalBorelSaturation

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped Pointwise

theorem fixed_noncentral_normal_solvable_quotient
    (t : TwistTag) (K : Type) [Field K]
    (σ : K ≃+* K) (M : Subgroup (graphFixedRootGroup t K σ.toRingHom)) [M.Normal]
    (hM : ¬ M ≤ Subgroup.center (graphFixedRootGroup t K σ.toRingHom)) :
    Group.IsSolvable (graphFixedRootGroup t K σ.toRingHom ⧸ M) := by
  have hsat := (fixed_normal_Borel_saturation t K σ M).resolve_left hM
  have hBC := graphFixedRootBorel_le t K σ.toRingHom
  have := isSolvable_graphFixedRootBorel (t := t) (K := K) (σ := σ.toRingHom) σ.surjective
  let f : graphFixedRootBorel t K σ.toRingHom →* graphFixedRootGroup t K σ.toRingHom ⧸ M :=
    (QuotientGroup.mk' M).comp (Subgroup.inclusion hBC)
  refine Group.isSolvable_of_surjective (f := f) fun q => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hx : (x : ModGL t.tag K) ∈
      ((M.map (graphFixedRootGroup t K σ.toRingHom).subtype : Set (ModGL t.tag K)) *
        (graphFixedRootBorel t K σ.toRingHom : Set (ModGL t.tag K))) := by
    rw [hsat.1, hsat.2]
    exact x.2
  obtain ⟨_, ⟨m, hm, rfl⟩, b, hb, hmb⟩ := hx
  refine ⟨⟨b, hb⟩, ?_⟩
  change (QuotientGroup.mk (Subgroup.inclusion hBC ⟨b, hb⟩) :
    graphFixedRootGroup t K σ.toRingHom ⧸ M) = QuotientGroup.mk x
  rw [QuotientGroup.eq]
  have e : (Subgroup.inclusion hBC ⟨b, hb⟩)⁻¹ * x = (Subgroup.inclusion hBC ⟨b, hb⟩)⁻¹ * m *
      Subgroup.inclusion hBC ⟨b, hb⟩ := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, ← hmb]
    rfl
  rw [e]
  have h := Subgroup.Normal.conj_mem inferInstance m hm (Subgroup.inclusion hBC ⟨b, hb⟩)⁻¹
  rwa [inv_inv] at h

end CFSG.LieType.Chevalley
