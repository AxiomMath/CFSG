module

public import CFSG.LieType.Chevalley.GraphFixedMinimalBorel
public import CFSG.LieType.Chevalley.GraphFixedParabolicLevi

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem orbitX_mem_graphFixedParabolicRadical
    {J : Set (Fin t.foldedTag.rank)}
    {a : Fin t.foldedTag.rank} (ha : a ∉ J) (c : orbitField t K σ a) :
    (orbitX t K σ a c : ModGL t.tag K) ∈ graphFixedParabolicRadical t K σ J := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 (orbitX_mem t σ a c)
  refine Subgroup.mem_inf.2 ⟨rootSpan_mono ?_ h1, h2⟩
  rintro _ ⟨i, hi, rfl⟩
  refine mem_parabolicRadicalRoots_iff.2 ⟨isRoot_single _ i, by rw [height_single]; exact one_pos,
    i, fun hiA => ha ?_, by simp⟩
  obtain ⟨b, hb, hib⟩ := (t.mem_orbitUnion).1 hiA
  have hab : a = b := ((t.mem_orbit_iff).1 hi).symm.trans ((t.mem_orbit_iff).1 hib)
  exact hab ▸ hb

theorem diagram_fixed_parabolic_root_radical_normalizers
    (t : TwistTag) (K : Type) [Field K]
    (σ : K ≃+* K) (J : Set (Fin t.foldedTag.rank)) :
    graphFixedRootGroup t K σ.toRingHom ⊓
        Subgroup.normalizer (graphFixedParabolicRadical t K σ.toRingHom J : Set (ModGL t.tag K)) =
      graphFixedParabolic t K σ.toRingHom J := by
  have hσ : Function.Surjective σ.toRingHom := σ.surjective
  have hLevi := diagram_fixed_parabolic_root_radical_Levi_factors t K σ J
  have hPN : graphFixedParabolic t K σ.toRingHom J ≤ Subgroup.normalizer
      (graphFixedParabolicRadical t K σ.toRingHom J : Set (ModGL t.tag K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLevi.2.2.2.2.2.2.2.2.1).1
      hLevi.2.2.2.2.2.2.2.2.2.1
  have hPC := le_inf (graphFixedParabolic_le t K σ.toRingHom J) hPN
  refine le_antisymm ?_ hPC
  rw [eq_graphFixedParabolic_of_le hσ
    ((graphFixedRootBorel_le_graphFixedParabolic t K σ.toRingHom J).trans hPC) inf_le_left]
  refine (graphFixedParabolic_le_iff hσ).2 fun a ha => ?_
  by_contra haJ
  have hnN := (Subgroup.mem_inf.1 ha).2
  have hx := orbitX_mem_graphFixedParabolicRadical (σ := σ.toRingHom) haJ 1
  have e : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
      (orbitX t K σ.toRingHom a 1 : ModGL t.tag K) *
        (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a))⁻¹ =
          orbitY t K σ.toRingHom a (-1) := by
    rw [← canonicalRep_orbitReflection_conj_orbitX t σ.toRingHom a (-1), neg_neg]
  have hy := (Subgroup.mem_normalizer_iff.1 hnN _).1 hx
  rw [e] at hy
  have h1 : (orbitY t K σ.toRingHom a (-1) : ModGL t.tag K) ∈
      graphFixedRootBorel t K σ.toRingHom ⊓ graphFixedNegUnipotent t K σ.toRingHom :=
    Subgroup.mem_inf.2 ⟨graphFixedPosUnipotent_le_graphFixedRootBorel
      (graphFixedParabolicRadical_le_graphFixedPosUnipotent J hy),
      orbitY_mem_graphFixedNegUnipotent t σ.toRingHom a (-1)⟩
  rw [graphFixedRootBorel_inf_graphFixedNegUnipotent, Subgroup.mem_bot, ← e, conj_eq_one_iff] at h1
  exact one_ne_zero (orbitX_injective σ.toRingHom a
    ((Subtype.ext h1).trans (orbitX_zero t σ.toRingHom a).symm))

end CFSG.LieType.Chevalley
