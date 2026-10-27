module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs

public section

namespace CFSG.ComponentClassification.RankTwoAltFive

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
@[expose] def conjActHom {K A' : Subgroup G} (hKA : K ≤ normalizer (A' : Set G)) :
    ↥K →* MulAut ↥A' where
  toFun k :=
    { toFun := fun a => ⟨k * a * k⁻¹, (mem_normalizer_iff.mp (hKA k.2) a).mp a.2⟩
      invFun := fun a => ⟨k⁻¹ * a * k, by
        simpa using (mem_normalizer_iff.mp (inv_mem (hKA k.2)) a).mp a.2⟩
      left_inv := fun a => Subtype.ext (by simp [mul_assoc])
      right_inv := fun a => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by
        change (k : G) * (a * b) * (k : G)⁻¹ = (k * a * (k : G)⁻¹) * (k * b * (k : G)⁻¹)
        group) }
  map_one' := by
    ext a
    simp
  map_mul' k l := by
    ext a
    simp [mul_assoc]

omit [Finite G] in
theorem conjActHom_apply {K A' : Subgroup G} (hKA : K ≤ normalizer (A' : Set G)) (k : ↥K)
    (a : ↥A') : ((conjActHom hKA k a : ↥A') : G) = k * a * (k : G)⁻¹ :=
  rfl

omit [Finite G] in
theorem ker_conjActHom {K A' : Subgroup G} (hKA : K ≤ normalizer (A' : Set G)) :
    (conjActHom hKA).ker = (centralizer (A' : Set G)).subgroupOf K := by
  ext k
  rw [MonoidHom.mem_ker, mem_subgroupOf, mem_centralizer_iff, MulEquiv.ext_iff]
  constructor
  · intro h a ha
    have h1 := congrArg Subtype.val (h ⟨a, ha⟩)
    change (k : G) * a * (k : G)⁻¹ = a at h1
    calc a * k = (k : G) * a * (k : G)⁻¹ * k := by rw [h1]
      _ = k * a := by group
  · intro h a
    apply Subtype.ext
    change (k : G) * a * (k : G)⁻¹ = a
    rw [← h a a.2]
    group

end CFSG.ComponentClassification.RankTwoAltFive
