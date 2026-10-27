module

public import CFSG.GF2Type.Aschbacher1976Full.HSAut
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {z : G} {T V : Subgroup G}

theorem hsAut_exists_SL (hGL : GL3Stmt) (hset : HSSetting G z) (hV : HSV z T V) :
    ∃ θ : ↥(Subgroup.normalizer (V : Set G)) →* SL(3, ZMod 2), Function.Surjective θ ∧
      θ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf
        (Subgroup.normalizer (V : Set G)) := by
  obtain ⟨θ, hθs, hθk⟩ := CFSG.ComponentClassification.GHarris.exists_GL32_of_dvd_index
    hV.isElem hV.card_eq (by rw [hsAut_index hGL hset hV]; norm_num)
  let e : GL (Fin 3) (ZMod 2) ≃* SL(3, ZMod 2) :=
    CFSG.ComponentClassification.GHarris.SL32EquivGL32.symm
  refine ⟨e.toMonoidHom.comp θ, e.surjective.comp hθs, ?_⟩
  rw [← hθk]
  ext n
  simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]

end CFSG.GF2Type.Aschbacher1976Full.HS
