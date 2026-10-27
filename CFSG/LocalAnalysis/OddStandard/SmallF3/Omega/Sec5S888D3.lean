module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888D2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Ctx

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

theorem sec5_cht_le_normalizer (h37 : Asc82Lemma37) (h52a : Asc82Lemma52a)
    (h513 : Asc82Lemma513) (h514 : Asc82Lemma514) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) ≤
      normalizer (Qsub K₁ K₂ h : Set G) := by
  intro y hy
  obtain ⟨hyt, hyz⟩ := Subgroup.mem_inf.mp hy
  have hconj : CFSG.conjugate (Sec5B517All (Kfam5 K₁ K₂ h)) y =
      Sec5B517All (Kfam5 K₁ K₂ h) := by
    rw [sec5b517_all_eq, sup_assoc, sec5b_conjugate_sup,
      sec5_conj_K12 h52a c hyt hyz, sec5_conj_K34 h37 h52a h513 c hyt hyz]
  rw [sec5b517_Qsub_eq]
  exact Sec5B517Quad.mem_normalizer_of_conj (sec5b517_quad h514 c) hconj

end CFSG.OddStandard.SmallF3.Omega
