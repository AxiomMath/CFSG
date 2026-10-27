module

public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.GenA
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.SolomonA7Input
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.EvenSporadicStandard.SolomonRed

open Subgroup Equiv

theorem outSq_alternatingGroup_seven : OutSq (alternatingGroup (Fin 7)) := by
  intro α
  obtain ⟨σ, hσ⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num)).2 α
  have hsq : σ * σ ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]
    exact Int.units_mul_self _
  refine ⟨⟨σ * σ, hsq⟩, fun x => ?_⟩
  subst hσ
  apply Subtype.ext
  show (σ * ((σ * (x : Perm (Fin 7)) * σ⁻¹)) * σ⁻¹) = (σ * σ) * x * (σ * σ)⁻¹
  group

theorem solomonZ2A7_of_cat (h : CatNoAlmostSimpleZ2 (alternatingGroup (Fin 7))) :
    M23Std.SolomonZ2A7 := by
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hc : Subgroup.center (alternatingGroup (Fin 7)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  exact solomonGen_of_cat (exists_noncommute_of_center_eq_bot hc) outSq_alternatingGroup_seven h

end CFSG.EvenSporadicStandard.SolomonRed
