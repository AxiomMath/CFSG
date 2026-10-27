module

public import CFSG.FeitThompson.Representations.FrobeniusReciprocityClassFunctions
public import CFSG.FeitThompson.Representations.NormalSubgroupInduction
import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace NormalInducedFamily

open NormalInduction (conjClassFun conjClassFun_apply)

variable {L : Type*} [Group L] (H : Subgroup L)

@[simp] theorem conjClassFun_one_right [H.Normal] (t : L) :
    conjClassFun H t (1 : H → ℂ) = 1 := by
  funext n
  simp [conjClassFun_apply]

theorem indClassFun_one_mem_indFam [Fintype L] :
    indClassFun H (1 : H → ℂ) ∈ indFam H (Irr H) :=
  indClassFun_mem_indFam H one_mem_Irr

@[simp] theorem resClassFun_one : resClassFun H (1 : L → ℂ) = 1 := by
  funext x
  simp

theorem cfInner_indClassFun_indClassFun_one [Fintype L] [H.Normal] {θ : H → ℂ}
    (hθ : θ ∈ Irr H) (hne : θ ≠ 1) :
    cfInner (indClassFun H θ) (indClassFun H (1 : H → ℂ)) = 0 :=
  cfInner_indClassFun_indClassFun_eq_zero H hθ one_mem_Irr fun t ht => by
    rw [conjClassFun_one_right] at ht
    exact hne ht.symm

theorem cfInner_indClassFun_one [Fintype L] {θ : H → ℂ} (hθ : θ ∈ Irr H) (hne : θ ≠ 1) :
    cfInner (indClassFun H θ) (1 : L → ℂ) = 0 := by
  have : Fintype H := Fintype.ofFinite _
  rw [cfInner_indClassFun H θ (Irr_subset_classFun one_mem_Irr), resClassFun_one]
  exact cfInner_eq_zero_of_mem_Irr hθ one_mem_Irr hne

theorem indFam_diff_singleton [Fintype L] [H.Normal] :
    indFam H (Irr H) \ {indClassFun H (1 : H → ℂ)} = indFam H (Irr H \ {1}) := by
  ext f
  simp only [Set.mem_sdiff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hf, hne⟩
    obtain ⟨θ, hθ, rfl⟩ := (mem_indFam H).1 hf
    exact (mem_indFam H).2 ⟨θ, ⟨hθ, fun h => hne (by rw [h])⟩, rfl⟩
  · intro hf
    obtain ⟨θ, ⟨hθ, hθ1⟩, rfl⟩ := (mem_indFam H).1 hf
    refine ⟨indClassFun_mem_indFam H hθ, fun h => ?_⟩
    obtain ⟨t, ht⟩ := (indClassFun_eq_iff_exists_conjClassFun H hθ one_mem_Irr).1 h
    rw [conjClassFun_one_right] at ht
    exact hθ1 ht.symm

theorem cfInner_indClassFun_one_of_mem_indFam_diff [Fintype L] [H.Normal] {ξ : L → ℂ}
    (hξ : ξ ∈ indFam H (Irr H) \ {indClassFun H (1 : H → ℂ)}) :
    cfInner ξ (indClassFun H (1 : H → ℂ)) = 0 := by
  rw [indFam_diff_singleton] at hξ
  obtain ⟨θ, ⟨hθ, hθ1⟩, rfl⟩ := (mem_indFam H).1 hξ
  exact cfInner_indClassFun_indClassFun_one H hθ hθ1

theorem cfInner_one_of_mem_indFam_diff [Fintype L] [H.Normal] {ξ : L → ℂ}
    (hξ : ξ ∈ indFam H (Irr H) \ {indClassFun H (1 : H → ℂ)}) :
    cfInner ξ (1 : L → ℂ) = 0 := by
  rw [indFam_diff_singleton] at hξ
  obtain ⟨θ, ⟨hθ, hθ1⟩, rfl⟩ := (mem_indFam H).1 hξ
  exact cfInner_indClassFun_one H hθ hθ1

end NormalInducedFamily

end CFSG.FeitThompson
