module

public import CFSG.ClassicalInvolution.Q3.Q3TMFSBasic
public import CFSG.ClassicalInvolution.Q3.Q3TMFSSl2

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T.MFS

open CFSG CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups

variable {Y : Type} [Group Y] [Finite Y] {z : Y} {L T : Subgroup Y}

omit [Finite Y] in
theorem memberIndex_cases [T.Normal] (hL : IsClassicalMember3 L z) :
    memberIndex L T = 1 ∨ memberIndex L T = 3 ∨ memberIndex L T = 12 ∨ memberIndex L T = 24 := by
  obtain ⟨e⟩ := hL.nonempty_equiv
  let O : Subgroup L := classicalInvolutionOddCore L
  have hOn : O.Normal := inferInstance
  let φ : L →* SL(2, ZMod 3) :=
    (e : L ⧸ O →* SL(2, ZMod 3)).comp (QuotientGroup.mk' O)
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective O)
  have hker : φ.ker = O := by
    ext x
    simp [φ]
  let N : Subgroup L := T.subgroupOf L ⊔ O
  have hNn : N.Normal := inferInstance
  have hle : φ.ker ≤ N := hker ▸ le_sup_right
  have hcomap : (N.map φ).comap φ = N := Subgroup.comap_map_eq_self hle
  have hNm : (N.map φ).Normal := hNn.map φ hφs
  have hcases := normal_sl2Three_index_cases (N.map φ)
  have hidx : (N.map φ).index = N.index := by
    rw [← Subgroup.index_comap_of_surjective (N.map φ) hφs, hcomap]
  have : memberIndex L T = N.index := rfl
  rw [this, ← hidx]
  exact hcases

end CFSG.ClassicalInvolution.Q3.Q3T.MFS
