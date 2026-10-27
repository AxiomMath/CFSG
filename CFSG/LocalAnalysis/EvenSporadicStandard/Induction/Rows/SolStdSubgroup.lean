module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Last
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Lemma36Q

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Junction

variable {H : Type} [Group H] {N L : Subgroup H}

theorem solStd_subgroupOf [Finite H] (hLN : L ≤ N) {r : H} (hrN : r ∈ N) (hr2 : orderOf r = 2)
    (hrC : r ∈ centralizer (L : Set H)) (h : SolStd L) : SolStd (L.subgroupOf N) := by
  have hLC : L ≤ centralizer ({r} : Set H) := fun l hl =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hrC l hl)
  obtain ⟨t₀, -, hcomp₀⟩ := h.2
  have hcomp : IsCompIn L (centralizer ({r} : Set H)) :=
    isCompIn_of_normal hLC hcomp₀.isQuasisimple
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLC).2 (h.centralizer_le_normalizer hrC hr2))
  have hcomp2 := isCompIn_subgroupOf (isCompIn_of_le hcomp (le_inf hLC hLN) inf_le_left)
    (inf_le_right : centralizer ({r} : Set H) ⊓ N ≤ N)
  have hcen : (centralizer ({r} : Set H) ⊓ N).subgroupOf N =
      centralizer ({(⟨r, hrN⟩ : ↥N)} : Set ↥N) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_centralizer_singleton_iff,
      mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h, -⟩
      exact Subtype.ext h
    · intro h
      exact ⟨congrArg Subtype.val h, x.2⟩
  refine ⟨stdBare_subgroupOf_of_stdBare hLN h.1, ⟨r, hrN⟩,
    by rw [Subgroup.orderOf_mk]; exact hr2, ?_⟩
  rwa [hcen] at hcomp2

end CFSG.EvenSporadicStandard.Induction
