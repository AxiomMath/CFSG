module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Lift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeZ2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Inputs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem inF_pocketable_or_isLnEps3 [Finite G] (hG1 : Asc82NoQ8InL2) {I : Subgroup G}
    (hI : InFStar I) {f' : QuaternionGroup 2 →* ↥I ⧸ oddCore ↥I} (hf' : Function.Injective f') :
    (InF I ∧ PocketableQuotient (↥I ⧸ oddCore ↥I)) ∨ IsLnEps3 I := by
  have h := hI
  unfold InFStar IsFStarGroup IsFGroup at h
  rcases h with ⟨hq, hΩ | hT⟩ | ⟨-, h9 | h81 | h3 | hU3⟩
  · have hF : InF I := ⟨hq, Or.inl hΩ⟩
    rcases hΩ with h | h | h | h | h | h
    · exact Or.inl ⟨hF, Or.inl h⟩
    · exact Or.inr ⟨4, Or.inl h⟩
    · exact Or.inr ⟨4, Or.inr h⟩
    · exact Or.inl ⟨hF, Or.inr (Or.inl h)⟩
    · exact Or.inl ⟨hF, Or.inr (Or.inr (Or.inl h))⟩
    · exact Or.inl ⟨hF, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
  · exact Or.inl ⟨⟨hq, Or.inr hT⟩, Or.inr (Or.inr (Or.inr (Or.inr
      ⟨isQuasisimple_quotient_oddCore hq, hT⟩)))⟩
  · exact (hG1 _ (Or.inl h9) f' hf').elim
  · exact (hG1 _ (Or.inr h81) f' hf').elim
  · exact Or.inr ⟨3, Or.inl h3⟩
  · exact Or.inr ⟨3, Or.inr hU3⟩

theorem isI4PlusIn_of_quotient [Finite G] {I : Subgroup G} {y : G} (hyI : y ∈ I)
    (hy : orderOf y = 2)
    (h : IsI4PlusIn (⊤ : Subgroup (↥I ⧸ oddCore ↥I)) (QuotientGroup.mk (⟨y, hyI⟩ : ↥I))) :
    IsI4PlusIn I y := by
  refine isI4PlusIn_of_top hyI (isI4PlusIn_top_of_quotient ?_ h)
  rw [Subgroup.orderOf_mk]
  exact hy

end CFSG.OddStandard.SmallF3.Omega
