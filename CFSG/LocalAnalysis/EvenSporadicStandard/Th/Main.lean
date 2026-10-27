module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.DataTh
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Reduction

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup CFSG.Blueprint.NativeSporadic

@[expose] def ThCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ (F : Subgroup G) (t : G), IsSporadic F .Th → orderOf t = 2 →
      centralizer ({t} : Set G) = F ⊔ zpowers t → (∀ g : G, g⁻¹ * t * g ∉ F) → False

section Certified


theorem th_not_standard_of_core (core : ThCore) {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (h : StdHyp G L) : ¬ IsSporadic L .Th := by
  rintro ⟨e⟩
  have hD : ThData ↥L := ThData.of_mulEquiv e thData_th
  obtain ⟨R, t, H⟩ := exists_thCyc h hD
  exact core G H.simple H.nonabelian L t ⟨e⟩ H.order_two H.centralizer_eq_zpowers
    H.not_conj_mem

end Certified

end CFSG.EvenSporadicStandard.ThStd
