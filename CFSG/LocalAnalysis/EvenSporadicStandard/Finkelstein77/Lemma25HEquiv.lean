module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement

public section

namespace CFSG.EvenSporadicStandard.Finkelstein77.Lemma25HProof

open Subgroup CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G]

theorem isDihedral_of_mulEquiv {A B : Subgroup G} (e : A ≃* B) (h : IsDihedralTwoGroup B) :
    IsDihedralTwoGroup A := by
  obtain ⟨n, hn, ⟨f⟩⟩ := h
  exact ⟨n, hn, ⟨e.trans f⟩⟩

theorem isSemidihedral_of_mulEquiv {A B : Subgroup G} (e : A ≃* B)
    (h : IsSemidihedralTwoGroup B) : IsSemidihedralTwoGroup A := by
  obtain ⟨n, hn, ⟨f⟩⟩ := h
  exact ⟨n, hn, ⟨e.trans f⟩⟩

noncomputable def mulEquivConj (P : Subgroup G) (k : G) :
    P ≃* P.map (MulAut.conj k⁻¹).toMonoidHom :=
  (MulAut.conj k⁻¹).subgroupMap P

end CFSG.EvenSporadicStandard.Finkelstein77.Lemma25HProof
