module

public import Certificates.Certificate33101

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four

theorem card_T0_ra : Nat.card L34Facts.T0 = 64 :=
  L34Facts.card_T0

theorem card_RA : Nat.card RA = 256 :=
  Certificates.certificate33101.1

theorem RA_le_R : RA ≤ R := by
  rw [RA, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, SetLike.mem_coe] at hx
  rcases hx with hx | rfl | rfl
  · exact S_le_R (L34Facts.T0_le_S hx)
  · exact g₅_mem_R
  · exact g₆_mem_R

theorem T0_le_RA : L34Facts.T0 ≤ RA := fun _ hx => Subgroup.subset_closure (Or.inl hx)

theorem RA_inf_S : RA ⊓ S = L34Facts.T0 :=
  Certificates.certificate33101.2

end CFSG.ComponentClassification.GrSLit.L34Tw
