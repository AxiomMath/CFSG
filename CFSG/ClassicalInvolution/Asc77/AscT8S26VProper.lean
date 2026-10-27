module

public import CFSG.ClassicalInvolution.Asc77.AscT8S26Hull
public import CFSG.ClassicalInvolution.Asc77.AscT8S26UTyp

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem s26_omegaNbrGen_le_sigmaNorm (hΩ : ConjInvariant Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    omegaNbrGen Ω K ≤ sigmaNorm Ω K :=
  iSup₂_le fun _ hM => s26_le_sigmaNorm_of_mem_dComp hΩ hK (T8.mem_dComp_of_mem_omegaNbr hM)

variable {p f : ℕ} [Fact p.Prime]

theorem s26XProper_proved : S26XProper p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc _ htop
  have hle := s26_omegaNbrGen_le_sigmaNorm hs.stand.hyp.conjInvariant hs.stand.mem
  rw [htop, top_le_iff] at hle
  exact hdisc (dConnected_of_sigmaNorm_eq_top hs.stand.mem hs.stand.trans hle)

end CFSG.ClassicalInvolution.Asc77
