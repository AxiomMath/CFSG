module

public import CFSG.ClassicalInvolution.Asc77.AscT8YC4Eng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.MuTab T8YY

namespace T8ZZ

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J W : Subgroup G} {z t : G}

theorem frame_xMemE (hcl : ConjInvariant Ω) (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M)
    (hcommW : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (F : FrameData Ω W K J z t)
    (hzt : z * t = F.zz 0 * F.zz 1) (hcen : ∀ i : Fin 4, (F.ρ i).R ≤ T8.cenZ (z * t))
    (i : Fin 4) : T8.XMem Ω (z * t) (F.ρ i).K := by
  refine ⟨(F.ρ i).hK, ?_, (F.ρ i).R, (F.ρ i).hRK, fun r hr => ?_⟩
  · have hcomm : z * t ∈ Subgroup.centralizer ({F.zz i} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff, hzt]
      refine Eq.symm ?_
      calc F.zz i * (F.zz 0 * F.zz 1) = (F.zz i * F.zz 0) * F.zz 1 := by group
        _ = (F.zz 0 * F.zz i) * F.zz 1 := by rw [F.zz_comm_of hcommW i 0]
        _ = F.zz 0 * (F.zz i * F.zz 1) := by group
        _ = F.zz 0 * (F.zz 1 * F.zz i) := by rw [F.zz_comm_of hcommW i 1]
        _ = F.zz 0 * F.zz 1 * F.zz i := by group
    exact T8.centralizer_le_normalizer_of_noTwins hcl (F.ρ i).hK
      (hnt _ (F.ρ i).hK) (F.hz i) hcomm
  · exact T8.mem_cenZ_iff.mp (hcen i hr)

end T8ZZ

end CFSG.ClassicalInvolution.Asc77
