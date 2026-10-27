module

public import CFSG.ClassicalInvolution.Asc77.AscT8LayerRes

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8V

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {J T : Subgroup G} {z t : G}

theorem T_le_cenZE (hTz : T ≤ Subgroup.centralizer ({z} : Set G))
    (hTt : T ≤ Subgroup.centralizer ({t} : Set G)) : T ≤ T8.cenZ (z * t) := by
  intro x hx
  rw [T8.mem_cenZ_iff]
  have h1 : x * z = z * x :=
    Subgroup.mem_centralizer_singleton_iff.mp (hTz hx)
  have h2 : x * t = t * x :=
    Subgroup.mem_centralizer_singleton_iff.mp (hTt hx)
  calc x * (z * t) = (x * z) * t := by group
    _ = (z * x) * t := by rw [h1]
    _ = z * (x * t) := by group
    _ = z * (t * x) := by rw [h2]
    _ = (z * t) * x := by group

theorem xMem_JE (hcl : ConjInvariant Ω) (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M)
    (hJΩ : J ∈ Ω) (ht : IsUniqueInvolution J t) (hc : z * t = t * z) (hTsyl : IsSylow2In T J)
    (hTle : T ≤ T8.cenZ (z * t)) : T8.XMem Ω (z * t) J := by
  refine ⟨hJΩ, ?_, T, hTsyl, fun r hr => (T8.mem_cenZ_iff.mp (hTle hr))⟩
  have haz : z * t ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc z * t * t = (t * z) * t := by rw [hc]
      _ = t * (z * t) := by group
  exact T8.centralizer_le_normalizer_of_noTwins hcl hJΩ (hnt _ hJΩ) ht haz

end T8V

end CFSG.ClassicalInvolution.Asc77
