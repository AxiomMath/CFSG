module

public import CFSG.ClassicalInvolution.Asc77.AscT8YC4Eng
public import CFSG.ClassicalInvolution.Asc77.AscT8RepEng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.MuTab T8YY

namespace T8ZZ

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J W : Subgroup G} {z t : G}

theorem frame_rep_le_cen_zE (H : T8V.RepHooks Ω W) (F : FrameData Ω W K J z t) (i : Fin 4) :
    (F.ρ i).R ≤ T8.cenZ z := by
  intro r hr
  rw [T8.mem_cenZ_iff]
  have h : (F.ρ i).R ≤ Subgroup.centralizer ({F.zz 0} : Set G) := by
    by_cases hi : i = 0
    · subst hi
      exact T8V.rep_le_centralizerE H (F.ρ 0) (F.ρ 0) (Or.inl rfl) (F.hz 0)
    · exact T8V.rep_le_centralizerE H (F.ρ i) (F.ρ 0) (Or.inr (F.hadj i 0 hi)) (F.hz 0)
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (h hr)
  rw [F.hz0] at h1
  exact h1

theorem frame_xMem_zE (hcl : ConjInvariant Ω) (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M)
    (hcommW : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (F : FrameData Ω W K J z t)
    (hcen : ∀ i : Fin 4, (F.ρ i).R ≤ T8.cenZ z) (i : Fin 4) : T8.XMem Ω z (F.ρ i).K := by
  refine ⟨(F.ρ i).hK, ?_, (F.ρ i).R, (F.ρ i).hRK,
    fun r hr => T8.mem_cenZ_iff.mp (hcen i hr)⟩
  have hcomm : z ∈ Subgroup.centralizer ({F.zz i} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := F.zz_comm_of hcommW 0 i
    rw [F.hz0] at h
    exact h
  exact T8.centralizer_le_normalizer_of_noTwins hcl (F.ρ i).hK (hnt _ (F.ρ i).hK)
    (F.hz i) hcomm

theorem oddCore_z_commutes_nbrE {s : G} (hz : IsUniqueInvolution K z)
    {Y : Subgroup G} (hoY : oddCoreOf Y ≤ oddCoreOf (Subgroup.centralizer ({z} : Set G)))
    (hα' : alphaOf (Subgroup.closure ({s, z} : Set G)) = ⊥) {n : G} (hn : n ∈ oddCoreOf Y) :
    n * s = s * n := by
  have hnC : n ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) := hoY hn
  have hzA : z ∈ Subgroup.closure ({s, z} : Set G) := Subgroup.subset_closure (by simp)
  have hsA : s ∈ Subgroup.closure ({s, z} : Set G) := Subgroup.subset_closure (by simp)
  exact T8.oddCoreOf_centralizer_commutes hα' hzA hz.ne_one hsA n hnC

end T8ZZ

end CFSG.ClassicalInvolution.Asc77
