module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8TrBase
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGPocketCover
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGPocketSix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

section Generic

variable {G H : Type} [Group G] [Group H] {K : Subgroup G}

theorem ffOutFFE8TrCent_mem_centralizer_iff {ρ : ↥K →* H} (hρ : Function.Injective ρ)
    {E : Subgroup G} (hEK : E ≤ K) (x : ↥K) :
    ρ x ∈ centralizer (ffImg ρ E : Set H) ↔ (x : G) ∈ centralizer (E : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h g hg
    have h1 := h (ρ ⟨g, hEK hg⟩) (mem_ffImg_iff.mpr ⟨⟨g, hEK hg⟩, hg, rfl⟩)
    have h2 : (⟨g, hEK hg⟩ : ↥K) * x = x * ⟨g, hEK hg⟩ :=
      hρ (by rw [map_mul, map_mul]; exact h1)
    exact congrArg Subtype.val h2
  · intro h y hy
    obtain ⟨l, hlE, rfl⟩ := mem_ffImg_iff.mp hy
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext (h l hlE))

theorem ffOutFFE8TrCent_pull_inf {ρ : ↥K →* H} (hρ : Function.Injective ρ) {E : Subgroup G}
    (hEK : E ≤ K) :
    ffOutFFE8TrPull ρ (ρ.range ⊓ centralizer (ffImg ρ E : Set H)) =
      K ⊓ centralizer (E : Set G) := by
  ext x
  rw [ffOutFFE8TrPull_mem_iff, Subgroup.mem_inf]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, (ffOutFFE8TrCent_mem_centralizer_iff hρ hEK ⟨x, hx⟩).mp (Subgroup.mem_inf.mp h).2⟩
  · rintro ⟨hx, hc⟩
    exact ⟨hx, Subgroup.mem_inf.mpr ⟨⟨⟨x, hx⟩, rfl⟩,
      (ffOutFFE8TrCent_mem_centralizer_iff hρ hEK ⟨x, hx⟩).mpr hc⟩⟩

end Generic

section Model

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G] [Finite G] {K : Subgroup G}

theorem ffOutFFE8TrCent_simHasType (hK : IsOm6P K) (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* omegaProj hQ) {z : G} (hzK : z ∈ K)
    (hzI : IsI4PlusIn K z) : SimHasType (ffOutFFE8TrRho hQ e ⟨z, hzK⟩) 4 1 := by
  have hP : IsI4PlusIn (⊤ : Subgroup ↥(omegaProj hQ)) (ff6mPhi e ⟨z, hzK⟩) :=
    (fg_isI4PlusIn_iff_of_cover (ff6m_phi_cover e (ff6p_odd_center hK)) hzK hzI.1).mp hzI
  rw [ffOutFFE8TrRho_apply, ffOmegaToSim_apply]
  exact simHasType_projOrthToProjSim (fg_hasType_of_isI4PlusIn_top_six_plus hQ hdim hsgn hP)

theorem ffOutFFE8TrCent_theta_mem_centralizer (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (hz : Subgroup.center ↥K = ⊥) (e : ↥K ⧸ Subgroup.center ↥K ≃* omegaProj hQ) {x : G}
    (hxN : x ∈ normalizer (K : Set G)) {E : Subgroup G} (hx : ∀ g ∈ E, x * g = g * x) :
    ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩ ∈
      centralizer (ffImg (ffOutFFE8TrRho hQ e) E : Set (ProjSim Q)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨l, hlE, rfl⟩ := mem_ffImg_iff.mp hy
  rw [ffOutFFE8TrRho_apply]
  exact ((ff6p_commute_iff hQ hdim hsgn hz e hxN l).mp (hx l hlE)).symm

end Model

end CFSG.OddStandard.SmallF3.Omega
