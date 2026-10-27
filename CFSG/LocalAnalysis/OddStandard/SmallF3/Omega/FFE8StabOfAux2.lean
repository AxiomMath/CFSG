module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8Std
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8TrBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G] [Finite G] {K : Subgroup G}

theorem ffOutFFE8TrStab_thetaImg_P (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* omegaProj hQ) (fr : PFrame Q (Option (Fin 5)) ffC)
    {P : Subgroup G} (hPK : P ≤ K) (hPφ : ffImg (ff6mPhi e) P = ffP1p hQ fr) :
    ffThetaImg (ffTheta6P hQ hdim hsgn e) P = ffP1Sim hQ fr := by
  have h := ffThetaImg_cap_six_plus hQ hdim hsgn e P
  rw [inf_of_le_left hPK, hPφ] at h
  exact h

theorem ffOutFFE8TrStab_rho_z (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (hz0 : Subgroup.center ↥K = ⊥)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* omegaProj hQ) (fr : PFrame Q (Option (Fin 5)) ffC)
    {P : Subgroup G} (hPφ : ffImg (ff6mPhi e) P = ffP1p hQ fr) {z : G} (hzP : z ∈ centerIn P)
    (hzK : z ∈ K) (hz1 : z ≠ 1) : ffOutFFE8TrRho hQ e ⟨z, hzK⟩ = ffZ0Sim hQ fr := by
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.mp hzP
  have hcz' : (c : G) = z := hcz
  have hzPm : z ∈ P := by
    rw [← hcz']
    exact c.2
  have hcomm : ∀ m ∈ P, m * z = z * m := by
    intro m hm
    have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨m, hm⟩)
    rw [← hcz']
    exact h
  have hmem : ff6mPhi e ⟨z, hzK⟩ ∈ ffP1p hQ fr := by
    rw [← hPφ]
    exact mem_ffImg_iff.mpr ⟨⟨z, hzK⟩, hzPm, rfl⟩
  have hcent : ∀ h ∈ ffP1p hQ fr, h * ff6mPhi e ⟨z, hzK⟩ = ff6mPhi e ⟨z, hzK⟩ * h := by
    intro h hh
    rw [← hPφ] at hh
    obtain ⟨m, hmP, rfl⟩ := mem_ffImg_iff.mp hh
    rw [← map_mul, ← map_mul]
    exact congrArg (ff6mPhi e) (Subtype.ext (hcomm (m : G) hmP))
  rcases ffP1p_center hQ hπ fr hmem hcent with h1 | h1
  · exfalso
    have h2 : (⟨z, hzK⟩ : ↥K) = 1 := ff6p_phi_injective hQ hz0 e (by rw [h1, map_one])
    exact hz1 (congrArg Subtype.val h2)
  · rw [ffOutFFE8TrRho_apply, h1]
    rfl

theorem ffOutFFE8TrStab_restrict_injective (hK : IsOm6P K) (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* omegaProj hQ) {Y : Subgroup G}
    (hYK : Y ≤ normalizer (K : Set G)) (hYC : Y ⊓ centralizer (K : Set G) = ⊥) :
    Function.Injective ((ffTheta6P hQ hdim hsgn e).comp (Subgroup.inclusion hYK)) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have h1 : ffTheta6P hQ hdim hsgn e ⟨(y : G), hYK y.2⟩ = 1 := hy
  have h2 := (ff6p_theta_eq_one_iff hK hQ hdim hsgn e (hYK y.2)).mp h1
  have h3 : (y : G) ∈ Y ⊓ centralizer (K : Set G) := Subgroup.mem_inf.mpr ⟨y.2, h2⟩
  rw [hYC] at h3
  exact Subtype.ext (Subgroup.mem_bot.mp h3)

end CFSG.OddStandard.SmallF3.Omega
