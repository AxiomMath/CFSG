module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PTheta
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSMono

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G] {L : Subgroup G}

private theorem ffOutFF6PSyl1_relIndex_map_dvd {M P : Type*} [Group M] [Group P]
    (f : M →* P) (A B : Subgroup M) :
    (A.map f).relIndex (B.map f) ∣ A.relIndex B := by
  have hB : B.map f = (f.comp B.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hB, ← Subgroup.index_comap]
  exact Subgroup.index_dvd_of_le fun b hb =>
    Subgroup.mem_comap.mpr (Subgroup.mem_map.mpr ⟨b, hb, rfl⟩)

theorem ff6p_thetaImg_isSylow2Of (θ : ↥(Subgroup.normalizer (L : Set G)) →* ProjSim Q)
    {H S₁ : Subgroup G} (hHN : H ≤ Subgroup.normalizer (L : Set G)) (hS : IsSylow2Of S₁ H) :
    IsSylow2Of (ffThetaImg θ S₁) (ffThetaImg θ H) := by
  refine ⟨?_, ffThetaImg_isPGroup θ hS.2.1, ?_⟩
  · intro q hq
    obtain ⟨s, hs, hsS, rfl⟩ := mem_ffThetaImg_iff.mp hq
    exact mem_ffThetaImg_iff.mpr ⟨s, hs, hS.1 hsS, rfl⟩
  · intro hdvd
    have hdvd' : (ffThetaImg θ S₁).relIndex (ffThetaImg θ H) ∣ S₁.relIndex H := by
      have h := ffOutFF6PSyl1_relIndex_map_dvd θ
        (S₁.subgroupOf (Subgroup.normalizer (L : Set G)))
        (H.subgroupOf (Subgroup.normalizer (L : Set G)))
      rw [Subgroup.relIndex_subgroupOf hHN] at h
      simpa only [ffThetaImg] using h
    exact hS.2.2 (hdvd.trans hdvd')

theorem ff6p_ts_mem_thetaImg [Finite G] (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (fr : PFrame Q (Option (Fin 5)) ffC)
    {H S₁ : Subgroup G} (hHN : H ≤ Subgroup.normalizer (L : Set G)) (hS : IsSylow2Of S₁ H)
    (hP : ffImg (ff6mPhi e) (S₁ ⊓ L) = ffP1p hQ fr)
    (hts : ffTs fr ∈ ffThetaImg (ffTheta6P hQ hdim hsgn e) H) :
    ffTs fr ∈ ffThetaImg (ffTheta6P hQ hdim hsgn e) S₁ := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  haveI : Finite V := Module.finite_of_finite (ZMod 3)
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun f : V ≃ₗ[ZMod 3] V => (f : V → V))
      (fun f g h => LinearEquiv.ext (congrFun h))
  haveI : Finite (simGroup Q) := Subtype.finite
  haveI : Finite (ProjSim Q) := inferInstance
  let T : Subgroup (ProjSim Q) := ffThetaImg (ffTheta6P hQ hdim hsgn e) H ⊓
    Subgroup.normalizer (((ffP1p hQ fr).map (ffOmegaToSim hQ) :
      Subgroup (ProjSim Q)) : Set (ProjSim Q))
  have hT2 : IsPGroup 2 T := by
    refine ff6p_normalizer_isPGroup hQ hdim hsgn h2 fr T ?_
    intro x hx
    exact ff6p_act_map_eq_of_normalizes hQ h2 (Subgroup.mem_inf.mp hx).2
  have hSylow : IsSylow2Of (ffThetaImg (ffTheta6P hQ hdim hsgn e) S₁)
      (ffThetaImg (ffTheta6P hQ hdim hsgn e) H) :=
    ff6p_thetaImg_isSylow2Of (ffTheta6P hQ hdim hsgn e) hHN hS
  have hsub : ffImg (ff6mPhi e) (S₁ ⊓ L) = ffImg (ff6mPhi e) S₁ := by
    rw [ffImg, ffImg, Subgroup.inf_subgroupOf_right]
  have hsub' : ffImg (ff6mPhi e) S₁ = ffP1p hQ fr := hsub.symm.trans hP
  have hcap' : ffThetaImg (ffTheta6P hQ hdim hsgn e) (S₁ ⊓ L) =
      (ffP1p hQ fr).map (ffOmegaToSim hQ) := by
    rw [ffThetaImg_cap_six_plus hQ hdim hsgn e S₁, hsub']
  have hleT : ffThetaImg (ffTheta6P hQ hdim hsgn e) S₁ ≤ T := by
    refine le_inf ?_ ?_
    · intro q hq
      obtain ⟨s, hs, hsS, rfl⟩ := mem_ffThetaImg_iff.mp hq
      exact mem_ffThetaImg_iff.mpr ⟨s, hs, hS.1 hsS, rfl⟩
    · intro x hx
      have hx' := ffThetaImg_le_normalizer (ffTheta6P hQ hdim hsgn e)
        (hS.1.trans hHN) hx
      rwa [hcap'] at hx'
  have hEq : T = ffThetaImg (ffTheta6P hQ hdim hsgn e) S₁ :=
    IsSylow2Of.eq_of_le hSylow
      (show T ≤ ffThetaImg (ffTheta6P hQ hdim hsgn e) H from inf_le_left) hT2 hleT
  have htsT : ffTs fr ∈ T := by
    refine Subgroup.mem_inf.mpr ⟨hts, ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hy
      have hcomm := ffTs_comm_normalizer hQ h2 hπ fr (ffP1p_le_normalizer hQ hπ fr hp)
      have heq : ffTs fr * ffOmegaToSim hQ p * (ffTs fr)⁻¹ = ffOmegaToSim hQ p := by
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rw [heq]
      exact Subgroup.mem_map_of_mem (ffOmegaToSim hQ) hp
    · intro hy
      obtain ⟨p, hp, hpeq⟩ := Subgroup.mem_map.mp hy
      have hcomm := ffTs_comm_normalizer hQ h2 hπ fr (ffP1p_le_normalizer hQ hπ fr hp)
      have heq : y = ffOmegaToSim hQ p := by
        calc y = (ffTs fr)⁻¹ * (ffTs fr * y * (ffTs fr)⁻¹) * ffTs fr := by group
          _ = (ffTs fr)⁻¹ * ffOmegaToSim hQ p * ffTs fr := by rw [hpeq]
          _ = ffOmegaToSim hQ p := by
                rw [mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [heq]
      exact Subgroup.mem_map_of_mem (ffOmegaToSim hQ) hp
  rwa [← hEq]

theorem ff6p_outer_in_sylow [Finite G] (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (fr : PFrame Q (Option (Fin 5)) ffC)
    {H S₁ : Subgroup G} (hLH : L ≤ H) (hHN : H ≤ Subgroup.normalizer (L : Set G))
    (hS : IsSylow2Of S₁ H) (hP : ffImg (ff6mPhi e) (S₁ ⊓ L) = ffP1p hQ fr) {h : G} (hhH : h ∈ H)
    (hxG : SimInGStar (ffTheta6P hQ hdim hsgn e ⟨h, hHN hhH⟩))
    (hxΩ : ¬ SimInOmegaStar hQ (ffTheta6P hQ hdim hsgn e ⟨h, hHN hhH⟩)) :
    ∃ (y : G) (hy : y ∈ Subgroup.normalizer (L : Set G)), y ∈ S₁ ∧
      ffTheta6P hQ hdim hsgn e ⟨y, hy⟩ = ffTs fr := by
  have hxH : ffTheta6P hQ hdim hsgn e ⟨h, hHN hhH⟩ ∈
      ffThetaImg (ffTheta6P hQ hdim hsgn e) H :=
    mem_ffThetaImg_iff.mpr ⟨h, hHN hhH, hhH, rfl⟩
  obtain ⟨n, hn⟩ := ff6p_ts_mem_of_outer hQ hdim hsgn fr hxG hxΩ
  have hιH : ffOmegaToSim hQ n ∈ ffThetaImg (ffTheta6P hQ hdim hsgn e) H :=
    ff6p_iota_mem_thetaImg hQ hdim hsgn e hLH n
  have htsH : ffTs fr ∈ ffThetaImg (ffTheta6P hQ hdim hsgn e) H := by
    rw [hn]
    exact Subgroup.mul_mem _ hιH hxH
  have htsS₁ : ffTs fr ∈ ffThetaImg (ffTheta6P hQ hdim hsgn e) S₁ :=
    ff6p_ts_mem_thetaImg hQ hdim hsgn e fr hHN hS hP htsH
  obtain ⟨y, hy, hyS, hyθ⟩ := mem_ffThetaImg_iff.mp htsS₁
  exact ⟨y, hy, hyS, hyθ⟩

end CFSG.OddStandard.SmallF3.Omega
