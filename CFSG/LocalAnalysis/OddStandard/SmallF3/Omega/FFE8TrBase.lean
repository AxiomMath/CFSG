module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8TrBaseAux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8Def
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PTheta

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G] {K : Subgroup G}

@[expose] noncomputable def ffOutFFE8TrRho (hQ : Q.Nondegenerate)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* omegaProj hQ) : ↥K →* ProjSim Q :=
  (ffOmegaToSim hQ).comp (ff6mPhi e)

theorem ffOutFFE8TrRho_apply (hQ : Q.Nondegenerate)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* omegaProj hQ) (l : ↥K) :
    ffOutFFE8TrRho hQ e l = ffOmegaToSim hQ (ff6mPhi e l) :=
  rfl

theorem ffOutFFE8TrRho_injective (hQ : Q.Nondegenerate) (hz : Subgroup.center ↥K = ⊥)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* omegaProj hQ) :
    Function.Injective (ffOutFFE8TrRho hQ e) :=
  (ffOmegaToSim_injective hQ).comp (ff6p_phi_injective hQ hz e)

theorem ffOutFFE8TrRho_range (hQ : Q.Nondegenerate)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* omegaProj hQ) :
    (ffOutFFE8TrRho hQ e).range = ffOmegaSim hQ := by
  ext x
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨ff6mPhi e l, rfl⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨l, rfl⟩ := ff6mPhi_surjective e w
    exact ⟨l, rfl⟩

theorem ffOutFFE8Tr_finite_projSim (Q : QuadraticForm (ZMod 3) V) : Finite (ProjSim Q) := by
  haveI : Finite V := Module.finite_of_finite (ZMod 3)
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun f : V ≃ₗ[ZMod 3] V => (f : V → V))
      (fun f g h => LinearEquiv.ext (congrFun h))
  haveI : Finite (simGroup Q) := Subtype.finite
  infer_instance

theorem ffOutFFE8TrThetaImg_eq (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (e : ↥K ⧸ Subgroup.center ↥K ≃* omegaProj hQ) {S : Subgroup G}
    (hS : S ≤ K) :
    ffThetaImg (ffTheta6P hQ hdim hsgn e) S = ffImg (ffOutFFE8TrRho hQ e) S := by
  have h := ffThetaImg_cap_six_plus hQ hdim hsgn e S
  rw [inf_of_le_left hS] at h
  rw [h]
  unfold ffImg ffOutFFE8TrRho
  exact (Subgroup.map_map _ _ _)

theorem ffOutFFE8Tr_sdata (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (hz : Subgroup.center ↥K = ⊥)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* omegaProj hQ) {E : Subgroup G} {z ν : G}
    (hE : IsElemAb2 E 3) (hEK : E ≤ K) (hzE : z ∈ E) (hνK : ν ∈ K) (hν3 : orderOf ν = 3)
    (hνN : ν ∈ normalizer (E : Set G)) (hfix : ∀ x ∈ E, ν * x = x * ν → x = 1 ∨ x = z)
    (hzT : SimHasType (ffOutFFE8TrRho hQ e ⟨z, hEK hzE⟩) 4 1) :
    FFE8SData hQ (ffThetaImg (ffTheta6P hQ hdim hsgn e) E) (ffOutFFE8TrRho hQ e ⟨z, hEK hzE⟩)
      (ffOutFFE8TrRho hQ e ⟨ν, hνK⟩) := by
  have hρ : Function.Injective (ffOutFFE8TrRho hQ e) := ffOutFFE8TrRho_injective hQ hz e
  have hνnorm : ffOutFFE8TrRho hQ e ⟨ν, hνK⟩ ∈
      normalizer ((ffThetaImg (ffTheta6P hQ hdim hsgn e) E : Subgroup (ProjSim Q)) :
        Set (ProjSim Q)) := by
    have h1 := ffOutFFE8TrMap_mem_normalizer (ffTheta6P hQ hdim hsgn e) (T := E)
      (Subgroup.le_normalizer hνK) hνN
    have h2 : ffTheta6P hQ hdim hsgn e ⟨ν, Subgroup.le_normalizer hνK⟩ =
        ffOutFFE8TrRho hQ e ⟨ν, hνK⟩ := ffTheta6P_of_mem hQ hdim hsgn e ⟨ν, hνK⟩
    rwa [h2] at h1
  rw [ffOutFFE8TrThetaImg_eq hQ hdim hsgn e hEK] at hνnorm ⊢
  refine ⟨?_, ffOutFFE8TrImg_elemAb2 hρ hEK hE, mem_ffImg_iff.mpr ⟨⟨z, hEK hzE⟩, hzE, rfl⟩,
    hzT, ?_, ?_, hνnorm, ?_⟩
  · rw [← ffOutFFE8TrRho_range hQ e]
    exact ffOutFFE8TrImg_le_range E
  · rw [← ffOutFFE8TrRho_range hQ e]
    exact ⟨⟨ν, hνK⟩, rfl⟩
  · rw [orderOf_injective _ hρ ⟨ν, hνK⟩]
    rw [← hν3]
    exact (Subgroup.orderOf_coe ⟨ν, hνK⟩).symm
  · intro x' hx' hcomm
    obtain ⟨l, hlE, rfl⟩ := mem_ffImg_iff.mp hx'
    have h1 : (⟨ν, hνK⟩ : ↥K) * l = l * ⟨ν, hνK⟩ := hρ (by rw [map_mul, map_mul]; exact hcomm)
    have h2 : ν * (l : G) = (l : G) * ν := congrArg Subtype.val h1
    rcases hfix l hlE h2 with h | h
    · left
      have h3 : l = 1 := Subtype.ext h
      rw [h3, map_one]
    · right
      have h3 : l = ⟨z, hEK hzE⟩ := Subtype.ext h
      rw [h3]

end CFSG.OddStandard.SmallF3.Omega
