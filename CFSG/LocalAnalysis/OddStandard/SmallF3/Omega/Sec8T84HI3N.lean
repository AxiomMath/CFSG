module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFThetaSylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HP1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G] {L : Subgroup G}

@[expose] noncomputable def sec8t84hImg {hQ : Q.Nondegenerate}
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (S : Subgroup G) : Subgroup (ProjOrth Q) :=
  (ffImg (ff6mPhi e) S).map (omegaProj hQ).subtype

theorem mem_sec8t84hImg_iff {hQ : Q.Nondegenerate}
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {S : Subgroup G} {y : ProjOrth Q} :
    y ∈ sec8t84hImg e S ↔
      ∃ l : ↥L, (l : G) ∈ S ∧ ((ff6mPhi e l : ↥(omegaProj hQ)) : ProjOrth Q) = y := by
  unfold sec8t84hImg
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, hwy⟩
    obtain ⟨l, hlS, hlw⟩ := mem_ffImg_iff.mp hw
    exact ⟨l, hlS, by rw [hlw]; simpa using hwy⟩
  · rintro ⟨l, hlS, hly⟩
    exact ⟨ff6mPhi e l, mem_ffImg_iff.mpr ⟨l, hlS, rfl⟩, hly⟩

theorem sec8t84hImg_sylow [Finite G] (hQ : Q.Nondegenerate)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    {S : Subgroup G} (hS : IsSylow2Of S (Subgroup.normalizer (L : Set G))) :
    IsSylow2Of (sec8t84hImg e S) (omegaProj hQ) := by
  unfold sec8t84hImg
  exact sec8t84h_isSylow2Of_map_subtype (omegaProj hQ) (ffThetaImg_sylow hQ e hodd hS)

theorem sec8t84hImg_normalizes (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {S : Subgroup G}
    (hS : S ≤ Subgroup.normalizer (L : Set G)) {y' : G} (hy'S : y' ∈ S) {x'' : ProjOrth Q}
    (hx : projOrthToProjSim Q x'' = ffTheta6M hQ hdim hsgn e ⟨y', hS hy'S⟩) :
    x'' ∈ Subgroup.normalizer ((sec8t84hImg e S : Subgroup (ProjOrth Q)) : Set (ProjOrth Q)) := by
  have hmem : ffTheta6M hQ hdim hsgn e ⟨y', hS hy'S⟩ ∈
      ffThetaImg (ffTheta6M hQ hdim hsgn e) S :=
    mem_ffThetaImg_iff.mpr ⟨y', hS hy'S, hy'S, rfl⟩
  have hnorm : ffTheta6M hQ hdim hsgn e ⟨y', hS hy'S⟩ ∈
      Subgroup.normalizer
        (ffThetaImg (ffTheta6M hQ hdim hsgn e) (S ⊓ L) : Set (ProjSim Q)) :=
    ffThetaImg_le_normalizer (ffTheta6M hQ hdim hsgn e) hS hmem
  have hcap : ffThetaImg (ffTheta6M hQ hdim hsgn e) (S ⊓ L) =
      (sec8t84hImg e S).map (projOrthToProjSim Q) := by
    rw [ffThetaImg_cap hQ hdim hsgn e S]
    unfold sec8t84hImg
    rw [Subgroup.map_map]
    rfl
  have hxnorm : projOrthToProjSim Q x'' ∈
      Subgroup.normalizer
        ((sec8t84hImg e S).map (projOrthToProjSim Q) : Set (ProjSim Q)) := by
    rw [← hcap, hx]
    exact hnorm
  exact sec8t84h_mem_normalizer_of_map (projOrthToProjSim Q)
    (projOrthToProjSim_injective (Q := Q)) hxnorm

end CFSG.OddStandard.SmallF3.Omega
