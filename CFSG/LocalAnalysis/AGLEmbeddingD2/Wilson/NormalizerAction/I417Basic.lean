module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4L0Struct
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4 Subgroup

theorem theta_eq_bot_of_center_three {Y : Type*} [Group Y] [Finite Y] (hY : IsQuasisimple Y)
    (hZ : Nat.card (center Y) = 3) : aschbacherSolvableCore 3 Y = ⊥ := by
  obtain ⟨hsolv, hchar, h3, -⟩ := solvable_prime_complement_core_characterization
    (H := Y) Nat.prime_three
  set θ := aschbacherSolvableCore 3 Y with hθ
  haveI := hchar
  have hnorm : θ.Normal := inferInstance
  obtain ⟨-, hsimple, hna⟩ := hY
  haveI := hsimple
  have : Group.IsPerfect (Y ⧸ center Y) := isPerfect_of_simple_nonabelian hna
  have hmapnorm : (θ.map (QuotientGroup.mk' (center Y))).Normal :=
    hnorm.map _ (QuotientGroup.mk'_surjective _)
  have hle : θ ≤ center Y := by
    haveI := hmapnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (θ.map (QuotientGroup.mk' (center Y))) with h | h
    · intro x hx
      have : QuotientGroup.mk' (center Y) x ∈ θ.map (QuotientGroup.mk' (center Y)) := ⟨x, hx, rfl⟩
      rw [h, mem_bot] at this
      exact (QuotientGroup.eq_one_iff x).1 this
    · exfalso
      have hsolvmap : Group.IsSolvable (θ.map (QuotientGroup.mk' (center Y))) :=
        solvable_of_surjective (f := (QuotientGroup.mk' (center Y)).subgroupMap θ)
          ((QuotientGroup.mk' (center Y)).subgroupMap_surjective θ)
      rw [h] at hsolvmap
      have hs : Group.IsSolvable (Y ⧸ center Y) :=
        solvable_of_surjective (f := (topEquiv : (⊤ : Subgroup (Y ⧸ center Y)) ≃* _).toMonoidHom)
          (topEquiv.surjective)
      exact Group.IsPerfect.not_isSolvable _ hs
  have hdvd : Nat.card θ ∣ 3 := by
    rw [← hZ]
    exact Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3'
  · exact (Subgroup.card_eq_one).1 h1
  · exact absurd (by rw [h3']) h3

theorem inner_of_theta_inner {Y : Type*} [Group Y] [Finite Y] (hθ : aschbacherSolvableCore 3 Y = ⊥)
    (σ : MulAut Y)
    (h : thetaQuotMulAut Y σ ∈ (MulAut.conj : (Y ⧸ aschbacherSolvableCore 3 Y) →*
      MulAut (Y ⧸ aschbacherSolvableCore 3 Y)).range) : ∃ k : Y, σ = MulAut.conj k := by
  obtain ⟨kb, hkb⟩ := h
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 Y) kb
  refine ⟨k, MulEquiv.ext fun x => ?_⟩
  have h1 := congrArg (fun τ => τ (x : Y ⧸ aschbacherSolvableCore 3 Y)) hkb
  simp only [MulAut.conj_apply, thetaQuotMulAut_mk] at h1
  have h2 : ((σ x : Y) : Y ⧸ aschbacherSolvableCore 3 Y) =
      ((k * x * k⁻¹ : Y) : Y ⧸ aschbacherSolvableCore 3 Y) := by
    rw [← h1]
    rfl
  have h3 := QuotientGroup.eq.1 h2
  rw [hθ, mem_bot] at h3
  have : (σ x)⁻¹ * (k * x * k⁻¹) = 1 := h3
  rw [MulAut.conj_apply]
  exact inv_mul_eq_one.1 this

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
