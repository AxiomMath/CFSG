module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CDNorm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFThetaAdapt

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {V : Type} [AddCommGroup V]
  [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V}
  {hQ : Q.Nondegenerate}

theorem sec5c_adapt (hS : Asc82SchurU43) (hL : IsOm6Z2 L) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (h2 : 2 ≤ Module.finrank (ZMod 3) V) (fr : NFrame Q (Fin 6) 1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {t : G} (ht2 : orderOf t = 2)
    (htc : t ∈ centerIn L) {B : Subgroup G} (hBL : B ≤ L) (hB : IsElemAb2 B 5) (htB : t ∈ B) :
    ∃ y : ProjSim Q, ffImg (ff6mPhi (ffAdapt h2 e y)) B = ffB1 hQ fr := by
  obtain ⟨φ, hφ, he⟩ := t5_cover_of_model hS hL hdim hsgn e
  have hcov : OddCentralCover φ := hφ.oddCentralCover hL
  have hB2 : IsPGroup 2 B := IsPGroup.of_card (p := 2) (n := 5) hB.2
  have hE : IsElemAb2 (ffImg φ B) 5 := (ff_cover_elemAb2_iff hcov hBL hB2 5).mp hB
  have htL : t ∈ L := hBL htB
  have hπ : (⟨piOrth Q, ff_piOrth_mem_omegaGroup_six_minus hQ hdim hsgn⟩ :
      ↥(omegaGroup hQ)) ∈ ffImg φ B := by
    rw [mem_ffImg_iff]
    exact ⟨⟨t, htL⟩, htB, Subtype.ext (hφ.map_central hL htc ht2 htL)⟩
  have hU4 := sec5c_elemAb2_img hQ hdim hsgn hπ hE
  have hUeq : ffImg (ff6mPhi e) B = (ffImg φ B).map (omegaToProj hQ) := by
    have hcomp : ff6mPhi e = (omegaToProj hQ).comp φ :=
      MonoidHom.ext fun l => by rw [ff6mPhi_apply, he l]; rfl
    rw [hcomp]
    simp only [ffImg]
    exact (Subgroup.map_map _ _ _).symm
  obtain ⟨y, hy⟩ := ff_star_E16_conj hQ hdim hsgn h2 fr
    (U := ffImg (ff6mPhi e) B) (by rw [hUeq]; exact hU4)
  exact ⟨y, ffImg_ffAdapt h2 e y B (ffB1 hQ fr) hy⟩

theorem sec5c_img_B0 (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ} (hφ : IsCoverMap L φ)
    {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ}
    (he : ∀ l : ↥L, e (QuotientGroup.mk l) = omegaToProj hQ (φ l)) (fr : NFrame Q (Fin 6) 1)
    {t : G} (ht2 : orderOf t = 2) (htc : t ∈ centerIn L) {B : Subgroup G} (htB : t ∈ B)
    (hBL : B ≤ L) (hU : ffImg (ff6mPhi e) B = ffB1 hQ fr) :
    (∀ b : ↥L, (b : G) ∈ B → (φ b : OGroup Q) ∈ ffB0 fr) ∧
      ∀ g ∈ ffB0 fr, ∃ b : ↥L, (b : G) ∈ B ∧ (φ b : OGroup Q) = g := by
  have htL : t ∈ L := hBL htB
  have hφe : ∀ l : ↥L, ff6mPhi e l = omegaToProj hQ (φ l) := fun l => by
    rw [ff6mPhi_apply, he l]
  refine ⟨fun b hb => ?_, fun g hg => ?_⟩
  · have hmem : omegaToProj hQ (φ b) ∈ ffB1 hQ fr := by
      rw [← hU, ← hφe b]
      exact mem_ffImg_iff.mpr ⟨b, hb, rfl⟩
    rw [← ffLift_ffB1 hQ fr]
    exact (mem_ffLift_iff hQ).mpr ⟨(φ b).2, hmem⟩
  · rw [← ffLift_ffB1 hQ fr] at hg
    obtain ⟨hgΩ, hgU⟩ := (mem_ffLift_iff hQ).mp hg
    rw [← hU] at hgU
    obtain ⟨l, hlB, hl⟩ := mem_ffImg_iff.mp hgU
    rw [hφe l] at hl
    rcases omegaToProj_eq_iff hQ hl with h1 | h1
    · exact ⟨l, hlB, h1.symm⟩
    · refine ⟨l * ⟨t, htL⟩, B.mul_mem hlB htB, ?_⟩
      have hπ := hφ.map_central hL htc ht2 htL
      rw [map_mul, Subgroup.coe_mul, hπ, mul_piOrth_comm]
      exact h1.symm

end CFSG.OddStandard.SmallF3.Omega
