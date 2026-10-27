module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1ModC
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1RegD
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2Norm

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_M6_comm_le_V1 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    ⁅M6 c.e, M6 c.e⁆ ≤ V1 c.e := by
  have h := c.y7acfg hH
  have hLFA := lfactsA_of_setting hH.hS hH.hZ c.s
  haveI := y7a_Z_normal_A c hH
  obtain ⟨_, _, _, hP⟩ := y7a_reg_data c hH hF
  obtain ⟨f, _, _, _, hker⟩ := y7a_mod_hom c hH hF hP
  have hcommA : _root_.commutator ↥c.s.fr.A ≤ c.s.fr.Z.subgroupOf c.s.fr.A := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def] using hLFA.comm_A (a : G) a.2 (b : G) b.2
  haveI : IsMulCommutative (↥c.s.fr.A ⧸ c.s.fr.Z.subgroupOf c.s.fr.A) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommA
  have hM6' : ⁅M6 c.e, M6 c.e⁆ ≤ AV1 c.e := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hxyM6 : ⁅x, y⁆ ∈ M6 c.e := by
      rw [commutatorElement_def]
      exact (M6 c.e).mul_mem
        ((M6 c.e).mul_mem ((M6 c.e).mul_mem hx hy) ((M6 c.e).inv_mem hx))
        ((M6 c.e).inv_mem hy)
    have hker_mem : (⟨⁅x, y⁆, hxyM6⟩ : ↥(M6 c.e)) ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      have he : (⟨⁅x, y⁆, hxyM6⟩ : ↥(M6 c.e)) =
          ⁅(⟨x, hx⟩ : ↥(M6 c.e)), (⟨y, hy⟩ : ↥(M6 c.e))⁆ := by
        apply Subtype.ext
        simp [commutatorElement_def]
      rw [he, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm' _ _
    rw [hker] at hker_mem
    exact Subgroup.mem_subgroupOf.mp hker_mem
  have hVle : V1 c.e ≤ Subgroup.centralizer (M6 c.e : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hm).2 v hv).symm
  have hbot1 : ⁅⁅M6 c.e, AV1 c.e⁆, M6 c.e⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr ((y7a_comm_M6_AV c hH hF).trans hVle)
  have hbot2 : ⁅⁅AV1 c.e, M6 c.e⁆, M6 c.e⁆ = ⊥ := by
    rw [commutator_comm (AV1 c.e) (M6 c.e)]
    exact hbot1
  have hthree : ⁅⁅M6 c.e, M6 c.e⁆, AV1 c.e⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate (H₁ := M6 c.e) (H₂ := M6 c.e) (H₃ := AV1 c.e)
      hbot1 hbot2
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hxyAV : ⁅x, y⁆ ∈ AV1 c.e := hM6' (Subgroup.commutator_mem_commutator hx hy)
  refine y7a_cen_AV h ⁅x, y⁆ hxyAV ?_
  intro w hw
  have hcen := commutator_eq_bot_iff_le_centralizer.mp hthree
    (Subgroup.commutator_mem_commutator hx hy)
  exact (Subgroup.mem_centralizer_iff.mp hcen w hw).symm

end CFSG.OddStandard.HigherRank.YamadaG23
