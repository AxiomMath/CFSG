module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YAFacts
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFRel

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

theorem frame_a₁b₁b₂_not_mem_B {Γ : Type} [Group Γ] [Finite Γ] (fr : Frame Γ) (L : Subgroup Γ)
    (h11 : fr.Fact11 L) (h14 : fr.Fact14) : fr.a₁ * fr.b₁ * fr.b₂ ∉ fr.B := by
  intro hmem
  rw [SFrame.B, centIn, Subgroup.mem_inf] at hmem
  obtain ⟨-, hcen⟩ := hmem
  have hs := srel_of_fact11 fr h11
  have hw : fr.b₁ * fr.b₂ ∈ Subgroup.closure ({fr.b₁ * fr.b₂} : Set Γ) :=
    Subgroup.subset_closure (Set.mem_singleton _)
  have hcomm := (Subgroup.mem_centralizer_iff.mp hcen) _ hw
  have hb2a1 : fr.b₂ * fr.a₁ = fr.a₁ * fr.b₂ :=
    (commutatorElement_eq_one_iff_mul_comm.mp hs.a1b2).symm
  have hcomm_w : fr.a₁ * (fr.b₁ * fr.b₂) * (fr.b₁ * fr.b₂) =
      (fr.b₁ * fr.b₂) * fr.a₁ * (fr.b₁ * fr.b₂) := by
    convert hcomm.symm using 1 <;> group
  have h_aw : fr.a₁ * (fr.b₁ * fr.b₂) = (fr.b₁ * fr.b₂) * fr.a₁ :=
    mul_right_cancel hcomm_w
  have hEq3 : fr.a₁ * fr.b₁ = fr.b₁ * fr.a₁ := by
    apply mul_right_cancel (b := fr.b₂)
    calc fr.a₁ * fr.b₁ * fr.b₂ = fr.a₁ * (fr.b₁ * fr.b₂) := by group
      _ = (fr.b₁ * fr.b₂) * fr.a₁ := h_aw
      _ = fr.b₁ * fr.a₁ * fr.b₂ := by
        rw [mul_assoc fr.b₁ fr.b₂ fr.a₁, hb2a1]
        group
  have hz1 : fr.z = 1 := by
    rw [← hs.comm1, commutatorElement_eq_one_iff_mul_comm]
    exact hEq3
  have hzord : orderOf fr.z = 2 := (A_facts fr h14).2.2.2.2.2.1
  rw [hz1] at hzord
  simp at hzord

end CFSG.OddStandard.HigherRank.YamadaG23
