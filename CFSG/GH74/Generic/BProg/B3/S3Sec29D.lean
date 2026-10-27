module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29A1
public import CFSG.GH74.Generic.BProg.B3.S3Sec29Defs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools
open scoped commutatorElement

namespace S3Sec29D

variable {G : Type} [Group G] [Finite G]

theorem center_ne_bot_of_sl2 {X : Type} [Group X] (h : HasSL2Model X Odd) : center X ≠ ⊥ := by
  obtain ⟨F, _, _, hodd, ⟨e⟩⟩ := h
  have h2F : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hodd
  let e' : Matrix.SpecialLinearGroup (Fin 2) F ≃* X := (specialLinearGroupEquivStatedSL 2 F).trans e.symm
  have hne : (-1 : Matrix.SpecialLinearGroup (Fin 2) F) ≠ 1 := by
    intro h
    have h00 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h00
    exact h2F (by linear_combination (-1 : F) * h00)
  intro hbot
  have hmem : e' (-1) ∈ center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨z, rfl⟩ := e'.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    ext i j
    simp
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hne (e'.injective (by simpa using hmem))

end S3Sec29D

variable {G : Type} [Group G] [Finite G]

end CFSG.GH74.Generic.BProg.B3
