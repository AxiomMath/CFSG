module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSimple
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk)

section Final

variable {G : Type} [Group G] [Finite G]


theorem u64TypesAt_of_fact (h : U64Fact) : U64TypesAt G := by
  intro X K J y lab hX h5 h3 hmark hZ hy hy3 hJ hJl
  have htag := u64_five_center_of_marking hmark hZ
  have hbar := mix_transfer (by norm_num : Nat.Prime 5) (by norm_num : Nat.Prime 3) hy hy3 h5 h3 hJ
  have hlab := hasLabel_image_bar (by norm_num : Nat.Prime 5) (by norm_num : Nat.Prime 3) hy h5 h3
    hJ (S := fun l : GLALabel => l = ⟨.twA, 4, 2⟩) hJl
  have hβ3 : (barAut 5 K ⟨y, hy⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, hy⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [this, map_one]
  exact h (PQuot 5 K) lab hmark htag hZ _ hβ3 _ hbar hlab

theorem u64TypesAt_of_facts (h : U64FactS) : U64TypesAt G :=
  u64TypesAt_of_fact (u64Fact_of_simple h)

end Final

end CFSG.LocalAnalysis.GLTheoremA.Y10F
