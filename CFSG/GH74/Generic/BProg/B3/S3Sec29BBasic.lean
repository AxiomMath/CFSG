module

public import CFSG.GH74.Generic.BProg.B3.S3Ctx29Defs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools
open scoped commutatorElement

namespace S3Sec29B

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem comm_of_isElementaryAbelian {B : Subgroup G} (hB : CFSG.IsElementaryAbelian 2 ↥B) :
    ∀ a ∈ B, ∀ c ∈ B, a * c = c * a := fun a ha c hc =>
  congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥B) ⟨c, hc⟩)

end S3Sec29B

theorem Ctx29.obs_data {G : Type} [Group G] [Finite G] {x y b : G} {K A B Q D J : Subgroup G}
    (h : Ctx29 G x K A B Q y b D J) :
    orderOf b = 2 ∧ IsPCompIn 2 (centralizer ({b} : Set G)) J ∧ b ∈ centralizer (B : Set G) := by
  rcases h.obs with hobs | ⟨hby, hobs32, -, -, -⟩
  · exact ⟨hobs.b_ord, hobs.comp, hobs.b_cent⟩
  · subst hby
    obtain ⟨hAB, -, -, hBel, -, -, -⟩ := h.ext
    have hbB : b ∈ B := h.b_mem
    refine ⟨h.y_ord, hobs32.comp, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact S3Sec29B.comm_of_isElementaryAbelian hBel z hz b hbB

end CFSG.GH74.Generic.BProg.B3
