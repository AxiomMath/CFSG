module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf10U1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMu

namespace Pf3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Asc77.Star3T CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Asc77.MuTab (muTabElt muTabElt_mem)

section Swap

theorem exists_swap_noncomm {s₁ s₂ : Equiv.Perm (Fin 4)} (h₁ : s₁.IsSwap) (h₂ : s₂.IsSwap) :
    ∃ s₃ : Equiv.Perm (Fin 4), s₃.IsSwap ∧ s₃ * s₁ ≠ s₁ * s₃ ∧ s₃ * s₂ ≠ s₂ * s₃ := by
  obtain ⟨a, b, hab, rfl⟩ := h₁
  obtain ⟨c, d, hcd, rfl⟩ := h₂
  have key : ∀ a b c d : Fin 4, a ≠ b → c ≠ d → ∃ x y : Fin 4, x ≠ y ∧
      Equiv.swap x y * Equiv.swap a b ≠ Equiv.swap a b * Equiv.swap x y ∧
      Equiv.swap x y * Equiv.swap c d ≠ Equiv.swap c d * Equiv.swap x y := by decide
  obtain ⟨x, y, hxy, h1, h2⟩ := key a b c d hab hcd
  exact ⟨Equiv.swap x y, ⟨x, y, hxy, rfl⟩, h1, h2⟩

end Swap

section Conj


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem exists_conj_secImg {J : Subgroup G} {y : G} (hy : y ∈ coreLayer Ω c) :
    ∃ g : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c),
      conjSub g (secImg Ω c J) = secImg Ω c (conjSub y J) := by
  obtain ⟨ŷ, hŷ, rfl⟩ := Subgroup.mem_map.mp hy
  refine ⟨QuotientGroup.mk (⟨ŷ, hŷ⟩ : ↥(coreHull Ω c)), ?_⟩
  unfold secImg
  have h1 := AscQuot.map_conjSub (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)))
    (⟨ŷ, hŷ⟩ : ↥(coreHull Ω c))
    (((TwinADescent.coreAt c J).subgroupOf (Subgroup.centralizer ({c} : Set G))).subgroupOf
      (coreHull Ω c))
  rw [show QuotientGroup.mk (⟨ŷ, hŷ⟩ : ↥(coreHull Ω c)) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)) ⟨ŷ, hŷ⟩ from rfl, ← h1]
  congr 1
  rw [Generic.conjSub_subgroupOf, Generic.conjSub_subgroupOf (Subgroup.centralizer ({c} : Set G)) ŷ]
  rw [show (((⟨ŷ, hŷ⟩ : ↥(coreHull Ω c)) : ↥(Subgroup.centralizer ({c} : Set G))) : G) = (ŷ : G) from rfl,
    TwinADescent.conjSub_coreAt ŷ.2]
  rfl

end Conj

end Pf3

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMu
