module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPfCore
public import CFSG.ClassicalInvolution.SmallCases.A7T22Const

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp

section Datum

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem exists_hyp22G (h : PerpHypS n Y R S t) (h3 : ¬ TwoTwins R) :
    ∃ (K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y),
      A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' K₃ t u₁ u₂ u₃ := by
  have hC := CoreData.of_S h.core
  have hU : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  obtain ⟨K', hK', hne⟩ := hC.twin
  have hne2 : KPerp (CoreAssembly.conjClass (tightCore R)) (tightCore R) ≠
      {tightCore R, K'} := fun hP => h3 (twoTwins_of_eq_pair (h.perp ▸ hP))
  obtain ⟨K₃, u₁, u₂, u₃, -, hd⟩ := A7T22.exists_hyp22Core_of_perp hC.hyp
    (CoreAssembly.mem_conjClass_self _) hU hK' hne h.perp hne2
  exact ⟨K', K₃, u₁, u₂, u₃, A7T22.Hyp22G.of_core hd fun L hL =>
    isSubnormal_of_hypOmegaGen hC.hyp hL.1 (isUniqueInvolution_of_mem_twinSet hU hL)⟩

end Datum

@[expose] def V3Hyp51B (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypS n Y R S t → ¬ TwoTwins R → ¬ TwinE4 Y →
      ∀ (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y),
        A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ →
          Hyp51 (Subgroup.closure ({u₁ * u₂, t, u₂ * u₃} : Set Y))

section Alpha

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem alphaConst (hV : V3Hyp51B n) (h : PerpHypS n Y R S t) (h3 : ¬ TwoTwins R)
    (hE : ¬ TwinE4 Y) :
    A7T22.AlphaConst (CoreAssembly.conjClass (tightCore R)) t :=
  A7T22.alphaConst_of_hyp51 fun K K' K₃ u₁ u₂ u₃ hd => hV Y R S t h h3 hE K K' K₃ u₁ u₂ u₃ hd

theorem centralizer_le_normalizer_alpha (hα : A7T22.AlphaConst (CoreAssembly.conjClass (tightCore R)) t)
    {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y}
    (hd : A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃) :
    Subgroup.centralizer ({t} : Set Y) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) : Set Y) :=
  hd.centralizer_le_normalizer_alpha hα

end Alpha

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
