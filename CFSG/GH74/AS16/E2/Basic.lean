module

public import CFSG.GH74.AS16.Chain
public import CFSG.GH74.NoComponent
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.E2.Shapes
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.OddLinearTwoAliases

public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG CFSG.Blueprint
open CFSG.GH74.E2 hiding Hyp

theorem hyp_of_e2 {G : Type} [Group G] [Finite G] (hH : CFSG.GH74.E2.Hyp G)
    (he : Assembly.evenRank G ≤ 2) (hnot : ¬ Assembly.Quasithin.quasithinEvenCharacteristic G) :
    CFSG.GH74.AS16.Hyp G :=
  ⟨hH.simple, hH.nonabelian, CFSG.GH74.kProper_of_kgh hH.kgh, hH.restrictedEven.isEvenType, he,
    hnot⟩

@[expose] def Terminal {G : Type} [Group G] (L : Subgroup G) : Prop :=
  ∀ t : G, orderOf t = 2 → t ∈ centralizer (L : Set G) → IsCompCen t L

structure Cfg (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (z : G) (L : Subgroup G) :
    Prop where
  hyp : CFSG.GH74.E2.Hyp G
  quasithin : Assembly.evenRank G ≤ 2
  pair : Pair T z L
  shape : ∀ y : G, orderOf y = 2 → ∀ K : Subgroup G, IsCompCen y K → K0Shape ↥K
  uniq : ∀ y : G, orderOf y = 2 → ∀ K K' : Subgroup G, IsCompCen y K → IsCompCen y K' → K = K'

theorem lieModel_of_shapeA5
    {K : Type} [Group K] (h : ShapeA5 K) : LieModel K .PSL 2 5 1 := by
  rcases h with h | h | h
  · exact Or.inl ⟨by decide,
      CFSG.LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_five_of_alternating_five K h⟩
  · exact Or.inl ⟨by decide,
      CFSG.LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_five_of_alternating_five K
        (CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model K h)⟩
  · exact h

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {z : G} {L : Subgroup G}

theorem Cfg.isCentralInvolution (h : Cfg G T z L) : IsCentralInvolution z :=
  ⟨h.pair.orderOf_eq, T, h.pair.mem_sylow, h.pair.central⟩

theorem Cfg.isTerminalPair (h : Cfg G T z L) (ht : Terminal L) : GLS.IsTerminalPair 2 z L := by
  refine ⟨h.pair.orderOf_eq, h.pair.isComp, ?_, fun y hy hyL => ht y hy hyL⟩
  obtain ⟨i, hiL, hi⟩ := exists_involution_of_isQuasisimple h.pair.isQuasisimple
  have h2 : orderOf (⟨i, hiL⟩ : ↥L) = 2 := by rw [← Subgroup.orderOf_coe]; exact hi
  rw [← h2]
  exact orderOf_dvd_natCard _

end CFSG.GH74.AS16.E2
