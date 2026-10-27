module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.WPrimeShapeSimple
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm

namespace WreathCase

theorem card_le_altCentCard8_of_isComponent_centralizer {X : Type} [Group X] [Finite X]
    {t : X} {Sg V K : Subgroup X} (hO : CFSG.pPrimeCore 2 X = ⊥) (H : WreathCase t Sg V K)
    (e : K ⧸ center K ≃* alternatingGroup (Fin 8)) {x : X} (hx : x * x = 1)
    (hxN : x ∈ normalizer (K : Set X)) {D : Subgroup X} (hDx : D ≤ centralizer ({x} : Set X))
    (hD : CFSG.IsComponent (D.subgroupOf (centralizer ({x} : Set X)))) (hDs : IsSimpleGroup D) :
    Nat.card D ≤ altCentCard8 (theta H e ⟨x, hxN⟩).1 ∨
      Nat.card D ≤ altCentCard8 (theta H e ⟨x, hxN⟩).2 := by
  have ht : x ^ 2 = 1 := by rw [pow_two]; exact hx
  have hDE : D ≤ CFSG.layer X :=
    CFSG.SeitzReduction.isComponent_centralizer_le_layer hO ht hDx hD
  have hqs : CFSG.IsQuasisimple ↥D :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hDx) hD.1
  obtain ⟨-, -, a, b, hab⟩ := hqs
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  have hn : ∃ a ∈ D, ∃ b ∈ D, a * b ≠ b * a := by
    refine ⟨a, a.2, b, b.2, fun h => hab ?_⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (Subtype.ext h)
  exact H.card_le_altCentCard8_of_isSimpleGroup e hxN hDE hDx hDs hn

end WreathCase

end CFSG.OddStandard.AltStdSec.SwapPartner
