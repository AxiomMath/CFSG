module

public import CFSG.LieType.Steinberg.CentralExt.SpThree
public import CFSG.ClassicalInvolution.Q3.Q3WALoc

public section

namespace CFSG.ClassicalInvolution.Q3.Q3OF

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Q3.Q3W CFSG.Assembly.Dichotomy
open scoped MatrixGroups

@[expose] def KindClosed3 (c : CompData) : Prop :=
  ∀ (E : Type) [Group E] [Finite E] (π : E →* c.G), Function.Surjective π →
    π.ker ≤ Subgroup.center E → ∃ σ : c.G →* E, ∀ x, π (σ x) = x

section Kinds

theorem kindClosed3_psl {m : ℕ} (hm : 2 ≤ m) : KindClosed3 (CompData.model .PSL (m + 1)) := by
  intro E _ _ π hπ hcen
  by_cases hm2 : m = 2
  · subst hm2
    exact CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_separating
      (F := GaloisField 3 1) le_rfl
      (CFSG.LieType.Steinberg.CentralExt.SLClosed.separating_of_card le_rfl
        (by rw [card_gf3]; norm_num) (by rw [card_gf3]; omega) (by rw [card_gf3]; omega)) hπ hcen
  · exact CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_card_three
      (F := GaloisField 3 1) (by omega) card_gf3 hπ hcen

theorem kindClosed3_psp {n : ℕ} (hn : 3 ≤ n) : KindClosed3 (CompData.model .PSp n) := by
  intro E _ _ π hπ hcen
  exact CFSG.LieType.Steinberg.CentralExt.SpThree.sp_three_exists_section_of_central
    (F := GaloisField 3 1) card_gf3 hn hπ hcen

end Kinds

end CFSG.ClassicalInvolution.Q3.Q3OF
