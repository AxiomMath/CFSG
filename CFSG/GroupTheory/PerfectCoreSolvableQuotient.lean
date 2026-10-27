module

public import CFSG.Quasithin.Background.A3ComponentsBasic
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.GroupTheory

theorem perfectCore_le_of_isSolvable_quotient {G : Type} [Group G] [Finite G]
    {X N : Subgroup G} (hNX : N ≤ X) [(N.subgroupOf X).Normal]
    (hs : Group.IsSolvable (↥X ⧸ N.subgroupOf X)) :
    CFSG.Quasithin.perfectCore X ≤ N := by
  obtain ⟨-, -, -, -, hiff, -⟩ := CFSG.perfect_residual_characterization (G := ↥X)
  have h := (hiff (N.subgroupOf X)).mp hs
  rw [CFSG.Quasithin.perfectCore_eq_map_perfectResidual X]
  calc (CFSG.perfectResidual ↥X).map X.subtype
      ≤ (N.subgroupOf X).map X.subtype := Subgroup.map_mono h
    _ = N := Subgroup.map_subgroupOf_eq_of_le hNX

theorem perfectCore_eq_of_le_sup_of_isSolvable_quotient {H : Type} [Group H] [Finite H]
    {X P M : Subgroup H} (hMnorm : M ≤ Subgroup.normalizer (X : Set H))
    [(P.subgroupOf (X ⊔ M)).Normal] (hPX : P ≤ X ⊔ M) (hMs : Group.IsSolvable M)
    (hquot : Group.IsSolvable (↥(X ⊔ M) ⧸ P.subgroupOf (X ⊔ M))) :
    CFSG.Quasithin.perfectCore X = CFSG.Quasithin.perfectCore P := by
  let Y := X ⊔ M
  have hXn : (X.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hMnorm)
  have hle1 : CFSG.Quasithin.perfectCore P ≤ X :=
    (CFSG.Quasithin.perfectCore_mono hPX).trans
      (CFSG.Quasithin.perfectCore_le_of_sup_solvable le_sup_left hXn rfl hMs)
  have hle1' : CFSG.Quasithin.perfectCore P ≤ CFSG.Quasithin.perfectCore X :=
    CFSG.Quasithin.le_perfectCore_of_perfect hle1 (CFSG.Quasithin.perfectCore_perfect P)
  have hle2 : CFSG.Quasithin.perfectCore X ≤ CFSG.Quasithin.perfectCore P := by
    have hpc : CFSG.Quasithin.perfectCore Y ≤ P :=
      perfectCore_le_of_isSolvable_quotient hPX hquot
    exact CFSG.Quasithin.le_perfectCore_of_perfect
      ((CFSG.Quasithin.perfectCore_mono le_sup_left).trans hpc)
      (CFSG.Quasithin.perfectCore_perfect X)
  exact le_antisymm hle2 hle1'

end CFSG.GroupTheory
