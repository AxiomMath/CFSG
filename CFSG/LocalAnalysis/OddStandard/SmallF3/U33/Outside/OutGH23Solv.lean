module

public import Mathlib.GroupTheory.Solvable
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23Vocab
public import Certificates.Data.GH23Perm

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open CFSG.OddStandard.SmallF3.HarrisU33.GH23Data

theorem gh23_isSolvable_of_chain {G : Type*} [Group G] (D : ℕ → Subgroup G) (n : ℕ)
    (hstep : ∀ k < n, ⁅D k, D k⁆ ≤ D (k + 1)) (hn : D n = ⊥) : IsSolvable ↥(D 0) := by
  refine ⟨⟨n, ?_⟩⟩
  have key : ∀ k ≤ n, (derivedSeries ↥(D 0) k).map (D 0).subtype ≤ D k := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [derivedSeries_zero, Subgroup.map_top, Subgroup.range_subtype]
    | succ k ih =>
      intro hk
      have hkn : k < n := Nat.lt_of_succ_le hk
      have ihk := ih (le_of_lt hkn)
      calc
        (derivedSeries ↥(D 0) (k + 1)).map (D 0).subtype
            = ⁅(derivedSeries ↥(D 0) k).map (D 0).subtype,
                (derivedSeries ↥(D 0) k).map (D 0).subtype⁆ := by
              rw [derivedSeries_succ, Subgroup.map_commutator]
        _ ≤ ⁅D k, D k⁆ := Subgroup.commutator_mono ihk ihk
        _ ≤ D (k + 1) := hstep k hkn
  have hmap : (derivedSeries ↥(D 0) n).map (D 0).subtype = ⊥ :=
    le_bot_iff.mp ((key n le_rfl).trans hn.le)
  exact (Subgroup.map_eq_bot_iff_of_injective (derivedSeries ↥(D 0) n)
    (D 0).subtype_injective).mp hmap

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
