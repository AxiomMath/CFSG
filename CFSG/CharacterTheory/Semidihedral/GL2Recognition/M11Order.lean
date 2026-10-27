module

public import CFSG.Sporadic.Bridge.M11
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Sporadic.Bridge.M11CheckInputs

public section

namespace CFSG.Semidihedral.GL2Recognition

theorem card_nativeM11 :
    Nat.card CFSG.Blueprint.NativeSporadic.M11 = 7920 := by
  obtain ⟨hfin, hcard⟩ := CFSG.Sporadic.Bridge.M11.finite_card_le
  refine le_antisymm ?_ CFSG.Sporadic.Bridge.M11.le_card_native
  exact (Nat.card_le_card_of_surjective _ CFSG.Sporadic.Bridge.M11.toNative_surjective).trans
    hcard

theorem statedM11_eq_nativeM11 :
    CFSG.Open.StatedM11 = CFSG.Blueprint.NativeSporadic.M11 := by
  unfold CFSG.Open.StatedM11 CFSG.Blueprint.NativeSporadic.M11
  congr 1

theorem lowTwoRankStatedM11_eq_nativeM11 :
    CFSG.Assembly.LowTwoRank.StatedM11 = CFSG.Blueprint.NativeSporadic.M11 :=
  statedM11_eq_nativeM11

theorem card_statedM11 : Nat.card CFSG.Open.StatedM11 = 7920 := by
  rw [statedM11_eq_nativeM11]
  exact card_nativeM11

theorem card_lowTwoRankStatedM11 :
    Nat.card CFSG.Assembly.LowTwoRank.StatedM11 = 7920 :=
  card_statedM11

end CFSG.Semidihedral.GL2Recognition
