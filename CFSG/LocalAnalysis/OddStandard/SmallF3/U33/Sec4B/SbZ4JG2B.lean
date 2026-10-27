module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG2A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR5A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {X : Type} [Group X] [Finite X] {N : Subgroup X} [N.Normal]

theorem z4j_exists_lift_max (hN : Odd (Nat.card N)) {Q : Subgroup X} (hQ : IsPGroup 2 Q)
    {W : Subgroup (X ⧸ N)} (hW : IsPGroup 2 W) (hQW : Q.map (z4iπ N) ≤ W)
    (hmax : ∀ P'' : Subgroup (X ⧸ N), IsPGroup 2 P'' → W ≤ P'' → P'' = W) :
    ∃ P : Subgroup X, Z4JLift N P W ∧ Q ≤ P ∧
      ∀ P'' : Subgroup X, IsPGroup 2 P'' → P ≤ P'' → P'' ≤ P := by
  obtain ⟨P, hP, hQP, hPW, hmaxP⟩ := z4i_exists_lift_max N hN hQ hW hQW hmax
  exact ⟨P, ⟨hN, hP, hPW⟩, hQP, hmaxP⟩

namespace Z4JLift

variable {P : Subgroup X} {Vh : Subgroup (X ⧸ N)} (h : Z4JLift N P Vh)
include h

theorem eq_of_map_eq {U U' : Subgroup X} (hU : U ≤ P) (hU' : U' ≤ P)
    (hUU : U.map (z4iπ N) = U'.map (z4iπ N)) : U = U' :=
  z4i_eq_of_map_eq N h.odd h.isPGroup hU hU' hUU

theorem le_of_map_le {U U' : Subgroup X} (hU : U ≤ P) (hU' : U' ≤ P)
    (hUU : U.map (z4iπ N) ≤ U'.map (z4iπ N)) : U ≤ U' := by
  intro x hx
  obtain ⟨b, hb, hbx⟩ := hUU (Subgroup.mem_map_of_mem (z4iπ N) hx)
  have hb' : b = x := h.inj (hU' hb) (hU hx) hbx
  rwa [← hb']

theorem card_map {U : Subgroup X} (hU : U ≤ P) : Nat.card (U.map (z4iπ N)) = Nat.card U :=
  z4i_card_map N h.odd (h.isPGroup.to_le hU)

theorem map_commutator : (⁅P, P⁆).map (z4iπ N) = ⁅Vh, Vh⁆ := by
  rw [Subgroup.map_commutator, h.map_eq]

end Z4JLift

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
