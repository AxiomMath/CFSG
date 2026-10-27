module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Bridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Card

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.CosetTable CFSG.Sporadic.Recognition.Fi24PrimeMultiplier CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

theorem Zp_le_stabilizer : Zp ≤ MulAction.stabilizer Q3 x0 := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, hi, rfl⟩
  exact MulAction.mem_stabilizer_iff.2 (smul_x0_of_fix (mem_subsetOf_iff.1 hi))

theorem index_stabilizer :
    (MulAction.stabilizer Q3 x0).index = 920808 := by
  rw [MulAction.index_stabilizer_of_transitive, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem Zp_eq_stabilizer :
    Zp = MulAction.stabilizer Q3 x0 := by
  have hle := Zp_le_stabilizer
  obtain ⟨hfin, hidx⟩ := index_Zp_le
  have h1 := Subgroup.relIndex_mul_index hle
  rw [index_stabilizer] at h1
  have hne : Zp.index ≠ 0 := hfin.index_ne_zero
  have hpos : 0 < Zp.relIndex (MulAction.stabilizer Q3 x0) :=
    Nat.pos_of_ne_zero fun h => hne (h1.symm.trans (by rw [h, zero_mul]))
  have h3 : Zp.relIndex (MulAction.stabilizer Q3 x0) * 920808 ≤ 1 * 920808 := by
    rw [one_mul, h1]; exact hidx
  have h2 : Zp.relIndex (MulAction.stabilizer Q3 x0) = 1 :=
    Nat.le_antisymm (Nat.le_of_mul_le_mul_right h3 (by norm_num)) hpos
  exact le_antisymm hle (Subgroup.relIndex_eq_one.1 h2)

theorem mem_Zp_iff_of_rep
    {T : Table} {g : Q3} (h : Rep 920808 T g) : g ∈ Zp ↔ ap T 0 = 0 := by
  rw [Zp_eq_stabilizer, MulAction.mem_stabilizer_iff]
  have e := smul_val_of_rep h x0
  rw [x0_val] at e
  constructor
  · intro hg
    rw [← e, hg, x0_val]
  · intro h0
    apply Fin.ext
    rw [e, h0, x0_val]

@[expose] noncomputable def omegaEquiv :
    Q3 ⧸ Zp ≃ Ω :=
  (Subgroup.quotientEquivOfEq Zp_eq_stabilizer).trans
    (Equiv.ofBijective (MulAction.ofQuotientStabilizer Q3 x0)
      ⟨MulAction.injective_ofQuotientStabilizer Q3 x0, fun p => by
        obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Q3 x0 p
        exact ⟨QuotientGroup.mk g, MulAction.ofQuotientStabilizer_mk Q3 x0 g⟩⟩)

theorem omegaEquiv_mk (g : Q3) :
    omegaEquiv (QuotientGroup.mk g : Q3 ⧸ Zp) = g • x0 :=
  rfl

theorem omegaEquiv_smul (g : Q3)
    (q : Q3 ⧸ Zp) : omegaEquiv (g • q) = g • omegaEquiv q := by
  induction q using QuotientGroup.induction_on with
  | H h =>
    have e : (g • (QuotientGroup.mk h : Q3 ⧸ Zp)) = QuotientGroup.mk (g * h) := rfl
    rw [e, omegaEquiv_mk, omegaEquiv_mk, mul_smul]

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
