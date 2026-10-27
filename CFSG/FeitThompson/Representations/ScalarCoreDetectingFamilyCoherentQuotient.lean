module

public import CFSG.FeitThompson.Representations.ScalarCoordinateDegreeDivisibility

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace ScalarCoordinateSystem

variable {p q : ℕ} [Fact p.Prime] {V U : Type*} [AddCommGroup V] [Module (ZMod p) V] [Group U]
  (S : ScalarCoordinateSystem p q V U)

theorem le_ker_act_of_le_totalCentralizer {N : Subgroup U} (hN : N ≤ S.totalCentralizer) :
    N ≤ S.act.ker := fun u hu =>
  MonoidHom.mem_ker.2 (LinearEquiv.ext fun v => (S.mem_totalCentralizer.1 (hN hu)) v)

noncomputable def quotient (N : Subgroup U) [N.Normal] (hN : N ≤ S.totalCentralizer) :
    ScalarCoordinateSystem p q V (U ⧸ N) where
  two_le_q := S.two_le_q
  line := S.line
  finrank_line := S.finrank_line
  indep_line := S.indep_line
  iSup_line := S.iSup_line
  act := QuotientGroup.lift N S.act (S.le_ker_act_of_le_totalCentralizer hN)
  map_line u i v hv := by
    induction u using QuotientGroup.induction_on with
    | _ u => exact S.map_line u i v hv
  coprime_card :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_quotient_dvd_card N) S.coprime_card

variable (N : Subgroup U) [N.Normal] (hN : N ≤ S.totalCentralizer)

@[simp] theorem quotient_line : (S.quotient N hN).line = S.line := (rfl)

@[simp] theorem quotient_act_mk (u : U) :
    (S.quotient N hN).act (QuotientGroup.mk u) = S.act u := (rfl)

theorem mk_mem_lineCentralizer_quotient_iff (i : Fin q) (u : U) :
    (QuotientGroup.mk u : U ⧸ N) ∈ (S.quotient N hN).lineCentralizer i ↔
      u ∈ S.lineCentralizer i := by
  rw [mem_lineCentralizer, mem_lineCentralizer, quotient_line, quotient_act_mk]

theorem lineCentralizer_quotient (i : Fin q) :
    (S.quotient N hN).lineCentralizer i = (S.lineCentralizer i).map (QuotientGroup.mk' N) := by
  ext z
  induction z using QuotientGroup.induction_on with
  | _ u =>
    rw [S.mk_mem_lineCentralizer_quotient_iff N hN]
    refine ⟨fun h => ⟨u, h, rfl⟩, ?_⟩
    rintro ⟨w, hw, hwu⟩
    have hmem : w⁻¹ * u ∈ N := QuotientGroup.eq.1 hwu
    have hmem' : w⁻¹ * u ∈ S.lineCentralizer i :=
      S.totalCentralizer_le_lineCentralizer i (hN hmem)
    simpa using (S.lineCentralizer i).mul_mem hw hmem'

end ScalarCoordinateSystem

end CFSG.FeitThompson
