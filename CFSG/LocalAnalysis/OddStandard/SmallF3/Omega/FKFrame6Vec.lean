module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4IIIAux4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fk_fr_exists_vec (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1)
    (ht1 : invDim t = 1) : ∃ (v : V) (hv : Q v ≠ 0), t = reflOf Q v hv := by
  have hfin : Module.finrank (ZMod 3) (commSp t) = 1 := by
    simpa only [invDim] using ht1
  obtain ⟨w, hw0, hwspan⟩ :=
    (finrank_eq_one_iff' (K := ZMod 3) (V := commSp t)).mp hfin
  have hwV0 : (w : V) ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hwQ : Q (w : V) ≠ 0 := by
    intro hQw
    have hnd : (Q.restrict (commSp t)).Nondegenerate := nondegenerate_restrict_commSp hQ htt
    rw [QuadraticMap.nondegenerate_iff_radical_eq_bot] at hnd
    have hmem : w ∈ (Q.restrict (commSp t)).radical := by
      rw [QuadraticMap.mem_radical_iff']
      refine ⟨hQw, fun y => ?_⟩
      obtain ⟨c, hc⟩ := hwspan y
      have hcV : c • (w : V) = (y : V) := congrArg Subtype.val hc
      have hvc : (w : V) + c • (w : V) = (1 + c) • (w : V) := by
        rw [add_smul, one_smul]
      change Q ((w : V) + (y : V)) = Q (y : V)
      calc Q ((w : V) + (y : V)) = Q ((w : V) + c • (w : V)) := by rw [hcV]
        _ = Q ((1 + c) • (w : V)) := by rw [← hvc]
        _ = ((1 + c) * (1 + c)) • Q (w : V) := QuadraticMap.map_smul Q (1 + c) (w : V)
        _ = 0 := by rw [hQw, smul_zero]
        _ = Q (y : V) := by rw [← hcV, QuadraticMap.map_smul Q, hQw, smul_zero]
    have hwbot : w = 0 := by
      rw [hnd] at hmem
      simpa using hmem
    exact hw0 hwbot
  refine ⟨(w : V), hwQ, ?_⟩
  have hspan : commSp t = Submodule.span (ZMod 3) {(w : V)} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hfin w.2 hwV0
  have heq : commSp (reflOf Q (w : V) hwQ) = commSp t :=
    (ff_commSp_reflOf hQ hwQ).trans hspan.symm
  exact (eq_of_commSp_eq hQ (reflOf_mul_self (w : V) hwQ) htt heq).symm

end CFSG.OddStandard.SmallF3.Omega
