module

public import CFSG.LieType.SeitzGeneration.QuasiHigh5E6CoverTw

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8NegC

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LieType.Seitz

set_option linter.unusedSectionVars false


theorem seitzHyperGamma_eq_top_twE6Cover (hD : QuasiHigh5E6Cover.TwE6ThreeOpenDiag)
    {P : Type*} [Group P] [Finite P] (hperf : commutator P = ⊤) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid)
    (e : P ⧸ Subgroup.center P ≃* Cat ⟨.twistedE6 q, hv⟩)
    (hq : q.card % 3 = 2) (hq2 : q.card ≠ 2) (hq8 : q.card ≠ 8) {E : Subgroup (MulAut P)}
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 2) :
    seitzHyperGamma 3 E = ⊤ := by
  have hD2 : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 (TauCeti.LieTypeIndex.twistedE6 q) := by
    simp [CFSG.AGLEmbeddingD2.IsD2SeitzException]
  have hp3 : (3 : ℕ) ≠ (TauCeti.LieTypeIndex.twistedE6 q).characteristic := by
    rw [TauCeti.LieTypeIndex.characteristic_twistedE6]
    intro h3
    rw [TauCeti.PrimePower.card_def, ← h3] at hq
    have : 3 ∣ 3 ^ q.exponent := dvd_pow_self 3 q.exponent_pos.ne'
    omega
  have hr : (TauCeti.LieTypeIndex.twistedE6 q).characteristic.Prime := by
    rw [TauCeti.LieTypeIndex.characteristic_twistedE6]
    exact q.prime_p
  have hgen := QuasiHigh5E6Cover.uniSeitzPlanes_twE6_three_two_of_open
    (QuasiHigh5E6Cover.twE6ThreeOpenPlanes_of QuasiHigh5E6Cover.twE6ThreeOpenInner_holds hD)
    ⟨.twistedE6 q, hv⟩ 3 Nat.prime_three (by norm_num) hp3 hD2 (coverImage e E)
    (isElemAbelian_coverImage e hE) ((card_coverImage hperf e E).trans hc)
    ⟨rfl, q, rfl, hq, hq2, fun h8 => absurd h8 hq8⟩
  exact seitzHyperGamma_eq_top_of_uniPlaneGen hperf e Nat.prime_three hr (Ne.symm hp3) hE hc hgen

end KSE8NegC

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
