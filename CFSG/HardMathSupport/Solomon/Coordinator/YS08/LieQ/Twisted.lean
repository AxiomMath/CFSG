module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Fixed
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Exc
public import CFSG.LieType.Chevalley.TwistedE6NormalForm

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.LieType.BorelTits

set_option linter.unusedSectionVars false

section Twisted


theorem two_le_foldedTag_rank (t : TwistTag) : 2 ≤ t.foldedTag.rank := by
  cases t <;> decide

theorem radRigid_of_twistedChevalleyModel {S : Type} [Group S] [Finite S] {t : TwistTag}
    (hBT : HoldsTits S 2) {f : ℕ} (hf : 1 ≤ f) (h : TwistedChevalleyModel S t (2 ^ f)) :
    RadRigid 2 S := by
  obtain ⟨K, _, hfin, hcard, σ, hσ, ⟨e⟩⟩ := h
  have hK : Nat.card K = (2 ^ f) ^ t.order := hcard
  obtain ⟨σ', hσ', hord, -⟩ := finite_graph_field_parameter_fields t Nat.prime_two hf K hK
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  have hperf := (finite_fixed_root_group_perfect t Nat.prime_two hf K hK σ hσ).2.2.1
  have hZ := exceptional_fixed_center_trivial t K σ'
  rw [hσσ'] at hZ
  obtain ⟨e'⟩ := nonempty_derivedCentralQuotient_equiv hperf hZ
  have e'' : S ≃* ↥(graphFixedRootGroup t K σ'.toRingHom) := by
    rw [hσσ']
    exact e.trans e'
  haveI : CharP K 2 := charP_two_of_card_two_pow' (f := f * t.order) (by rw [hK, ← pow_mul])
  have hσ'ord : σ' ^ t.order = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one σ'
  have hBT' : HoldsTits ↥(graphFixedRootGroup t K σ'.toRingHom) 2 := hBT.of_mulEquiv e''
  exact ((stdDatumFixed hσ'ord (two_le_foldedTag_rank t)).radRigid hBT').of_mulEquiv e''.symm

end Twisted

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
