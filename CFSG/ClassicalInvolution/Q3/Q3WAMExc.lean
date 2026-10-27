module

public import CFSG.ClassicalInvolution.Q3.Q3WAMBase
public import CFSG.ClassicalInvolution.Uniform.U8Cover
public import CFSG.ClassicalInvolution.Uniform.U8Twist

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Uniform (HasLayer3 hasLayer3_F4 hasLayer3_E6 hasLayer3_E7
  hasLayer3_E8)
open scoped MatrixGroups

section Layer

@[expose] def TwistedE6Layer3 : Prop :=
  ∀ n : ℕ, StatedLieAdmissible .twistedE6 n 3 1 → HasLayer3 .twistedE6 n

theorem hasLayer3_exc (hTw : TwistedE6Layer3) {t : StatedLieTag} {n : ℕ}
    (hexc : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6)
    (hadm : StatedLieAdmissible t n 3 1) : HasLayer3 t n := by
  rcases hexc with rfl | rfl | rfl | rfl | rfl
  · exact hasLayer3_F4 hadm
  · exact hasLayer3_E6 hadm
  · exact hasLayer3_E7 hadm
  · exact hasLayer3_E8 hadm
  · exact hTw n hadm

theorem twistedE6Layer3_proved : TwistedE6Layer3 := fun _ hadm =>
  Uniform.hasLayer3_twistedE6 hadm

end Layer

section Linked

theorem linkedIn_modelFund_exceptional3 {t : StatedLieTag} {n : ℕ}
    (hexc : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) (hlayer : HasLayer3 t n)
    (hadm : StatedLieAdmissible t n 3 1) {R R₁ R₂ : Subgroup (modelUniv t n 3 1 Fact.out).K}
    (hR : R ∈ ModelFund 3 t n 1) (hR₁ : R₁ ∈ ModelFund 3 t n 1) (hR₂ : R₂ ∈ ModelFund 3 t n 1)
    (c₁ : Commutes R₁ R) (c₂ : Commutes R₂ R) : LinkedIn (ModelFund 3 t n 1) R R₁ R₂ := by
  have hfund : IsFundTag t := by
    rcases hexc with rfl | rfl | rfl | rfl | rfl <;> trivial
  have hG2 : t ≠ .G2 := by
    rcases hexc with rfl | rfl | rfl | rfl | rfl <;> decide
  have hD4 : t ≠ .trialityD4 := by
    rcases hexc with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨L, hLq, hLC, hL3, -⟩ := hlayer R hR
  refine linkedIn_of_layer3 (F := ModelFund 3 t n 1)
    (fun S hS g => conjSub_mem_fundamentalSubgroups hS g)
    (fun S hS => not_commutes_self_modelFund3 hfund hadm hG2 hD4 hS) hLq hLC ?_ hR₁ hR₂ c₁ c₂
  intro S hS hSR
  obtain ⟨e⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := 3)
    (by norm_num) hfund hadm hG2 hD4 hS
  obtain ⟨T, hTS, hT3, hST⟩ := ModelFacts.gen3_of_equiv_sl2 e
  refine hST.trans ((Subgroup.closure_le _).2 fun s hs => hL3 s ?_ (hT3 s hs))
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (hSR s (hTS hs) y hy).symm

end Linked

end CFSG.ClassicalInvolution.Q3.Q3W
