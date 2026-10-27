module

public import CFSG.ClassicalInvolution.Asc77.AscCHN8
public import CFSG.ClassicalInvolution.Asc77.AscCHN3
public import CFSG.ClassicalInvolution.Asc77.AscCHN1
public import CFSG.ClassicalInvolution.Asc77.AscSCH28
public import CFSG.ClassicalInvolution.Asc77.AscCHN7

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace CHN

set_option linter.unusedSectionVars false

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.ExactLayer

variable {p f : ℕ} [Fact p.Prime]


theorem c23_chainMinus4_of_hodd (hodd : T7Z.OddCenterClassical) : C23_chainMinus4 p f := by
  intro hq3 G _ _ _ Ω K K' W z u e g hs hd hα hE hY
  classical
  have hst := hs.stand
  have hp2 : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hpi : piSign p f = false := by simp [piSign, hq3]
  have hE0 : LayerOrthType p f Ω e 6 false := by simpa [hpi] using hE
  have hY0 : LayerOrthType p f Ω u 6 true := by simpa [hpi] using hY
  obtain ⟨hOE, hOY⟩ := T7Z.oddCore_layers_eq_bot hodd hs hd hα.1 hE (Or.inr hY)
  have hex : ExactMembers Ω := T7Z.exactMembers_of_layer hs hd hα.1 hd.he2 hOE hE
  obtain ⟨K₁, z₁, hK₁Ω, hz₁, hK₁le, hpair, hYle, heN, hC, hz₁e, ⟨θ, hθ, hθτ⟩, hclaim⟩ :=
    ySide3 hq3 hs hd hex hOY hY0
  obtain ⟨K₃, hTw, hK₃z, hK₃perf, hK₃le, hEle, hJE, hJ'E⟩ :=
    eSide3 hq3 hs hd hα.1 hex hOE hE0 hz₁.sq hz₁e θ hθ hθτ hclaim
  obtain ⟨h, hh⟩ := hst.trans K₁ hK₁Ω
  subst hh
  have hz₁eq : h * z * h⁻¹ = z₁ := (hs.hz.conj h).eq hz₁
  have hs₁ : Hyp23Setting p f Ω (conjSub h K) (conjSub h K') z₁ := hz₁eq ▸ hs.conj h
  have hcomm : Commutes (conjSub h K) K₃ :=
    commutes_of_perfect_centralizer_e hs₁ hex hK₃z hK₃perf heN
      (fun ℓ hℓ => Subgroup.mem_centralizer_singleton_iff.mp
        (exactLayer_le_centralizer Ω e (hK₃le hℓ))) hC
  refine ⟨![conjSub h K, conjSub g K, K₃], hK₁Ω, hcomm, hpair, hTw, ?_⟩
  have hsup : (⨆ k, (![conjSub h K, conjSub g K, K₃] : Fin 3 → Subgroup G) k) =
      conjSub h K ⊔ conjSub g K ⊔ K₃ := by
    refine le_antisymm (iSup_le fun k => ?_) (sup_le (sup_le ?_ ?_) ?_)
    · fin_cases k
      · exact le_sup_left.trans le_sup_left
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right
    · exact le_iSup (fun k => (![conjSub h K, conjSub g K, K₃] : Fin 3 → Subgroup G) k) 0
    · exact le_iSup (fun k => (![conjSub h K, conjSub g K, K₃] : Fin 3 → Subgroup G) k) 1
    · exact le_iSup (fun k => (![conjSub h K, conjSub g K, K₃] : Fin 3 → Subgroup G) k) 2
  have hJH : conjSub g K ≤ conjSub h K ⊔ conjSub g K ⊔ K₃ :=
    le_sup_right.trans le_sup_left
  have hK₁H : conjSub h K ≤ conjSub h K ⊔ conjSub g K ⊔ K₃ := le_sup_left.trans le_sup_left
  have hK₃H : K₃ ≤ conjSub h K ⊔ conjSub g K ⊔ K₃ := le_sup_right
  have hEH : exactLayer Ω e ≤ conjSub h K ⊔ conjSub g K ⊔ K₃ :=
    hEle.trans (sup_le hJH hK₃H)
  have hYH : exactLayer Ω u ≤ conjSub h K ⊔ conjSub g K ⊔ K₃ :=
    hYle.trans (sup_le (sup_le (hJ'E.trans hEH) hK₁H) hJH)
  rw [hsup]
  refine eq_top_iff.mpr ?_
  rw [← hα.2, rLayer_eq_exactLayer hp2 hq hst.hyp hd.he2,
    rLayer_eq_exactLayer hp2 hq hst.hyp hd.hu2]
  exact sup_le hEH hYH

theorem c23_chainMinus4_proved : C23_chainMinus4 p f :=
  c23_chainMinus4_of_hodd SCH.oddCenterClassical

theorem c23_recogMinus4_proved : R31.C23_recogMinus4 p f :=
  c23_recogMinus4_of_chain c23_chainMinus4_proved

end CHN

end CFSG.ClassicalInvolution.Asc77
