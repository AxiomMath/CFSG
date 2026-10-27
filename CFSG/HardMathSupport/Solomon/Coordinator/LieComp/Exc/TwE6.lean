module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.FieldTw
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.InnerTw
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Untw

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar

set_option linter.unusedSectionVars false


theorem lieCompExport_twE6 (hres : ExcRationalLieTypes)
    (hA6 : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid),
      IsEmpty ((TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group ≃* alternatingGroup (Fin 6)))
    (hmon : MonomialToralAt Tag.E6 3)
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) (hq3 : 3 ≠ q.p)
    {S : Type} [Group S] (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group)
    (β : MulAut S) (hβ : β ^ 3 = 1) (hβ1 : β ≠ 1) (hlayer : PerfectInLayer β) :
    LieCompExport q.p β := by
  classical
  obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  let e' : S ≃* ↥(twistedE6RootGroup K σ) := e.trans eK
  have hβ' : MulAut.congr e' β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  have hβ1' : MulAut.congr e' β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr e').injective (h.trans (map_one _).symm))
  refine LieCompExport.of_congr e' ?_
  have hlayer' := perfectInLayer_congr_of e' hlayer
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p q.exponent_pos K hK σ hσ
  by_cases hΘβ : Θ (MulAut.congr e' β) = 1
  · have hmem : MulAut.congr e' β ∈ (twistedE6InndiagConj K σ).range := by
      rw [range_twistedE6InndiagConj, ← hker, MonoidHom.mem_ker]
      exact hΘβ
    obtain ⟨h, hh⟩ := hmem
    have hp1 : h ^ 3 = 1 :=
      twistedE6InndiagConj_injective q.prime_p q.exponent_pos hK σ hσ
        (by rw [map_pow, hh, hβ', map_one])
    have hh1 : h ≠ 1 := fun h' => hβ1' (by rw [← hh, h', map_one])
    rw [← hh] at hlayer' ⊢
    exact lieCompExport_inner_twE6 hres q.prime_p q.exponent_pos hK σ hσ hq3 hmon h hp1 hh1 hlayer'
  · exact lieCompExport_twE6_field hA6 q.prime_p q.exponent_pos (by rw [hK, ← pow_mul, mul_comm]) σ hσ
      Nat.prime_three (by norm_num) Θ hΘ _ hβ' hΘβ

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
