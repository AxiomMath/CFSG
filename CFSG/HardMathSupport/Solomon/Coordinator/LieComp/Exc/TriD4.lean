module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.InnerTw
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Untw

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar

set_option linter.unusedSectionVars false


@[expose] def TrialityOuterExport : Prop :=
  ∀ (ℓ f : ℕ) [Fact ℓ.Prime], ℓ ≠ 3 → 1 ≤ f → ∀ (K₃ : Type) [Field K₃] [Finite K₃],
    Nat.card K₃ = (ℓ ^ f) ^ 3 → ∀ (Fr : K₃ ≃+* K₃), (∀ c, Fr c = c ^ (ℓ ^ f)) →
    ∀ φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom), φ ^ 3 = 1 →
      φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range →
      LieCompExport ℓ φ

theorem lieCompExport_triD4 (hres : ExcRationalLieTypes) (hout : TrialityOuterExport)
    (hmon : MonomialToralAt Tag.D4 3)
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hq3 : 3 ≠ q.p)
    {S : Type} [Group S] (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group)
    (β : MulAut S) (hβ : β ^ 3 = 1) (hβ1 : β ≠ 1) (hlayer : PerfectInLayer β) :
    LieCompExport q.p β := by
  classical
  obtain ⟨K, _, _, σ, hK, hσ, ⟨Θ, hΘker⟩, ⟨eK⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  let e' : S ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := e.trans eK
  have hβ' : MulAut.congr e' β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  have hβ1' : MulAut.congr e' β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr e').injective (h.trans (map_one _).symm))
  refine LieCompExport.of_congr e' ?_
  have hlayer' := perfectInLayer_congr_of e' hlayer
  by_cases hΘβ : Θ (MulAut.congr e' β) = 1
  · have hmem : MulAut.congr e' β ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
      rw [← hΘker, MonoidHom.mem_ker]
      exact hΘβ
    obtain ⟨x, hx⟩ := hmem
    have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
      center_graphFixedRootGroup_eq_bot σ.surjective
    have hxp : x ^ 3 = 1 :=
      mulAut_conj_injective_of_center_eq_bot hZ (by rw [map_pow, hx, hβ', map_one])
    have hx1 : x ≠ 1 := fun h' => hβ1' (by rw [← hx, h', map_one])
    rw [← hx] at hlayer' ⊢
    exact lieCompExport_inner_triD4 hres q.prime_p q.exponent_pos hK σ hσ hq3 hmon x hxp hx1 hlayer'
  · have hout' : MulAut.congr e' β ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := fun hmem =>
      hΘβ (by rw [← MonoidHom.mem_ker, hΘker]; exact hmem)
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    exact hout q.p q.exponent hq3.symm q.exponent_pos K hK σ hσ _ hβ' hout'

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
