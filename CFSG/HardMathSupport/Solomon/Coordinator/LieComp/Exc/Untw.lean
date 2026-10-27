module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Field
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.InnerUntw

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.RecipeExcLang

set_option linter.unusedSectionVars false

theorem perfectInLayer_congr_of {S G : Type*} [Group S] [Group G] (e : S ≃* G) {β : MulAut S}
    (h : PerfectInLayer β) : PerfectInLayer (MulAut.congr e β) := by
  refine perfectInLayer_of_congr e.symm (MulAut.congr e β) ?_
  have : MulAut.congr e.symm (MulAut.congr e β) = β := by
    ext x
    simp [MulAut.congr_apply]
  rw [this]
  exact h


theorem lieCompExport_untw (hres : ExcRationalLieTypes) {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c)
    (hchar : ∀ q : TauCeti.PrimePower, (c q).characteristic = q.p)
    (hvalid : ∀ q : TauCeti.PrimePower, (τ = .G2 → 3 ≤ q.card) → (c q).Valid)
    (hG2 : ∀ (q : TauCeti.PrimePower), (c q).Valid → τ = .G2 → 3 ≤ q.card)
    (hA6 : ∀ (q : TauCeti.PrimePower) (hv : (c q).Valid),
      IsEmpty ((TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group ≃* alternatingGroup (Fin 6)))
    (q : TauCeti.PrimePower) (hv : (c q).Valid) (hq3 : 3 ≠ q.p) {S : Type} [Group S]
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group) (β : MulAut S) (hβ : β ^ 3 = 1)
    (hβ1 : β ≠ 1) (hlayer : PerfectInLayer β) : LieCompExport q.p β := by
  classical
  obtain ⟨K, _, hKfin, hK, hKchar, ⟨eK⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup hB q hv
  let e' : S ≃* ↥(adjointGroup τ K) := e.trans eK
  have hℓ : ringChar K = q.p := ringChar.eq K q.p
  have hβ' : MulAut.congr e' β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  have hβ1' : MulAut.congr e' β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr e').injective (h.trans (map_one _).symm))
  refine LieCompExport.of_congr e' ?_
  have hlayer' := perfectInLayer_congr_of e' hlayer
  have hG2K : τ = .G2 → 3 ≤ Nat.card K := fun h => hK ▸ hG2 q hv h
  have hpK : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    exact CFSG.LieType.SeitzGeneration.not_dvd_card_of_ne Nat.prime_three hq3
  have hdisp : (∃ (σ : K ≃+* K) (ψ : MulAut ↥(adjointGroup τ K)),
      σ ≠ 1 ∧ ψ * MulAut.congr e' β * ψ⁻¹ = entrywiseAdjointAut τ σ) ∨
    (∃ h ∈ inndiagGroup τ K, (∀ c : adjointGroup τ K,
        ((MulAut.congr e' β) c : ModGL τ K) = h * c * h⁻¹) ∧ h ^ 3 = 1 ∧ h ≠ 1) := by
    rcases hτ with h | h | h | h | h
    · exact exists_field_or_inndiag_FG (Or.inr h) hG2K Nat.prime_three (by norm_num) _ hβ' hβ1'
    · exact exists_field_or_inndiag_FG (Or.inl h) hG2K Nat.prime_three (by norm_num) _ hβ' hβ1'
    · exact exists_field_or_inndiag_E (Or.inl h) Nat.prime_three (by norm_num) _ hβ' hβ1'
    · exact exists_field_or_inndiag_E (Or.inr (Or.inl h)) Nat.prime_three (by norm_num) _ hβ' hβ1'
    · exact exists_field_or_inndiag_E (Or.inr (Or.inr h)) Nat.prime_three (by norm_num) _ hβ' hβ1'
  rcases hdisp with ⟨σ, ψ, -, hψ⟩ | ⟨h, hh, hβh, hp1, hh1⟩
  · refine lieCompExport_of_conj ψ _ ?_
    rw [hψ]
    exact lieCompExport_entrywiseAdjointAut_untw hB hchar hvalid hA6 hℓ σ
  · exact lieCompExport_inner_untw hres hτ hG2K hpK _ h
      (baseChange_mem_adjointGroup_of_mem_inndiag hh) hβh hp1 hh1 hlayer' hℓ

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
