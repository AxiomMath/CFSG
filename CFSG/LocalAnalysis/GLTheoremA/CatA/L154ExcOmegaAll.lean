module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcInnHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

theorem l154OmegaNID_mono {Q Q' : TauCeti.CFSGIndex → Prop} (hsub : ∀ i, Q i → Q' i)
    (h : L154OmegaNID Q') : L154OmegaNID Q := by
  intro p hp hp2 Ω _ _ S x y J hSn hqS hSp hSc hQ hxp hyp hxy hInn hF hJ hJy
  obtain ⟨i, hi, e⟩ := hQ
  exact h p hp hp2 Ω S x y J hSn hqS hSp hSc ⟨i, hsub i hi, e⟩ hxp hyp hxy hInn hF hJ hJy

theorem l154OmegaTD4_mono {Q Q' : TauCeti.CFSGIndex → Prop} (hsub : ∀ i, Q i → Q' i)
    (h : L154OmegaTD4 Q') : L154OmegaTD4 Q := by
  intro p hp hp2 Ω _ _ S x y J hSn hqS hSp hSc hQ hxp hyp hxy hInn hF hJ hJy
  obtain ⟨i, hi, e⟩ := hQ
  exact h p hp hp2 Ω S x y J hSn hqS hSp hSc ⟨i, hsub i hi, e⟩ hxp hyp hxy hInn hF hJ hJy

theorem l154OmegaNID_or {Q₁ Q₂ : TauCeti.CFSGIndex → Prop} (h₁ : L154OmegaNID Q₁)
    (h₂ : L154OmegaNID Q₂) : L154OmegaNID (fun i => Q₁ i ∨ Q₂ i) := by
  intro p hp hp2 Ω _ _ S x y J hSn hqS hSp hSc hQ hxp hyp hxy hInn hF hJ hJy
  obtain ⟨i, hi, e⟩ := hQ
  rcases hi with h | h
  · exact h₁ p hp hp2 Ω S x y J hSn hqS hSp hSc ⟨i, h, e⟩ hxp hyp hxy hInn hF hJ hJy
  · exact h₂ p hp hp2 Ω S x y J hSn hqS hSp hSc ⟨i, h, e⟩ hxp hyp hxy hInn hF hJ hJy

theorem l154OmegaTD4_or {Q₁ Q₂ : TauCeti.CFSGIndex → Prop} (h₁ : L154OmegaTD4 Q₁)
    (h₂ : L154OmegaTD4 Q₂) : L154OmegaTD4 (fun i => Q₁ i ∨ Q₂ i) := by
  intro p hp hp2 Ω _ _ S x y J hSn hqS hSp hSc hQ hxp hyp hxy hInn hF hJ hJy
  obtain ⟨i, hi, e⟩ := hQ
  rcases hi with h | h
  · exact h₁ p hp hp2 Ω S x y J hSn hqS hSp hSc ⟨i, h, e⟩ hxp hyp hxy hInn hF hJ hJy
  · exact h₂ p hp hp2 Ω S x y J hSn hqS hSp hSc ⟨i, h, e⟩ hxp hyp hxy hInn hF hJ hJy

section TitsSuz

theorem l154OmegaNID_tits : L154OmegaNID l154ExcTits := by
  intro p hp hp2 Ω _ _ S x y J hSn hqS hSp hSc hQ hxp hyp hxy hInn hF hJ hJy
  exact (l154_false_of_odd_inner hp hp2 (CFSG.HardMathSupport.Timmesfeld.Proving.glaPComponent_self
    hqS hSp) hSc hF.1 hyp hF (l154_oddInner_of_tits hQ)).elim

theorem l154OmegaTD4_tits : L154OmegaTD4 l154ExcTits := by
  intro p hp hp2 Ω _ _ S x y J hSn hqS hSp hSc hQ hxp hyp hxy hInn hF hJ hJy
  exact (l154_false_of_odd_inner hp hp2 (CFSG.HardMathSupport.Timmesfeld.Proving.glaPComponent_self
    hqS hSp) hSc hF.1 hyp hF (l154_oddInner_of_tits hQ)).elim

theorem l154OmegaNID_suz : L154OmegaNID l154ExcSuz := by
  intro p hp hp2 Ω _ _ S x y J hSn hqS hSp hSc hQ hxp hyp hxy hInn hF hJ hJy
  by_cases hcm : CentMod p S x
  · exact (l154_of_centMod hqS hSp hcm hF hJ).1
  · exact (l154_false_of_suzuki hp hp2 (CFSG.HardMathSupport.Timmesfeld.Proving.glaPComponent_self
      hqS hSp) hQ hxp (hInn.1 (Subgroup.mem_zpowers x)) hcm hInn hJ).elim

theorem l154OmegaTD4_suz : L154OmegaTD4 l154ExcSuz := by
  intro p hp hp2 Ω _ _ S x y J hSn hqS hSp hSc hQ hxp hyp hxy hInn hF hJ hJy
  by_cases hcm : CentMod p S x
  · exact (l154_of_centMod hqS hSp hcm hF hJ).2
  · exact (l154_false_of_suzuki hp hp2 (CFSG.HardMathSupport.Timmesfeld.Proving.glaPComponent_self
      hqS hSp) hQ hxp (hInn.1 (Subgroup.mem_zpowers x)) hcm hInn hJ).elim

end TitsSuz

section Two

theorem l154OmegaNID_two : L154OmegaNID l154ExcTwo := by
  intro p hp hp2 Ω _ _ S x y J hSn hqS hSp hSc hQ hxp hyp hxy hInn hF hJ hJy
  exact (l154_false_of_fieldOn_exponent_one hp hp2 hF (l154_labels_two hQ)).elim

theorem l154OmegaTD4_two : L154OmegaTD4 l154ExcTwo := by
  intro p hp hp2 Ω _ _ S x y J hSn hqS hSp hSc hQ hxp hyp hxy hInn hF hJ hJy
  exact (l154_false_of_fieldOn_exponent_one hp hp2 hF (l154_labels_two hQ)).elim

end Two

theorem l154_exc_cover_all (i : TauCeti.CFSGIndex) (h : l154Exc i) :
    l154ExcTits i ∨ l154ExcSuz i ∨ l154ExcTwo i ∨ l154ExcUntw i ∨ l154ExcTwE6 i ∨ l154ExcTriD4 i ∨
      l154ExcRee i := by
  rcases l154_exc_cover i h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · rcases l154_excRest_cover i h with h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

section Assembly

theorem l154OmegaNID_exc (hRee : L154OmegaNID l154ExcRee) : L154OmegaNID l154Exc :=
  l154OmegaNID_mono l154_exc_cover_all
    (l154OmegaNID_or l154OmegaNID_tits (l154OmegaNID_or l154OmegaNID_suz
      (l154OmegaNID_or l154OmegaNID_two (l154OmegaNID_or l154OmegaNID_excUntw_holds
        (l154OmegaNID_or l154OmegaNID_excTwE6_holds
          (l154OmegaNID_or l154OmegaNID_excTriD4_holds hRee))))))

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
