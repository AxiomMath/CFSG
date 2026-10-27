module

public import CFSG.GH74.GLS.TwoThin.ClassCongr

public section

namespace CFSG.GH74.E2

open Subgroup Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin Assembly.LowTwoRank

variable {K K' : Type} [Group K] [Group K']

theorem evenLieType_of_mulEquiv (e : K ≃* K') (h : EvenLieType K) : EvenLieType K' := by
  obtain ⟨t, n, f, hadm, hmod⟩ := h
  exact ⟨t, n, f, hadm, lieModel_of_mulEquiv e hmod⟩

theorem inChev2_of_mulEquiv (e : K ≃* K') (h : InChev2 K) : InChev2 K' := by
  rcases h with h | h | h
  · exact Or.inl (evenLieType_of_mulEquiv e h)
  · exact Or.inr (Or.inl (nonempty_alternating_of_mulEquiv e h))
  · exact Or.inr (Or.inr (lieModel_of_mulEquiv e h))

theorem simpleInC2_of_mulEquiv (e : K ≃* K') (h : SimpleInC2 K) : SimpleInC2 K' := by
  have hL : ∀ {t : StatedLieTag} {n p f : ℕ}, LieModel K t n p f → LieModel K' t n p f :=
    fun h => lieModel_of_mulEquiv e h
  have hS : ∀ {s : TauCeti.SporadicName}, NativeSporadic.IsSporadic K s →
      NativeSporadic.IsSporadic K' s := fun h => isSporadic_of_mulEquiv e h
  obtain ⟨hs, h⟩ := h
  refine ⟨e.isSimpleGroup_congr.1 hs, ?_⟩
  exact h.imp (inChev2_of_mulEquiv e) <| Or.imp (hasL2Model_of_mulEquiv e) <| Or.imp hL <|
    Or.imp hL <| Or.imp hL <| Or.imp hL <| Or.imp hS <| Or.imp hS <| Or.imp hS <| Or.imp hS <|
    Or.imp hS <| Or.imp hS <| Or.imp hS <| Or.imp hS <| Or.imp hS <| Or.imp hS <| Or.imp hS <|
    Or.imp hS <| Or.imp hS <| Or.imp hS <| Or.imp hS <| Or.imp hS <| Or.imp hS <| Or.imp hS <|
    hS

theorem excludedFromC2_of_mulEquiv (e : K ≃* K') (h : ExcludedFromC2 K) : ExcludedFromC2 K' := by
  rcases h with h | h | ⟨F, _, _, hF, ⟨e'⟩⟩ | ⟨F, _, _, hF, ⟨e'⟩⟩ | ⟨F, _, _, hF, ⟨e'⟩⟩ | ⟨h, hexp⟩
  · exact Or.inl (hasSL2Model_of_mulEquiv e h)
  · exact Or.inr (Or.inl (isDoubleCoverOfAlt_of_mulEquiv e h))
  · exact Or.inr (Or.inr (Or.inl ⟨F, inferInstance, inferInstance, hF, ⟨e.symm.trans e'⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨F, inferInstance, inferInstance, hF,
      ⟨e.symm.trans e'⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨F, inferInstance, inferInstance, hF,
      ⟨e.symm.trans e'⟩⟩))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨isL34Quotient_of_mulEquiv e h, ?_⟩))))
    rw [← Monoid.exponent_eq_of_mulEquiv (Subgroup.centerCongr e)]
    exact hexp

theorem inC2_of_mulEquiv (e : K ≃* K') (h : InC2 K) : InC2 K' := by
  obtain ⟨hq, hc, hs, hne⟩ := h
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, ?_, ?_,
    fun hex => hne (excludedFromC2_of_mulEquiv e.symm hex)⟩
  · have h1 : (center K).map e.toMonoidHom = center K' := Subgroup.map_center_eq e
    have h2 : (CFSG.pCore 2 K).map e.toMonoidHom = CFSG.pCore 2 K' := CFSG.pCore_map_iso 2 e
    rw [← h1, ← h2, hc]
  · exact simpleInC2_of_mulEquiv
      (QuotientGroup.congr (center K) (center K') e (Subgroup.map_center_eq e)) hs

end CFSG.GH74.E2
