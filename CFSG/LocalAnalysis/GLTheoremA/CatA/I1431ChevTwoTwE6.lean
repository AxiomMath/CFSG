module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoDefs
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.E6BadTwMain
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431C2

open CFSG.Blueprint

section TwE6


theorem u42FieldTwoAt_twistedE6 : U42FieldTwoAt fun d => ∃ q, d = .twistedE6 q := by
  intro Y _ _ _ _ hRk ⟨d, hv⟩ ⟨q, hdq⟩ hc hf ⟨e⟩ _ _ _
  subst hdq
  have hq2 : q.card = 2 := hf
  have hp : q.p = 2 := by simpa using hc
  have hexp : q.exponent = 1 := by
    have h := q.card_def
    rw [hq2, hp] at h
    exact (Nat.pow_right_injective (le_refl 2) (h.symm.trans (pow_one 2).symm))
  have hm := CFSG.StandardType.ChevTwo.twistedChevalleyModel_of_bridge
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv hp e
  have hCE : ChevalleyExceptionalModel (Y ⧸ Subgroup.center Y) .twistedE6 2 q.exponent :=
    ⟨⟨Nat.prime_two, q.exponent_pos, rfl⟩, hm⟩
  have hLM : LieModel (Y ⧸ Subgroup.center Y) .twistedE6 0 2 q.exponent :=
    .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags], hCE⟩)
  exact (CFSG.HardMathSupport.Dickson.Sec6.I1431.rkY_false_twE6 hRk Nat.prime_two
    q.exponent_pos hCE hLM (by rw [hexp]; norm_num)).elim

end TwE6

end CFSG.LocalAnalysis.GLTheoremA.I1431C2

end
