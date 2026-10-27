module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidDescent

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem LangSetup.exists_charP_isAlgebraic_zmod (S : LangSetup τ L p) (hAlg : S.IsAlgebraic)
    {l f : ℕ} (hl : l.Prime) (hf : 0 < f) (hq : S.D.q = l ^ f) :
    ∃ _ : CharP L l, letI := ZMod.algebra L l; Algebra.IsAlgebraic (ZMod l) L := by
  have hl0 : ((l : ℕ) : L) = 0 := by
    have h := S.hqpow.2
    rw [hq, Nat.cast_pow] at h
    exact (pow_eq_zero_iff hf.ne').1 h
  haveI hch : CharP L l := (CharP.charP_iff_prime_eq_zero hl).2 hl0
  haveI : Fact l.Prime := ⟨hl⟩
  letI := ZMod.algebra L l
  refine ⟨hch, ⟨fun c => ?_⟩⟩
  obtain ⟨n, hn, hc⟩ := hAlg c
  have hq1 : 1 < S.D.q := S.hqpow.1.one_lt
  refine ⟨Polynomial.X ^ (S.D.q ^ n) - Polynomial.X,
    FiniteField.X_pow_card_sub_X_ne_zero (ZMod l) (Nat.one_lt_pow hn.ne' hq1), ?_⟩
  simp only [map_sub, map_pow, Polynomial.aeval_X]
  rw [hc, sub_self]

end CFSG.HardMathSupport.Timmesfeld.LangTorus
