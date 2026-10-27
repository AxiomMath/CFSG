module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S1210NAlt1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S1210NA2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L1210
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Step1210N_of (hp : Asc82Pre11) (h122 : Asc82Lemma122) (h124 : Asc82Lemma124)
    (h125a : Asc82Lemma125a) (h125b : Asc82Lemma125b) (h128 : Asc82Lemma128) :
    Asc82Step1210N := by
  intro G _ _ t L S z K1 K2 E hctx
  have hV : IsElemAb2 (secV t S L E) 8 := h124 G t L S z K1 K2 E hctx
  have hCV := h125a G t L S z K1 K2 E hctx
  obtain ⟨hcentEq, ⟨e⟩⟩ := h125b G t L S z K1 K2 E hctx
  obtain ⟨X, hX⟩ := h122 G t L S z K1 K2 E hctx
  have hΩ := h128 G t L S z K1 K2 E X hctx hX
  have hbd := sec10BData_of hp.basic hp.facts.b5 hctx.toSec10Z
  have htS : t ∈ S := (hp.basic G t L S z hctx.toSec10Z).2.2.2.1
  have htN : t ∈ secN (secV t S L E) := sec12_S_le_secN hp hctx htS
  have ht2 : t * t = 1 := by rw [← sq, ← hctx.involution, pow_orderOf_eq_one]
  have hcent : Nat.card ↥(secNb (secV t S L E) ⊓ Subgroup.centralizer
      ({betaOf (secV t S L E) t} : Set (MulAut ↥(secV t S L E)))) = 120 := by
    have hz2 : Nat.card (Multiplicative (ZMod 2)) = 2 :=
      (Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2)).trans
        (Nat.card_zmod 2)
    rw [hcentEq, Nat.card_congr e.toEquiv, Nat.card_prod, sec12A5_card, hz2]
  rcases hΩ with h1 | h2
  · exact sec12N_alt1 hbd hV hCV h1 htN ht2 hcent
  · exact sec12N_alt2 h2 htN ht2 hcent

end CFSG.OddStandard.SmallF3.Omega
