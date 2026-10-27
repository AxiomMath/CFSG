module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011Br1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011P2c3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Bundles

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma1011_of (h36 : Asc82Lemma36) (h : Asc82Res10a) (h109 : Asc82Lemma109)
    (h1010 : Asc82Lemma1010) (hb : Asc82Basic10) (hf : Asc82Facts10) : Asc82Lemma1011 := by
  intro G _ _ t L S z K1 K2 hctx
  obtain ⟨φ, hs⟩ := sec1011_setup_of h.l105 h109 h1010 hb hf.b5 hctx
  have h107b := h.l107b G t L S z K1 K2 hctx
  have hpsp : IsPSp43 L := (hb G t L S z hctx.toSec10Z).1
  have hLC : L ⊓ centralizer (L : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_psp43 hctx.component.isQuasisimple hpsp
  have hN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    sec4_mem_normalizer h36 hctx.toSec10Z.toSec10Setting.toSec3SettingLB
  have hB16 : Nat.card (secB S L) = 2 ^ 4 := (sec10BData_of hb hf.b5 hctx.toSec10Z).2.1
  rcases sec1011_core_dichotomy (sec1011_core_of_setup hs) with h6 | hB
  · exact Or.inr (sec1011_alt2_of_setup hs h6 h107b (sec1011_p2_of_setup hf.b5 hf.out5 hpsp hLC
      (h.l102 G t L hctx.toSec10Z.toSec10Setting) hN hB16 hs h6 h107b))
  · exact Or.inl (sec1011_alt1_of_setup hs hB h107b)

end CFSG.OddStandard.SmallF3.Omega
