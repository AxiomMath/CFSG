module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3Unpack
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3Field
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreDisp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcLang

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

variable {Ω : Type} [Group Ω] [Finite Ω]

section Certs


theorem false_of_exc3_big {p : ℕ} {B X D J : Subgroup Ω} {x : Ω} (H : ExcHyp p B X D J x) (hp3 : p = 3)
    (hbig : catalogIs (PSimple p X) ExcBigIdx) : False := by
  subst hp3
  obtain ⟨f, -, hf3, hJ⟩ := type167J_three H.htype
  obtain ⟨k, qc, hv, hk, hqc, ⟨eE⟩⟩ := exc3_family hbig
  have hef : qc.exponent ∣ f := exc3_fieldRel H hJ hk hqc eE
  have h3 : 3 ∣ 2 ^ qc.exponent + 1 := exc3_arith hef hf3
  have hnt := exc3_nontrivial H
  have hcm := exc3_not_centMod H
  have hJx := exc3_glaPComponent_cx H
  have hcard : qc.card = 2 ^ qc.exponent := by rw [TauCeti.PrimePower.card_def, hqc]
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨L, _, _, _, SL, a, i, w, hq, hρ, hT, hap, ha1, hqs, ⟨eR⟩⟩ :=
      exc_lang_untw H.hp H.hp2 (Or.inl rfl) hqc H.hX hnt ⟨eE⟩ H.hxp H.hxN hcm H.hinn hJx
    exact exc3core_false_F4 SL i (hq.trans hcard) h3 hT hap ha1 hqs
      ((catalogIs_congr eR).1 hJ)
  · obtain ⟨L, _, _, _, SL, a, i, w, hq, hρ, hT, hap, ha1, hqs, ⟨eR⟩⟩ :=
      exc_lang_untw H.hp H.hp2 (Or.inr (Or.inl rfl)) hqc H.hX hnt ⟨eE⟩ H.hxp H.hxN hcm H.hinn hJx
    exact exc3core_false_E6 SL i (hq.trans hcard) h3 hT hap ha1 hqs
      ((catalogIs_congr eR).1 hJ)
  · obtain ⟨L, _, _, _, SL, a, i, w, hq, hρ, hT, hap, ha1, hqs, ⟨eR⟩⟩ :=
      exc_lang_twE6 H.hp H.hp2 hqc H.hX hnt ⟨eE⟩ H.hxp H.hxN hcm H.hinn hJx
    exact exc3core_false_E6 SL i (hq.trans hcard) h3 hT hap ha1 hqs
      ((catalogIs_congr eR).1 hJ)
  · obtain ⟨L, _, _, _, SL, a, i, w, hq, hρ, hT, hap, ha1, hqs, ⟨eR⟩⟩ :=
      exc_lang_untw H.hp H.hp2 (Or.inr (Or.inr (Or.inl rfl))) hqc H.hX hnt ⟨eE⟩ H.hxp H.hxN hcm
        H.hinn hJx
    exact exc3core_false_E7 SL i w hρ (hq.trans hcard) h3 hT hap ha1
      hqs ((catalogIs_congr eR).1 hJ)
  · obtain ⟨L, _, _, _, SL, a, i, w, hq, hρ, hT, hap, ha1, hqs, ⟨eR⟩⟩ :=
      exc_lang_untw H.hp H.hp2 (Or.inr (Or.inr (Or.inr rfl))) hqc H.hX hnt ⟨eE⟩ H.hxp H.hxN hcm
        H.hinn hJx
    exact exc3core_false_E8 SL i (hq.trans hcard) h3 hT hap ha1
      hqs ((catalogIs_congr eR).1 hJ)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.I167

end
