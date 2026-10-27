module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888L515ab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888L515G
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888L515H

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma515c_of (hS : Asc82Lemma515Setting) (h514 : Asc82Lemma514)
    (hF2 : Asc82FactPocketsTwo) (hb : Asc82Lemma515b) (h52a : Asc82Lemma52a)
    (h52b : Asc82Lemma52b) (h56 : Asc82Lemma56) (hZ : Asc82ZExists) (hB : Asc82Sec5FactB5)
    (h512b : Asc82Lemma512b) (h512K : Asc82Lemma512K) (h512H : Asc82Lemma512H)
    (tab : Asc82Tab5) : Asc82Lemma515c := by
  intro G _ _ t L S z r B A K₁ K₂ h c d hd
  have hd2 : orderOf d = 2 := hd.1
  have hdz : d ≠ z := hd.2.1
  have hz2 : orderOf z = 2 := c.pocket.1
  obtain ⟨I, hs, P, hP, hPI⟩ := hS G t L S z r B A K₁ K₂ h c d hd
  obtain ⟨hlay, -⟩ := sec5_setting_data h52a h52b h56 hZ hB h512b hs
  obtain ⟨i, j, hij, hdij⟩ := sec5_delta_support h514 c hd
  obtain ⟨l, m, hlm, hli, hlj, hmi, hmj⟩ := sec5_exists_compl i j hij
  have hPeq : P = Kfam5 K₁ K₂ h l ⊔ Kfam5 K₁ K₂ h m :=
    (sec5_kOf_iff h514 c hij hlm hli hlj hmi hmj hd2 hdz hdij P).mp hP
  have hle : Kfam5 K₁ K₂ h l ⊔ Kfam5 K₁ K₂ h m ≤ I := hPeq ▸ hPI
  have hp : Sec5Pair (Kfam5 K₁ K₂ h l) (Kfam5 K₁ K₂ h m) z :=
    Sec5Pair.of_quad (sec5b517_quad h514 c) hlm
  obtain ⟨S'', r'', B'', A'', P₁, P₂, h'', hc''⟩ :=
    sec5_exists_hctx_of_pair h52a h52b h56 hZ hB h512b h512K h512H tab hs hz2 hdz.symm hp hle
  rw [← hlay] at hc''
  exact ⟨S'', r'', B'', A'', P₁, P₂, h'', hc'', sec5_gamma_eq h514 hF2 hb c hd hc''⟩

theorem asc82Lemma515_of (hS : Asc82Lemma515Setting) (hF2 : Asc82FactPocketsTwo)
    (h514 : Asc82Lemma514) (h52a : Asc82Lemma52a) (h52b : Asc82Lemma52b) (h56 : Asc82Lemma56)
    (hZ : Asc82ZExists) (hB : Asc82Sec5FactB5) (h512b : Asc82Lemma512b)
    (h512K : Asc82Lemma512K) (h512H : Asc82Lemma512H) (tab : Asc82Tab5) :
    Asc82Lemma515a ∧ Asc82Lemma515b ∧ Asc82Lemma515c := by
  obtain ⟨ha, hb⟩ := asc82Lemma515ab_of hS h514 h52a h52b h56 hZ hB h512b h512K tab
  exact ⟨ha, hb,
    asc82Lemma515c_of hS h514 hF2 hb h52a h52b h56 hZ hB h512b h512K h512H tab⟩

end CFSG.OddStandard.SmallF3.Omega
