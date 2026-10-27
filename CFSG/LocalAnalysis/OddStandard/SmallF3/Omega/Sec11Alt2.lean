module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11A6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Statements2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11_autIn_mono {H K Y : Subgroup G} (h : H ≤ K) : autIn H Y ≤ autIn K Y := by
  simpa only [autIn] using
    Subgroup.map_mono (Subgroup.subgroupOf_mono (normalizer (Y : Set G)) h)

theorem sec11_not_alt1 {t : G} {S L : Subgroup G} (hyp : Hyp111 t S L) :
    ¬ Sec1011Alt1 t S L := by
  intro h
  obtain ⟨-, -, -, hcore, hab, -⟩ := h
  have hle : secCMB t S L ≤ secM t S L := inf_le_left
  have hXM : autIn (secCMB t S L) (secA t S L) ≤ secMstar t S L :=
    sec11_autIn_mono (Y := secA t S L) hle
  have hXbot : autIn (secCMB t S L) (secA t S L) = ⊥ := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hXM, hcore, sec11_pCore_hyp111 hyp,
      Subgroup.map_bot]
  have hcontr : (2 : ℕ) ^ 4 = 1 := by
    calc (2 : ℕ) ^ 4 = Nat.card ↥(autIn (secCMB t S L) (secA t S L)) := hab.2.symm
      _ = Nat.card ↥(⊥ : Subgroup (MulAut ↥(secA t S L))) := by rw [hXbot]
      _ = 1 := Subgroup.card_bot
  norm_num at hcontr

theorem sec11_class_card_six [Finite G] (h1011 : Asc82Lemma1011) {t : G} {L S : Subgroup G}
    {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) (hyp : Hyp111 t S L) :
    (conjClassIn (secM t S L) t).ncard = 6 := by
  have hdisj : Sec1011Alt1 t S L ∨ Sec1011Alt2 t S L z := h1011 G t L S z K1 K2 hctx
  rcases hdisj with h | h
  · exact absurd h (sec11_not_alt1 hyp)
  · exact h.2.2.2.1

end CFSG.OddStandard.SmallF3.Omega
