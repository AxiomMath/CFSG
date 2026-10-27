module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bCl

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank Blueprint
open P58b

theorem harris82Lemma58bCover_of_rows
    (hE : ∀ τ ∈ chevalleyExceptionalTags, Foote5.OddLieCore.Exc.NoPSLTwoOddCentreComponent τ)
    (hGA : TBLit.GriessMultipliersAllModels) (hTB : CFSG.TauCetiBridge.TypewiseBridges)
    (hcl : Burgoyne.BurgoynePropBClassicalS)
    (hPSL4 : Harris82Lemma58bNoConfig .PSL 4) (hPSU4 : Harris82Lemma58bNoConfig .PSU 4)
    (hPSp4 : Harris82Lemma58bNoConfig .PSp 2) (hB : ∀ n, Harris82Lemma58bRow .POmegaOdd n)
    (hD : ∀ n, Harris82Lemma58bRow .POmegaPlus n)
    (h2D : ∀ n, Harris82Lemma58bRow .POmegaMinus n) :
    Harris82Lemma58bCover := by
  intro X _ _ hX hO p hp hp2 hChev k c t Q L hcfg hL htL
  obtain ⟨τ, n, f, hm⟩ := hChev
  have hno : ∀ {τ' : StatedLieTag} {n' : ℕ}, LieModel (X ⧸ center X) τ' n' p f →
      Harris82Lemma58bNoConfig τ' n' → Lemma58bConclusion X p k L :=
    fun hm' h => (h X hX hO p f hp hp2 hm' k c t Q hcfg).elim
  have hadm := admissible_of_lieModel hm
  cases τ with
  | PSL =>
    have hn : 2 ≤ n := hadm.2.2.1
    rcases Nat.even_or_odd n with hev | hodd
    · rcases (by obtain ⟨j, hj⟩ := hev; omega : n = 2 ∨ n = 4 ∨ 6 ≤ n) with rfl | rfl | h6
      · exact hno hm noConfig_PSL_two
      · exact hno hm hPSL4
      · exact hno hm (noConfig_classicalS hcl (Or.inl ⟨Or.inl rfl, h6, hev⟩))
    · exact hno hm (noConfig_PSL_odd hodd)
  | PSU =>
    have hn : 3 ≤ n := hadm.2.2.1
    rcases Nat.even_or_odd n with hev | hodd
    · rcases (by obtain ⟨j, hj⟩ := hev; omega : n = 4 ∨ 6 ≤ n) with rfl | h6
      · exact hno hm hPSU4
      · exact hno hm (noConfig_classicalS hcl (Or.inl ⟨Or.inr rfl, h6, hev⟩))
    · exact hno hm (noConfig_PSU_odd hodd)
  | PSp =>
    have hn : 2 ≤ n := hadm.2.2.1
    rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | h3
    · exact hno hm hPSp4
    · exact hno hm (noConfig_classicalS hcl (Or.inr ⟨rfl, h3⟩))
  | POmegaOdd => exact hB n X hX hO p f hp hp2 hm k c t Q L hcfg hL htL
  | POmegaPlus => exact hD n X hX hO p f hp hp2 hm k c t Q L hcfg hL htL
  | POmegaMinus => exact h2D n X hX hO p f hp hp2 hm k c t Q L hcfg hL htL
  | G2 => exact hno hm (noConfig_exc_of hE (by decide) n)
  | F4 => exact hno hm (noConfig_exc_of hE (by decide) n)
  | E6 => exact hno hm (noConfig_exc_of hE (by decide) n)
  | E7 => exact hno hm (noConfig_exc_of hE (by decide) n)
  | E8 => exact hno hm (noConfig_exc_of hE (by decide) n)
  | twistedE6 => exact hno hm (noConfig_exc_of hE (by decide) n)
  | trialityD4 => exact hno hm (noConfig_exc_of hE (by decide) n)
  | twistedG2 => exact hno hm (noConfig_twistedG2 hTB hGA n)
  | twistedB2 => exact hno hm (noConfig_char_two (Or.inl rfl) n)
  | twistedF4 => exact hno hm (noConfig_char_two (Or.inr (Or.inl rfl)) n)
  | Tits => exact hno hm (noConfig_char_two (Or.inr (Or.inr rfl)) n)

theorem harris82Lemma58b_of_rows
    (hE : ∀ τ ∈ chevalleyExceptionalTags, Foote5.OddLieCore.Exc.NoPSLTwoOddCentreComponent τ)
    (hGA : TBLit.GriessMultipliersAllModels) (hTB : CFSG.TauCetiBridge.TypewiseBridges)
    (hcl : Burgoyne.BurgoynePropBClassicalS)
    (hPSL4 : Harris82Lemma58bNoConfig .PSL 4) (hPSU4 : Harris82Lemma58bNoConfig .PSU 4)
    (hPSp4 : Harris82Lemma58bNoConfig .PSp 2) (hB : ∀ n, Harris82Lemma58bRow .POmegaOdd n)
    (hD : ∀ n, Harris82Lemma58bRow .POmegaPlus n)
    (h2D : ∀ n, Harris82Lemma58bRow .POmegaMinus n) :
    Harris82Lemma58b :=
  harris82Lemma58b_of_cover
    (harris82Lemma58bCover_of_rows hE hGA hTB hcl hPSL4 hPSU4 hPSp4 hB hD h2D)

end CFSG.ComponentClassification.HarrisLit.T1
