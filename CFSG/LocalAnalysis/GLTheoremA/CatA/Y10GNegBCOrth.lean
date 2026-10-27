module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNegBCLab
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNegBCOrd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnOrth
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsOrth
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldOrthDict
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GSympLabel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GNegBC

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem negC_orth_inn (hRig : GGLabelRigidInput) {S : Type} [Group S] [Finite S] {p : ℕ}
    {α : MulAut S} {J : Subgroup S} {labK labJ : GLALabel} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : Subgroup.center S = ⊥) (hD5 : labK.tag = .D ∧ labK.rank = 5)
    (hlabK : HasLabel S (fun l : GLALabel => l = labK))
    (hin : InnDiagKind S labK α) (hα : α ^ p = 1)
    (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ))
    (hJ : GLAPComponent p (fixSubgroup α) J) :
    ¬ (labJ.tag = .twD ∧ labJ.rank = 5) := by
  have hFam : FamOrth labK := Or.inl ⟨hD5.1, by omega⟩
  obtain ⟨hmodel, a, rfl⟩ := Y10GInnOrthMark.innDiagKind_orth_data hcen hFam hin
  have hap : a ^ p = 1 := by
    have hc : a ^ p ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz := DFunLike.congr_fun (show MulAut.conj (a ^ p) = 1 by rw [map_pow, hα]) z
      rw [MulAut.conj_apply, MulAut.one_apply] at hz
      exact (mul_inv_eq_iff_eq_mul.mp hz).symm
    rw [hcen] at hc
    exact Subgroup.mem_bot.mp hc
  obtain ⟨t, ht, hG⟩ : ∃ t : StatedLieTag, (t = .POmegaPlus ∨ t = .POmegaMinus) ∧
      StatedClassicalModel S t labK.rank 2 (canonLabel labK).n := by
    rcases hmodel with hG | hG
    · exact ⟨_, Or.inl rfl, hG⟩
    · exact ⟨_, Or.inr rfl, hG⟩
  have hcK : canonLabel labK = labK := by
    obtain ⟨ht1, ht2⟩ := hD5
    simp [canonLabel, ht1, ht2]
  rcases Y10GInnOrthComp.quotCenter_cases_of_glaPComponent_conj_omega ht hG hp hp2 a hap hJ with
    ⟨b, k, E, _, _, hb, hE, -, hφ⟩ | ⟨b, k, E, _, _, τ, hτ, hb, hτk, hE, -, hφ⟩ |
      ⟨s, K', _, _, hs, hK', hne, ⟨φ⟩⟩ | ⟨s, hM | hM⟩
  ·
    exact not_twD5_of_canon
      (Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig _ labJ b k E hb hE hlabJ hφ) (by decide)
  ·
    rcases uniLabel_cases hRig τ hτ hb hτk hE hlabJ hφ with h | h
    · exact not_twD5_of_canon h (by decide)
    · exact not_twD5_of_canon h (by decide)
  ·
    exact not_twD5_of_canon
      (Y10GSympLabel.canonLabel_eq_of_quot_statedSp hRig hs hK' hne hlabJ φ) (by decide)
  ·
    exact not_twD5_of_canon
      ((Y10GFldOrth.orthLabelDict_of_ggLabelRigidInput hRig _ labJ s _ hlabJ).1 hM) (by decide)
  ·
    have hcan := (Y10GFldOrth.orthLabelDict_of_ggLabelRigidInput hRig _ labJ s _ hlabJ).2 hM
    rintro ⟨h1, h2⟩
    have hcJ : canonLabel labJ = labJ := by
      obtain ⟨t', r', n'⟩ := labJ
      simp only at h1 h2
      subst h1 h2
      simp [canonLabel]
    have hs5 : s = 5 := by
      have := congrArg LargeEvenLabel.rank (hcJ.symm.trans hcan)
      simp only at this
      omega
    subst hs5
    have hplus : t = .POmegaPlus := by
      rcases ht with rfl | rfl
      · rfl
      · exfalso
        have hG' : StatedClassicalModel (S ⧸ Subgroup.center S) .POmegaMinus labK.rank 2
            (canonLabel labK).n := by
          have e : S ⧸ Subgroup.center S ≃* S :=
            (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
          exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hG
        have := (Y10GFldOrth.orthLabelDict_of_ggLabelRigidInput hRig S labK labK.rank _ hlabK).2 hG'
        rw [hcK] at this
        have h3 := congrArg LargeEvenLabel.tag this
        simp only [hD5.1] at h3
        exact absurd h3 (by decide)
    subst hplus
    have hf : 1 ≤ (canonLabel labK).n := hG.1.2.1
    have hGcard : Nat.card S = ordD 5 (2 ^ (canonLabel labK).n) := by
      rw [← hD5.2]
      exact (CFSG.Timmesfeld.card_statedClassicalModel_two hG).2.2.2.1 rfl
    exact no_omega_minus_five_in_omega_plus hf hGcard J hM

theorem negC_orth (hRig : GGLabelRigidInput) (hFld : FldOrth) {S : Type} [Group S] [Finite S]
    {p : ℕ} {α : MulAut S} {J : Subgroup S} {labK labJ : GLALabel} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : Subgroup.center S = ⊥) (hD5 : labK.tag = .D ∧ labK.rank = 5)
    (hlabK : HasLabel S (fun l : GLALabel => l = labK)) (hα : α ^ p = 1)
    (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ))
    (hJ : GLAPComponent p (fixSubgroup α) J) :
    ¬ (labJ.tag = .twD ∧ labJ.rank = 5) := by
  have hFam : FamOrth labK := Or.inl ⟨hD5.1, by omega⟩
  rcases Y10GClsOrth.clsOrth_holds S p α labK hFam hp hp2 hcen hlabK hα with hin | hfld | htri
  · exact negC_orth_inn hRig hp hp2 hcen hD5 hlabK hin hα hlabJ hJ
  · obtain ⟨-, htag, -⟩ := hFld S p α J labK labJ hFam hp hp2 hcen hfld hα hlabJ hJ
    refine not_twD5_of_canon (t := (canonLabel labJ).tag) (r := (canonLabel labJ).rank)
      (k := (canonLabel labJ).n) rfl ?_
    rw [← htag]
    obtain ⟨ht1, ht2⟩ := hD5
    simp [canonLabel, ht1, ht2]
  · omega

end CFSG.LocalAnalysis.GLTheoremA.Y10GNegBC
