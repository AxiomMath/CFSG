module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcRedT
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcRedG
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcChev
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.Assembly CFSG.StandardType CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

open CFSG.LocalAnalysis.GLTheoremA.YS09Field
open CFSG.LocalAnalysis.GLTheoremA

section Certs


theorem fldExc_twF4 (hG : FixGapTwF4) (hRig : GGLabelRigidInput) {S : Type} [Group S] [Finite S]
    (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel) (hT : labK.tag = .twF4)
    (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥) (hfld : FieldKind S labK α)
    (hα : α ^ p = 1) (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ))
    (hJ : GLAPComponent p (fixSubgroup α) J) :
    (canonLabel labK).n = p * (canonLabel labJ).n ∧ (canonLabel labK).tag = (canonLabel labJ).tag ∧
      (canonLabel labK).rank = (canonLabel labJ).rank := by
  unfold FieldKind CFSG.Assembly.LargeEvenMarking at hfld
  obtain ⟨-, lab', hlam', hraw⟩ := hfld
  obtain ⟨_, _, _, _, hQ0⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hlab, -⟩ := hQ0
  subst hlab
  unfold CFSG.Assembly.LargeEvenRawDatum at hraw
  rw [hT] at hraw
  obtain ⟨hr0, hodd, h3⟩ : lab'.rank = 0 ∧ Odd lab'.n ∧ 3 ≤ lab'.n := by
    have h2 := hlam'.2
    rw [hT] at h2
    exact h2
  have hodd' : 2 * ((lab'.n - 1) / 2) + 1 = lab'.n := by
    obtain ⟨m, hm⟩ := hodd
    omega
  have ha : 1 ≤ (lab'.n - 1) / 2 := by omega
  have hne : ¬ (lab'.n - 1) / 2 = 0 := by omega
  obtain ⟨K, hKF, hKfin, hK, hQ⟩ := hraw
  rw [if_neg hne] at hQ
  obtain ⟨hsR, hnaR, θ, -, ⟨i, hi, f, hf, hind⟩, hout⟩ := hQ
  have hconj := RecipeExcLang.ggRawFieldConj_twF4 (a := (lab'.n - 1) / 2) ha hK hp
  have hfix : ∀ f' ∈ LargeEvenChevFieldImage LargeEvenCartanF4 K
      (LargeEvenTwF4H ((lab'.n - 1) / 2) K), orderOf f' = p →
      p ∣ lab'.n ∧ ∃ (R₀ : Type) (_ : Group R₀) (lab'' : LargeEvenLabel),
        IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ LargeEvenInLambda2 lab'' ∧
        canonLabel lab'' = ⟨lab'.tag, lab'.rank, lab'.n / p⟩ ∧ GGHasLabel lab'' R₀ ∧
        Nonempty (ggFixDer f' ≃* R₀) := by
    intro f' hf' hord'
    obtain ⟨hpn, R₀, hR₀, lab'', hs0, hna0, hl, hc, hG', hθ⟩ :=
      hG ((lab'.n - 1) / 2) p K ha hK hp hp2 f' hf' hord'
    rw [hodd'] at hpn
    refine ⟨hpn, R₀, hR₀, lab'', hs0, hna0, hl, ?_, hG', hθ⟩
    rw [hc, hodd', hT, hr0]
  have hcanK : canonLabel lab' = lab' := by
    unfold canonLabel
    rw [hT]
  exact fldExc_core hRig hp hcen hα hlabJ hJ hcanK θ hsR hnaR hi hf hind hout hconj hfix

theorem fldExc_G2der {S : Type} [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S)
    (labK labJ : GLALabel) (hT : labK.tag = .G2der) (hfld : FieldKind S labK α) :
    (canonLabel labK).n = p * (canonLabel labJ).n ∧ (canonLabel labK).tag = (canonLabel labJ).tag ∧
      (canonLabel labK).rank = (canonLabel labJ).rank := by
  unfold FieldKind CFSG.Assembly.LargeEvenMarking at hfld
  obtain ⟨-, lab', hlam', hraw⟩ := hfld
  obtain ⟨_, _, _, _, hQ0⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hlab, -⟩ := hQ0
  subst hlab
  unfold CFSG.Assembly.LargeEvenRawDatum at hraw
  rw [hT] at hraw
  obtain ⟨K, hKF, hKfin, hK, hQ⟩ := hraw
  obtain ⟨hsR, hnaR, θ, -, ⟨i, hi, f, hf, hind⟩, hout⟩ := hQ
  have hf1 := chevFieldImage_eq_one_of_card_two hK _ hf
  subst hf1
  exact (hout ⟨i, hi, by simpa using hind⟩).elim

theorem fldExc_twF4der {S : Type} [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S)
    (labK labJ : GLALabel) (hT : labK.tag = .twF4der) (hfld : FieldKind S labK α) :
    (canonLabel labK).n = p * (canonLabel labJ).n ∧ (canonLabel labK).tag = (canonLabel labJ).tag ∧
      (canonLabel labK).rank = (canonLabel labJ).rank := by
  unfold FieldKind CFSG.Assembly.LargeEvenMarking at hfld
  obtain ⟨-, lab', hlam', hraw⟩ := hfld
  obtain ⟨_, _, _, _, hQ0⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hlab, -⟩ := hQ0
  subst hlab
  have hn1 : lab'.n = 1 := by
    have h2 := hlam'.2
    rw [hT] at h2
    exact h2.2
  unfold CFSG.Assembly.LargeEvenRawDatum at hraw
  rw [hT] at hraw
  obtain ⟨K, hKF, hKfin, hK, hQ⟩ := hraw
  have hK2 : Nat.card K = 2 := by
    have h0 : (lab'.n - 1) / 2 = 0 := by omega
    rw [hK, h0]
    norm_num
  obtain ⟨hsR, hnaR, θ, -, ⟨i, hi, f, hf, hind⟩, hout⟩ := hQ
  have hf1 := chevFieldImage_eq_one_of_card_two hK2 _ hf
  subst hf1
  exact (hout ⟨i, hi, by simpa using hind⟩).elim

theorem fldExc_of_gaps (hG2 : FixGapG2) (hE6 : FixGapE6) (htwE6 : FixGapTwE6)
    (htriD4 : FixGapTriD4) (htwB2 : FixGapTwB2) (htwF4 : FixGapTwF4) : FldExc := by
  intro S _ _ p α J labK labJ hFam hp hp2 hcen hfld hnot hα hlabJ hJ
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  unfold FamExc at hFam
  rcases hFam with h | h | h | h | h | h | h | h | h | h | h
  · exact fldExc_E6 hE6 hRig p α J labK labJ h hp hp2 hcen hfld hα hlabJ hJ
  · exact fldExc_E7 hRig p α J labK labJ h hp hp2 hcen hfld hα hlabJ hJ
  · exact fldExc_E8 hRig p α J labK labJ h hp hp2 hcen hfld hα hlabJ hJ
  · exact fldExc_F4 hRig p α J labK labJ h hp hp2 hcen hfld hα hlabJ hJ
  · exact fldExc_twE6 htwE6 hRig p α J labK labJ h hp hp2 hcen hfld hα hlabJ hJ
  · exact fldExc_triD4 htriD4 hRig p α J labK labJ h hp hp2 (fun h3 => hnot ⟨h, h3⟩) hcen hfld hα
      hlabJ hJ
  · exact fldExc_G2 hG2 hRig p α J labK labJ h hp hp2 hcen hfld hα hlabJ hJ
  · exact fldExc_G2der p α J labK labJ h hfld
  · exact fldExc_twB2 htwB2 hRig p α J labK labJ h hp hp2 hcen hfld hα hlabJ hJ
  · exact fldExc_twF4 htwF4 hRig p α J labK labJ h hp hp2 hcen hfld hα hlabJ hJ
  · exact fldExc_twF4der p α J labK labJ h hfld

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10GField

end
