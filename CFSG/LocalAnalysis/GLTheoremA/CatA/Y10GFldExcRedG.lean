module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcGap
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcChev
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcOrd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.Assembly CFSG.StandardType CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.YS09Field
open CFSG.LocalAnalysis.GLTheoremA

theorem fldExc_G2
    (hG : FixGapG2) (hRig : GGLabelRigidInput) {S : Type} [Group S] [Finite S]
    (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel) (hT : labK.tag = .G2)
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
  obtain ⟨K, hKF, hKfin, hK, hQ⟩ := hraw
  obtain ⟨hsR, hnaR, θ, -, ⟨i, hi, f, hf, hind⟩, hout⟩ := hQ
  have hr2 : lab'.rank = 0 ∧ 2 ≤ lab'.n := by
    have h2 := hlam'.2
    rw [hT] at h2
    exact h2
  have hn : 1 ≤ lab'.n := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hK
  have hconj := RecipeExcLang.ggRawFieldConj_chev (τ := .G2) (ℓ := 2) (f := lab'.n) (p := p) hn hK
    hp (RecipeExcLang.innerFieldTrivial_G2 hr2.2 hK)
  have hfix : ∀ f' ∈ LargeEvenChevFieldImage LargeEvenCartanG2 K
      (LargeEvenChevH LargeEvenCartanG2 K false), orderOf f' = p → p ∣ lab'.n ∧
      ∃ (R₀ : Type) (_ : Group R₀) (lab'' : LargeEvenLabel), IsSimpleGroup R₀ ∧
        (∃ a b : R₀, a * b ≠ b * a) ∧ LargeEvenInLambda2 lab'' ∧
        canonLabel lab'' = ⟨lab'.tag, lab'.rank, lab'.n / p⟩ ∧ GGHasLabel lab'' R₀ ∧
        Nonempty (ggFixDer f' ≃* R₀) := by
    intro f' hf' hord'
    obtain ⟨hpn, R₀, hR₀, lab'', hs0, hna0, hl, hc, hG', hθ⟩ :=
      hG lab'.n p K hr2.2 hK hp hp2 f' hf' hord'
    refine ⟨hpn, R₀, hR₀, lab'', hs0, hna0, hl, ?_, hG', hθ⟩
    rw [hc, hT, hr2.1]
  have hcanK : canonLabel lab' = lab' := by
    unfold canonLabel
    rw [hT]
  exact fldExc_core hRig hp hcen hα hlabJ hJ hcanK θ hsR hnaR hi hf hind hout hconj hfix

theorem fldExc_E6
    (hG : FixGapE6) (hRig : GGLabelRigidInput) {S : Type} [Group S] [Finite S]
    (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel) (hT : labK.tag = .E6)
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
  obtain ⟨K, hKF, hKfin, hK, hQ⟩ := hraw
  obtain ⟨hsR, hnaR, θ, -, ⟨i, hi, f, hf, hind⟩, hout⟩ := hQ
  have hr0 : lab'.rank = 0 := by
    have h2 := hlam'.2
    rw [hT] at h2
    exact h2
  have hn : 1 ≤ lab'.n := hlam'.1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hK
  have hconj := RecipeExcLang.ggRawFieldConj_chev (τ := CFSG.Blueprint.Chevalley.TwistTag.E6.tag) (ℓ := 2) (f := lab'.n)
    (p := p) hn hK hp CFSG.StandardType.RecipeExcLang.innerFieldTrivial_E6
  have hfix : ∀ f' ∈ LargeEvenChevFieldImage (LargeEvenCartanE 6) K
      (LargeEvenChevH (LargeEvenCartanE 6) K false), orderOf f' = p → p ∣ lab'.n ∧
      ∃ (R₀ : Type) (_ : Group R₀) (lab'' : LargeEvenLabel), IsSimpleGroup R₀ ∧
        (∃ a b : R₀, a * b ≠ b * a) ∧ LargeEvenInLambda2 lab'' ∧
        canonLabel lab'' = ⟨lab'.tag, lab'.rank, lab'.n / p⟩ ∧ GGHasLabel lab'' R₀ ∧
        Nonempty (ggFixDer f' ≃* R₀) := by
    intro f' hf' hord'
    by_cases hcov : p ≠ 3 ∧ p ∣ 2 ^ lab'.n - 1
    · have hpn : p ∣ lab'.n :=
        dvd_of_chevField_order hn hK hp (LargeEvenChevH (LargeEvenCartanE 6) K false)
          (fun σ h hh => chevH_stable (LargeEvenCartanE 6) K false σ h hh) hf' hord'
      obtain ⟨K₀, hK₀F, hK₀fin, hK₀, hQ₀⟩ :=
        e6_fixStd hn hK hp hp2 hcov.1 hcov.2 hf' hord'
      obtain ⟨hs0, hna0, θ₀, -⟩ := hQ₀
      have hm : 1 ≤ lab'.n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
      refine ⟨hpn, LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K₀ false), inferInstance,
        ⟨.E6, lab'.rank, lab'.n / p⟩, hs0, hna0, ?_, ?_, ?_, ⟨θ₀⟩⟩
      · unfold LargeEvenInLambda2
        exact ⟨hm, hr0⟩
      · rw [hT]
        rfl
      · unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum
        exact ⟨K₀, hK₀F, hK₀fin, hK₀, ⟨MulEquiv.refl _⟩⟩
    · obtain ⟨hpn, R₀, hR₀, lab'', hs0, hna0, hl, hc, hG', hθ⟩ :=
        hG lab'.n p K hn hK hp hp2 hcov f' hf' hord'
      refine ⟨hpn, R₀, hR₀, lab'', hs0, hna0, hl, ?_, hG', hθ⟩
      rw [hc, hT, hr0]
  have hcanK : canonLabel lab' = lab' := by
    unfold canonLabel
    rw [hT]
  exact fldExc_core hRig hp hcen hα hlabJ hJ hcanK θ hsR hnaR hi hf hind hout hconj hfix

end CFSG.LocalAnalysis.GLTheoremA.Y10GField

end
