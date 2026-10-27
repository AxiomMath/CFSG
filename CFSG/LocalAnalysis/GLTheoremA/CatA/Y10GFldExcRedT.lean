module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcGap
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcRed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.Assembly CFSG.StandardType CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

open CFSG.LocalAnalysis.GLTheoremA.YS09Field
open CFSG.LocalAnalysis.GLTheoremA

section Certs


theorem fldExc_twE6 (hG : FixGapTwE6) (hRig : GGLabelRigidInput) {S : Type} [Group S] [Finite S]
    (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel) (hT : labK.tag = .twE6)
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
  have hconj := RecipeExcLang.ggRawFieldConj_twE6 hn hK hp hp2
  have hfix : ∀ f' ∈ LargeEvenChevFieldImage (LargeEvenCartanE 6) K
      (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 lab'.n), orderOf f' = p →
      p ∣ lab'.n ∧ ∃ (R₀ : Type) (_ : Group R₀) (lab'' : LargeEvenLabel),
        IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ LargeEvenInLambda2 lab'' ∧
        canonLabel lab'' = ⟨lab'.tag, lab'.rank, lab'.n / p⟩ ∧ GGHasLabel lab'' R₀ ∧
        Nonempty (ggFixDer f' ≃* R₀) := by
    intro f' hf' hord'
    obtain ⟨hpn, R₀, hR₀, lab'', hs0, hna0, hl, hc, hG', hθ⟩ :=
      hG lab'.n p K hn hK hp hp2 f' hf' hord'
    refine ⟨hpn, R₀, hR₀, lab'', hs0, hna0, hl, ?_, hG', hθ⟩
    rw [hc, hT, hr0]
  have hcanK : canonLabel lab' = lab' := by
    unfold canonLabel
    rw [hT]
  exact fldExc_core hRig hp hcen hα hlabJ hJ hcanK θ hsR hnaR hi hf hind hout hconj hfix

theorem fldExc_triD4 (hG : FixGapTriD4) (hRig : GGLabelRigidInput) {S : Type} [Group S] [Finite S]
    (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel) (hT : labK.tag = .triD4)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hcen : Subgroup.center S = ⊥)
    (hfld : FieldKind S labK α) (hα : α ^ p = 1) (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ))
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
  have hconj := RecipeExcLang.ggRawFieldConj_triD4 hn hK hp hp3
  have hfix : ∀ f' ∈ LargeEvenChevFieldImage LargeEvenCartanD4 K
      (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 lab'.n), orderOf f' = p →
      p ∣ lab'.n ∧ ∃ (R₀ : Type) (_ : Group R₀) (lab'' : LargeEvenLabel),
        IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ LargeEvenInLambda2 lab'' ∧
        canonLabel lab'' = ⟨lab'.tag, lab'.rank, lab'.n / p⟩ ∧ GGHasLabel lab'' R₀ ∧
        Nonempty (ggFixDer f' ≃* R₀) := by
    intro f' hf' hord'
    obtain ⟨hpn, R₀, hR₀, lab'', hs0, hna0, hl, hc, hG', hθ⟩ :=
      hG lab'.n p K hn hK hp hp2 hp3 f' hf' hord'
    refine ⟨hpn, R₀, hR₀, lab'', hs0, hna0, hl, ?_, hG', hθ⟩
    rw [hc, hT, hr0]
  have hcanK : canonLabel lab' = lab' := by
    unfold canonLabel
    rw [hT]
  exact fldExc_core hRig hp hcen hα hlabJ hJ hcanK θ hsR hnaR hi hf hind hout hconj hfix

theorem fldExc_twB2 (hG : FixGapTwB2) (hRig : GGLabelRigidInput) {S : Type} [Group S] [Finite S]
    (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel) (hT : labK.tag = .twB2)
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
  obtain ⟨hr0, hodd, h3⟩ : lab'.rank = 0 ∧ Odd lab'.n ∧ 3 ≤ lab'.n := by
    have h2 := hlam'.2
    rw [hT] at h2
    exact h2
  have hodd' : 2 * ((lab'.n - 1) / 2) + 1 = lab'.n := by
    obtain ⟨m, hm⟩ := hodd
    omega
  have ha : 1 ≤ (lab'.n - 1) / 2 := by omega
  have hconj := RecipeExcLang.ggRawFieldConj_suzuki (a := (lab'.n - 1) / 2) ha hK hp hp2
  have hfix : ∀ f' ∈ LargeEvenMatFieldImage (LargeEvenCenterMk (LargeEvenSzGroup ((lab'.n - 1) / 2) K)),
      orderOf f' = p → p ∣ lab'.n ∧
        (Group.IsSolvable ↥(ggFixSub f') ∨ ∃ (R₀ : Type) (_ : Group R₀) (lab'' : LargeEvenLabel),
          IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ LargeEvenInLambda2 lab'' ∧
          canonLabel lab'' = ⟨lab'.tag, lab'.rank, lab'.n / p⟩ ∧ GGHasLabel lab'' R₀ ∧
          Nonempty (ggFixDer f' ≃* R₀)) := by
    intro f' hf' hord'
    obtain ⟨hpn, hdisj⟩ := hG ((lab'.n - 1) / 2) p K ha hK hp hp2 f' hf' hord'
    rw [hodd'] at hpn
    refine ⟨hpn, ?_⟩
    rcases hdisj with hsolv | ⟨R₀, hR₀, lab'', hs0, hna0, hl, hc, hG', hθ⟩
    · exact Or.inl hsolv
    · refine Or.inr ⟨R₀, hR₀, lab'', hs0, hna0, hl, ?_, hG', hθ⟩
      rw [hc, hodd', hT, hr0]
  have hcanK : canonLabel lab' = lab' := by
    unfold canonLabel
    rw [hT]
  exact fldExc_core_or hRig hp hcen hα hlabJ hJ hcanK θ hsR hnaR hi hf hind hout hconj hfix

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10GField

end
