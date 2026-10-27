module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcOrd
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevRecipe
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangChev
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcCore
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S9.InputsClosing

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.Assembly CFSG.StandardType CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.YS09Field
open CFSG.LocalAnalysis.GLTheoremA

theorem fldExc_F4
    (hRig : GGLabelRigidInput) {S : Type} [Group S] [Finite S] (p : ℕ) (α : MulAut S)
    (J : Subgroup S) (labK labJ : GLALabel) (hT : labK.tag = .F4) (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : Subgroup.center S = ⊥) (hfld : FieldKind S labK α) (hα : α ^ p = 1)
    (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ)) (hJ : GLAPComponent p (fixSubgroup α) J) :
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
  have hn : 1 ≤ lab'.n := hlam'.1
  have hr : lab'.rank = 0 := by
    have h2 := hlam'.2
    rw [hT] at h2
    exact h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hK
  have hconj := RecipeExcLang.ggRawFieldConj_chev (τ := .F4) (ℓ := 2) (f := lab'.n) (p := p) hn hK
    hp (RecipeExcLang.innerFieldTrivial_F4 hn hK)
  have hfix : ∀ f' ∈ LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenChevH LargeEvenCartanF4 K false),
      orderOf f' = p → p ∣ lab'.n ∧ ∃ (R₀ : Type) (_ : Group R₀) (lab'' : LargeEvenLabel),
        IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ LargeEvenInLambda2 lab'' ∧
        canonLabel lab'' = ⟨lab'.tag, lab'.rank, lab'.n / p⟩ ∧ GGHasLabel lab'' R₀ ∧
        Nonempty (ggFixDer f' ≃* R₀) := by
    intro f' hf' hord'
    have hpn : p ∣ lab'.n :=
      dvd_of_chevField_order hn hK hp (LargeEvenChevH LargeEvenCartanF4 K false)
        (fun σ h hh => chevH_stable LargeEvenCartanF4 K false σ h hh) hf' hord'
    obtain ⟨K₀, hK₀F, hK₀fin, hK₀, hQ₀⟩ :=
      chev_fixStd (τ := .F4) (Or.inl rfl) hn hK hp.pos hf' hord'
    obtain ⟨hs0, hna0, θ₀, -⟩ := hQ₀
    have hm : 1 ≤ lab'.n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
    refine ⟨hpn, LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 K₀ false), inferInstance,
      ⟨.F4, lab'.rank, lab'.n / p⟩, hs0, hna0, ?_, ?_, ?_, ⟨θ₀⟩⟩
    · unfold LargeEvenInLambda2
      exact ⟨hm, hr⟩
    · rw [hT]
      rfl
    · unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum
      exact ⟨K₀, hK₀F, hK₀fin, hK₀, ⟨MulEquiv.refl _⟩⟩
  have hcanK : canonLabel lab' = lab' := by
    unfold canonLabel
    rw [hT]
  exact fldExc_core hRig hp hcen hα hlabJ hJ hcanK θ hsR hnaR hi hf hind hout hconj hfix


theorem fldExc_E7
    (hRig : GGLabelRigidInput) {S : Type} [Group S] [Finite S] (p : ℕ) (α : MulAut S)
    (J : Subgroup S) (labK labJ : GLALabel) (hT : labK.tag = .E7) (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : Subgroup.center S = ⊥) (hfld : FieldKind S labK α) (hα : α ^ p = 1)
    (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ)) (hJ : GLAPComponent p (fixSubgroup α) J) :
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
  have hn : 1 ≤ lab'.n := hlam'.1
  have hr : lab'.rank = 0 := by
    have h2 := hlam'.2
    rw [hT] at h2
    exact h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hK
  have hconj := RecipeExcLang.ggRawFieldConj_chev (τ := .E7) (ℓ := 2) (f := lab'.n) (p := p) hn hK
    hp (RecipeExcLang.innerFieldTrivial_E7_E8 (τ := .E7) hn hK (Or.inl rfl))
  have hfix : ∀ f' ∈ LargeEvenChevFieldImage (LargeEvenCartanE 7) K (LargeEvenChevH (LargeEvenCartanE 7) K false),
      orderOf f' = p → p ∣ lab'.n ∧ ∃ (R₀ : Type) (_ : Group R₀) (lab'' : LargeEvenLabel),
        IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ LargeEvenInLambda2 lab'' ∧
        canonLabel lab'' = ⟨lab'.tag, lab'.rank, lab'.n / p⟩ ∧ GGHasLabel lab'' R₀ ∧
        Nonempty (ggFixDer f' ≃* R₀) := by
    intro f' hf' hord'
    have hpn : p ∣ lab'.n :=
      dvd_of_chevField_order hn hK hp (LargeEvenChevH (LargeEvenCartanE 7) K false)
        (fun σ h hh => chevH_stable (LargeEvenCartanE 7) K false σ h hh) hf' hord'
    obtain ⟨K₀, hK₀F, hK₀fin, hK₀, hQ₀⟩ :=
      chev_fixStd (τ := .E7) (Or.inr (Or.inl rfl)) hn hK hp.pos hf' hord'
    obtain ⟨hs0, hna0, θ₀, -⟩ := hQ₀
    have hm : 1 ≤ lab'.n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
    refine ⟨hpn, LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K₀ false), inferInstance,
      ⟨.E7, lab'.rank, lab'.n / p⟩, hs0, hna0, ?_, ?_, ?_, ⟨θ₀⟩⟩
    · unfold LargeEvenInLambda2
      exact ⟨hm, hr⟩
    · rw [hT]
      rfl
    · unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum
      exact ⟨K₀, hK₀F, hK₀fin, hK₀, ⟨MulEquiv.refl _⟩⟩
  have hcanK : canonLabel lab' = lab' := by
    unfold canonLabel
    rw [hT]
  exact fldExc_core hRig hp hcen hα hlabJ hJ hcanK θ hsR hnaR hi hf hind hout hconj hfix


theorem fldExc_E8
    (hRig : GGLabelRigidInput) {S : Type} [Group S] [Finite S] (p : ℕ) (α : MulAut S)
    (J : Subgroup S) (labK labJ : GLALabel) (hT : labK.tag = .E8) (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : Subgroup.center S = ⊥) (hfld : FieldKind S labK α) (hα : α ^ p = 1)
    (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ)) (hJ : GLAPComponent p (fixSubgroup α) J) :
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
  have hn : 1 ≤ lab'.n := hlam'.1
  have hr : lab'.rank = 0 := by
    have h2 := hlam'.2
    rw [hT] at h2
    exact h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hK
  have hconj := RecipeExcLang.ggRawFieldConj_chev (τ := .E8) (ℓ := 2) (f := lab'.n) (p := p) hn hK
    hp (RecipeExcLang.innerFieldTrivial_E7_E8 (τ := .E8) hn hK (Or.inr rfl))
  have hfix : ∀ f' ∈ LargeEvenChevFieldImage (LargeEvenCartanE 8) K (LargeEvenChevH (LargeEvenCartanE 8) K false),
      orderOf f' = p → p ∣ lab'.n ∧ ∃ (R₀ : Type) (_ : Group R₀) (lab'' : LargeEvenLabel),
        IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ LargeEvenInLambda2 lab'' ∧
        canonLabel lab'' = ⟨lab'.tag, lab'.rank, lab'.n / p⟩ ∧ GGHasLabel lab'' R₀ ∧
        Nonempty (ggFixDer f' ≃* R₀) := by
    intro f' hf' hord'
    have hpn : p ∣ lab'.n :=
      dvd_of_chevField_order hn hK hp (LargeEvenChevH (LargeEvenCartanE 8) K false)
        (fun σ h hh => chevH_stable (LargeEvenCartanE 8) K false σ h hh) hf' hord'
    obtain ⟨K₀, hK₀F, hK₀fin, hK₀, hQ₀⟩ :=
      chev_fixStd (τ := .E8) (Or.inr (Or.inr rfl)) hn hK hp.pos hf' hord'
    obtain ⟨hs0, hna0, θ₀, -⟩ := hQ₀
    have hm : 1 ≤ lab'.n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
    refine ⟨hpn, LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 8) K₀ false), inferInstance,
      ⟨.E8, lab'.rank, lab'.n / p⟩, hs0, hna0, ?_, ?_, ?_, ⟨θ₀⟩⟩
    · unfold LargeEvenInLambda2
      exact ⟨hm, hr⟩
    · rw [hT]
      rfl
    · unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum
      exact ⟨K₀, hK₀F, hK₀fin, hK₀, ⟨MulEquiv.refl _⟩⟩
  have hcanK : canonLabel lab' = lab' := by
    unfold canonLabel
    rw [hT]
  exact fldExc_core hRig hp hcen hα hlabJ hJ hcanK θ hsR hnaR hi hf hind hout hconj hfix

end CFSG.LocalAnalysis.GLTheoremA.Y10GField

end
