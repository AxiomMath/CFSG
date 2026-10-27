module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnExcLabel
public import CFSG.HardMathSupport.Solomon.LocalBalance.ScpQuot
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Quasithin.Background.A3ComponentsAmbient

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)
open CFSG.StandardType (GGLabelRigidInput)

structure COrthLabelDict : Prop where
  lnA : ∀ {X : Type} [Group X], CFSG.Open.IsQuasisimple X → ∀ {n : ℕ}, 5 ≤ n →
    catalogIs (X ⧸ Subgroup.center X) (isLnA n 2) →
      ∃ lab : GLALabel, HasLabel X (fun l : GLALabel => l = lab) ∧
        canonLabel lab = (⟨.A, n - 1, 1⟩ : GLALabel)
  omM : ∀ {X : Type} [Group X], CFSG.Open.IsQuasisimple X → ∀ {n k : ℕ}, 4 ≤ n → 1 ≤ k →
    catalogIs (X ⧸ Subgroup.center X) (isOmMA n (2 ^ k)) →
      ∃ lab : GLALabel, HasLabel X (fun l : GLALabel => l = lab) ∧
        canonLabel lab = (⟨.twD, n, k⟩ : GLALabel)
  omP : ∀ {X : Type} [Group X], CFSG.Open.IsQuasisimple X → ∀ {n k : ℕ}, 3 ≤ n → 1 ≤ k → (n = 3 → 2 ≤ k) →
    catalogIs (X ⧸ Subgroup.center X) (isOmPA n (2 ^ k)) →
      ∃ lab : GLALabel, HasLabel X (fun l : GLALabel => l = lab) ∧
        canonLabel lab = (if n = 3 then (⟨.A, 3, k⟩ : GLALabel) else ⟨.D, n, k⟩)
  unA : ∀ {X : Type} [Group X], CFSG.Open.IsQuasisimple X → ∀ {m f : ℕ}, 2 ≤ m → 1 ≤ f →
    catalogIs (X ⧸ Subgroup.center X) (isUnA m (2 ^ f)) →
      ∃ lab : GLALabel, HasLabel X (fun l : GLALabel => l = lab) ∧
        canonLabel lab = (if m = 2 then (⟨.A, 1, f⟩ : GLALabel) else ⟨.twA, m - 1, f⟩)

variable (hD : COrthLabelDict) (hRig : GGLabelRigidInput) {X : Type} [Group X]
  (hq : CFSG.Open.IsQuasisimple X)
include hD hRig hq

theorem i167COrth_agree_plus {n k n' k' : ℕ} (hn : 3 ≤ n) (hk : 1 ≤ k) (hk3 : n = 3 → 2 ≤ k) (hn' : 3 ≤ n')
    (hk' : 1 ≤ k') (hk3' : n' = 3 → 2 ≤ k') (h : catalogIs (X ⧸ Subgroup.center X) (isOmPA n (2 ^ k)))
    (h' : catalogIs (X ⧸ Subgroup.center X) (isOmPA n' (2 ^ k'))) : n = n' ∧ k = k' := by
  obtain ⟨l, hl, e⟩ := hD.omP hq hn hk hk3 h
  obtain ⟨l', hl', e'⟩ := hD.omP hq hn' hk' hk3' h'
  have := Y10GInnExcLabel.canonLabel_eq_of_hasLabel hRig hl hl'
  rw [e, e'] at this
  split_ifs at this <;> simp at this <;> omega

theorem i167COrth_agree_minus {n k n' k' : ℕ} (hn : 4 ≤ n) (hk : 1 ≤ k) (hn' : 4 ≤ n') (hk' : 1 ≤ k')
    (h : catalogIs (X ⧸ Subgroup.center X) (isOmMA n (2 ^ k)))
    (h' : catalogIs (X ⧸ Subgroup.center X) (isOmMA n' (2 ^ k'))) : n = n' ∧ k = k' := by
  obtain ⟨l, hl, e⟩ := hD.omM hq hn hk h
  obtain ⟨l', hl', e'⟩ := hD.omM hq hn' hk' h'
  have := Y10GInnExcLabel.canonLabel_eq_of_hasLabel hRig hl hl'
  rw [e, e'] at this
  simpa using this

theorem i167COrth_clash_plus_minus {n k n' k' : ℕ} (hn : 3 ≤ n) (hk : 1 ≤ k) (hk3 : n = 3 → 2 ≤ k) (hn' : 4 ≤ n')
    (hk' : 1 ≤ k') (h : catalogIs (X ⧸ Subgroup.center X) (isOmPA n (2 ^ k)))
    (h' : catalogIs (X ⧸ Subgroup.center X) (isOmMA n' (2 ^ k'))) : False := by
  obtain ⟨l, hl, e⟩ := hD.omP hq hn hk hk3 h
  obtain ⟨l', hl', e'⟩ := hD.omM hq hn' hk' h'
  have := Y10GInnExcLabel.canonLabel_eq_of_hasLabel hRig hl hl'
  rw [e, e'] at this
  split_ifs at this <;> simp at this

theorem i167COrth_clash_lin_plus {n n' k' : ℕ} (hn : 5 ≤ n) (hn' : 3 ≤ n') (hk' : 1 ≤ k') (hk3' : n' = 3 → 2 ≤ k')
    (h : catalogIs (X ⧸ Subgroup.center X) (isLnA n 2))
    (h' : catalogIs (X ⧸ Subgroup.center X) (isOmPA n' (2 ^ k'))) : False := by
  obtain ⟨l, hl, e⟩ := hD.lnA hq hn h
  obtain ⟨l', hl', e'⟩ := hD.omP hq hn' hk' hk3' h'
  have := Y10GInnExcLabel.canonLabel_eq_of_hasLabel hRig hl hl'
  rw [e, e'] at this
  split_ifs at this <;> simp at this <;> omega

theorem i167COrth_clash_lin_minus {n n' k' : ℕ} (hn : 5 ≤ n) (hn' : 4 ≤ n') (hk' : 1 ≤ k')
    (h : catalogIs (X ⧸ Subgroup.center X) (isLnA n 2))
    (h' : catalogIs (X ⧸ Subgroup.center X) (isOmMA n' (2 ^ k'))) : False := by
  obtain ⟨l, hl, e⟩ := hD.lnA hq hn h
  obtain ⟨l', hl', e'⟩ := hD.omM hq hn' hk' h'
  have := Y10GInnExcLabel.canonLabel_eq_of_hasLabel hRig hl hl'
  rw [e, e'] at this
  simp at this

theorem i167COrth_clash_un_lin {m f n : ℕ} (hm : 2 ≤ m) (hf : 1 ≤ f) (hn : 5 ≤ n)
    (h : catalogIs (X ⧸ Subgroup.center X) (isUnA m (2 ^ f)))
    (h' : catalogIs (X ⧸ Subgroup.center X) (isLnA n 2)) : False := by
  obtain ⟨l, hl, e⟩ := hD.unA hq hm hf h
  obtain ⟨l', hl', e'⟩ := hD.lnA hq hn h'
  have := Y10GInnExcLabel.canonLabel_eq_of_hasLabel hRig hl hl'
  rw [e, e'] at this
  split_ifs at this <;> simp at this <;> omega

theorem i167COrth_clash_un_minus {m f n k : ℕ} (hm : 2 ≤ m) (hf : 1 ≤ f) (hn : 4 ≤ n) (hk : 1 ≤ k)
    (h : catalogIs (X ⧸ Subgroup.center X) (isUnA m (2 ^ f)))
    (h' : catalogIs (X ⧸ Subgroup.center X) (isOmMA n (2 ^ k))) : False := by
  obtain ⟨l, hl, e⟩ := hD.unA hq hm hf h
  obtain ⟨l', hl', e'⟩ := hD.omM hq hn hk h'
  have := Y10GInnExcLabel.canonLabel_eq_of_hasLabel hRig hl hl'
  rw [e, e'] at this
  split_ifs at this <;> simp at this

theorem i167COrth_clash_un_plus {m f n k : ℕ} (hm : 2 ≤ m) (hf : 1 ≤ f) (hn : 3 ≤ n) (hk : 1 ≤ k)
    (hk3 : n = 3 → 2 ≤ k) (h : catalogIs (X ⧸ Subgroup.center X) (isUnA m (2 ^ f)))
    (h' : catalogIs (X ⧸ Subgroup.center X) (isOmPA n (2 ^ k))) : False := by
  obtain ⟨l, hl, e⟩ := hD.unA hq hm hf h
  obtain ⟨l', hl', e'⟩ := hD.omP hq hn hk hk3 h'
  have := Y10GInnExcLabel.canonLabel_eq_of_hasLabel hRig hl hl'
  rw [e, e'] at this
  split_ifs at this <;> simp at this <;> omega

end CFSG.LocalAnalysis.GLTheoremA.I167

end
