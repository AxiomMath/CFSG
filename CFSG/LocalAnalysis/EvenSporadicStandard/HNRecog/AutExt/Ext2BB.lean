module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.EtaGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.ExtendCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.IsoGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.TypingA

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'}

theorem exists_iso_2BB (h : F5Std a z) (h' : F5Std a' z') {α : G → G'}
    (hα : IsIsoOn (Gx a) (Gx a') α) {w : G} (hw : w ∈ orb2BB a z a) :
    ∃ γ : G → G', IsIsoOn (Gx w) (Gx (α w)) γ ∧ ∀ x ∈ Gxy a w, γ x = α x := by
  have hαa : α a = a' := iso_apply_self h h' hα
  have hw' : α w ∈ orb2BB a' z' a' := typing_2BB h h' hα hw
  have haw : a * w = w * a :=
    h.mul_comm (Or.inl (IsConj.refl a)) (Or.inr hw.1) (Or.inr hw.2)
  have hat : a ∈ Gx w := mem_Gx.mpr haw.symm
  have hwx : IsConj z (w * a) := haw ▸ hw.2
  have ha'w' : a' * α w = α w * a' :=
    h'.mul_comm (Or.inl (IsConj.refl a')) (Or.inr hw'.1) (Or.inr hw'.2)
  have hwx' : IsConj z' (α w * a') := ha'w' ▸ hw'.2
  obtain ⟨γ, hγ, hγa⟩ :=
    exists_iso_Gz_fix h h' (w := w) (x := a) (w' := α w) (x' := a') hw.1
      (IsConj.refl a) hwx hw'.1 (IsConj.refl a') hwx'
  have hF : F5Std a w := h.of_isConj (IsConj.refl a) hw.1
  have hF' : F5Std a' (α w) := h'.of_isConj (IsConj.refl a') hw'.1
  have hγw : γ w = α w := iso_apply_self_Gz hF hF' hγ
  have hdec : ∀ y ∈ Gxy a w, ∃ u ∈ Subgroup.closure ({a, w} : Set G),
      ∃ n ∈ derivedOf (Gxy a w), y = u * n := by
    intro y hy
    rw [← Gxy_comm w a] at hy
    obtain ⟨n, hn, hyn⟩ := decomp_Y h hw.1 (IsConj.refl a) hwx y hy
    rw [Gxy_comm w a] at hn
    have haS : a ∈ Subgroup.closure ({a, w} : Set G) := Subgroup.subset_closure (by simp)
    have hwS : w ∈ Subgroup.closure ({a, w} : Set G) := Subgroup.subset_closure (by simp)
    have hawS : w * a ∈ Subgroup.closure ({a, w} : Set G) :=
      (Subgroup.closure ({a, w} : Set G)).mul_mem hwS haS
    rcases hyn with hyn | hyn | hyn | hyn
    · exact ⟨1, Subgroup.one_mem _, n, hn, by rw [hyn, one_mul]⟩
    · exact ⟨w, hwS, n, hn, by rw [hyn]⟩
    · exact ⟨a, haS, n, hn, by rw [hyn]⟩
    · exact ⟨w * a, hawS, n, hn, by rw [hyn]⟩
  obtain ⟨η, hη, hηw, hηa, hηout⟩ := exists_eta_Gz h hw.1 (IsConj.refl a) hwx
  rw [Gxy_comm w a] at hηout
  have hout : ∀ ψ₁ ψ₂ : G → G,
      IsIsoOn (derivedOf (Gxy a w)) (derivedOf (Gxy a w)) ψ₁ →
      IsIsoOn (derivedOf (Gxy a w)) (derivedOf (Gxy a w)) ψ₂ →
      (¬ ∃ g ∈ derivedOf (Gxy a w), ∀ x ∈ derivedOf (Gxy a w), ψ₁ x = g * x * g⁻¹) →
      (¬ ∃ g ∈ derivedOf (Gxy a w), ∀ x ∈ derivedOf (Gxy a w), ψ₂ x = g * x * g⁻¹) →
      ∃ g ∈ derivedOf (Gxy a w), ∀ x ∈ derivedOf (Gxy a w), ψ₁ (ψ₂ x) = g * x * g⁻¹ := by
    intro ψ₁ ψ₂ h₁ h₂ n₁ n₂
    rw [← Gxy_comm w a] at h₁ h₂ n₁ n₂ ⊢
    exact out_Y h hw.1 (IsConj.refl a) hwx h₁ h₂ n₁ n₂
  exact extend_iso_cent (a := a) (t := w) (a' := a') (α := α) (β := γ) (η := η)
    hα hαa hat hγ hγa hγw hdec hη hηa hηw hηout hout

end CFSG.EvenSporadicStandard.HNRecog.Section4
