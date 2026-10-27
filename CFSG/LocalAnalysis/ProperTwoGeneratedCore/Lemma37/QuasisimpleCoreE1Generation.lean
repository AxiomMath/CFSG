module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1Fusion

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

section Criterion

variable {X : Type} [Group X] {H : Subgroup X} {w₁ w₂ : X}

theorem mem_of_conj_eq_conj {w t g h₁ h₂ : X} (hw : Subgroup.centralizer {w} ≤ H) (hh₁ : h₁ ∈ H)
    (hh₂ : h₂ ∈ H) (e₁ : h₁ * w * h₁⁻¹ = t) (e₂ : h₂ * w * h₂⁻¹ = g⁻¹ * t * g) : g ∈ H := by
  have hk : h₂⁻¹ * g⁻¹ * h₁ ∈ Subgroup.centralizer {w} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e₃ : g⁻¹ * (h₁ * w * h₁⁻¹) * g = h₂ * w * h₂⁻¹ := by rw [e₁, e₂]
    calc h₂⁻¹ * g⁻¹ * h₁ * w = h₂⁻¹ * (g⁻¹ * (h₁ * w * h₁⁻¹) * g) * (g⁻¹ * h₁) := by group
      _ = w * (h₂⁻¹ * g⁻¹ * h₁) := by rw [e₃]; group
  have hg := H.mul_mem (H.mul_mem hh₂ (hw hk)) (H.inv_mem hh₁)
  rw [show h₂ * (h₂⁻¹ * g⁻¹ * h₁) * h₁⁻¹ = g⁻¹ by group] at hg
  simpa using H.inv_mem hg

theorem mem_of_conj_mem_of_forall_conj (hw : ¬ IsConj w₁ w₂)
    (hw₁ : Subgroup.centralizer {w₁} ≤ H) (hw₂ : Subgroup.centralizer {w₂} ≤ H)
    (hcls : ∀ t ∈ H, CFSG.BenderSuzuki.PFAppendixIII.IsInvolution t →
      (∃ h ∈ H, h * w₁ * h⁻¹ = t) ∨ ∃ h ∈ H, h * w₂ * h⁻¹ = t)
    {t g : X} (htH : t ∈ H) (ht : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution t)
    (htg : g⁻¹ * t * g ∈ H) : g ∈ H := by
  have ht' : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution (g⁻¹ * t * g) :=
    CFSG.BenderSuzuki.PFAppendixIII.isInvolution_rightConjugateElem ht
  have hconj : ∀ {a b h₁ h₂ : X}, h₁ * a * h₁⁻¹ = t → h₂ * b * h₂⁻¹ = g⁻¹ * t * g → IsConj a b :=
    fun {a b h₁ h₂} e₁ e₂ => isConj_iff.mpr ⟨h₂⁻¹ * g⁻¹ * h₁, by
      rw [show h₂⁻¹ * g⁻¹ * h₁ * a * (h₂⁻¹ * g⁻¹ * h₁)⁻¹ =
        h₂⁻¹ * (g⁻¹ * (h₁ * a * h₁⁻¹) * g) * h₂ by group, e₁, ← e₂]
      group⟩
  rcases hcls t htH ht with ⟨h₁, hh₁, e₁⟩ | ⟨h₁, hh₁, e₁⟩ <;>
    rcases hcls _ htg ht' with ⟨h₂, hh₂, e₂⟩ | ⟨h₂, hh₂, e₂⟩
  · exact mem_of_conj_eq_conj hw₁ hh₁ hh₂ e₁ e₂
  · exact absurd (hconj e₁ e₂) hw
  · exact absurd (hconj e₁ e₂).symm hw
  · exact mem_of_conj_eq_conj hw₂ hh₁ hh₂ e₁ e₂

theorem isStronglyEmbedded_of_forall_conj [Finite X] (hH : H ≠ ⊤) (hw : ¬ IsConj w₁ w₂)
    (hw₁ : Subgroup.centralizer {w₁} ≤ H) (hw₂ : Subgroup.centralizer {w₂} ≤ H)
    (hinv : ∃ t ∈ H, CFSG.BenderSuzuki.PFAppendixIII.IsInvolution t)
    (hcls : ∀ t ∈ H, CFSG.BenderSuzuki.PFAppendixIII.IsInvolution t →
      (∃ h ∈ H, h * w₁ * h⁻¹ = t) ∨ ∃ h ∈ H, h * w₂ * h⁻¹ = t) :
    CFSG.BenderSuzuki.IsStronglyEmbedded H := by
  refine ⟨hH, hinv, fun {g} hg {x} hxH hxg hx => hg ?_⟩
  obtain ⟨t, htH, rfl⟩ := Subgroup.mem_map.mp hxg
  have ht : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution t := by
    have h := CFSG.BenderSuzuki.PFAppendixIII.isInvolution_rightConjugateElem (g := g⁻¹) hx
    convert h using 1
    simp only [CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group
  refine mem_of_conj_mem_of_forall_conj hw hw₁ hw₂ hcls htH ht ?_
  convert hxH using 1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]

end Criterion

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem exists_conj_of_mem_typeD (htype : ∀ s ∈ (S : Subgroup J).map
      (QuotientGroup.mk' (Subgroup.center J)), s ∉ (partCSylow T).map
        (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
          CaseC3.Genuine (Subgroup.center J) s)
    {H : Subgroup (J ⧸ Subgroup.center J)}
    (hHz : Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40} ≤ H)
    (hHu : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)} ≤ H) {t : J ⧸ Subgroup.center J}
    (htH : t ∈ H) (htt : t * t = 1) (ht1 : t ≠ 1) :
    (CaseC3.Genuine (Subgroup.center J) t →
      ∃ h ∈ H, h * caseC3Word (Subgroup.center J) u m y x 40 * h⁻¹ = t) ∧
    (¬ CaseC3.Genuine (Subgroup.center J) t →
      ∃ h ∈ H, h * (u : J ⧸ Subgroup.center J) * h⁻¹ = t) := by
  obtain ⟨k, hk, v, hvv, hv0, hkt⟩ :=
    d.exists_conj_caseC3Word (d.map_le_centralizer_forty.trans hHz) htH htt ht1
  have hcls := d.exists_conj_of_typeD htype hHz hHu hvv hv0
  have hgen : CaseC3.Genuine (Subgroup.center J) (caseC3Word (Subgroup.center J) u m y x v) ↔
      CaseC3.Genuine (Subgroup.center J) t := by
    rw [← hkt]
    refine ⟨fun h' => ?_, fun h' => ?_⟩
    · have h'' := CaseC3.genuine_conj _ h' k
      rwa [show k⁻¹ * (k * t * k⁻¹) * k = t by group] at h''
    · have h'' := CaseC3.genuine_conj _ h' k⁻¹
      rwa [inv_inv] at h''
  have hback : ∀ {w : J ⧸ Subgroup.center J}, (∃ h ∈ H, h * w * h⁻¹ =
      caseC3Word (Subgroup.center J) u m y x v) → ∃ h ∈ H, h * w * h⁻¹ = t := by
    rintro w ⟨h, hh, hhv⟩
    refine ⟨k⁻¹ * h, H.mul_mem (H.inv_mem hk) hh, ?_⟩
    rw [show k⁻¹ * h * w * (k⁻¹ * h)⁻¹ = k⁻¹ * (h * w * h⁻¹) * k by group, hhv, ← hkt]
    group
  exact ⟨fun hg => hback (hcls.1 (hgen.mpr hg)), fun hg => hback (hcls.2 (mt hgen.mp hg))⟩

theorem centralizer_sup_centralizer_eq_top (htype : ∀ s ∈ (S : Subgroup J).map
      (QuotientGroup.mk' (Subgroup.center J)), s ∉ (partCSylow T).map
        (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
          CaseC3.Genuine (Subgroup.center J) s) :
    Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40} ⊔
      Subgroup.centralizer {(u : J ⧸ Subgroup.center J)} = ⊤ := by
  have hb := d.caseC3BCD
  by_contra hne
  have hHz := le_sup_left (a := Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40})
    (b := Subgroup.centralizer {(u : J ⧸ Subgroup.center J)})
  have hHu := le_sup_right (a := Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40})
    (b := Subgroup.centralizer {(u : J ⧸ Subgroup.center J)})
  have hz2 : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution
      (caseC3Word (Subgroup.center J) u m y x 40) :=
    ⟨by rw [Ne, hb.caseC3Word_eq_one_iff]; decide, by
      rw [pow_two, hb.caseC3Word_mul, c3Mul_forty_forty, CaseC3BCD.caseC3Word_zero]⟩
  have hu2 : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution (u : J ⧸ Subgroup.center J) := by
    rw [← CaseC3BCD.caseC3Word_thirtytwo (Z := Subgroup.center J) (m := m) (y := y) (x := x)]
    exact ⟨by rw [Ne, hb.caseC3Word_eq_one_iff]; decide, by
      rw [pow_two, hb.caseC3Word_mul, c3_thirtytwo.1, CaseC3BCD.caseC3Word_zero]⟩
  have hSE := isStronglyEmbedded_of_forall_conj hne d.not_isConj_forty_self hHz hHu
    ⟨_, hHz (Subgroup.mem_centralizer_singleton_iff.mpr rfl), hz2⟩ fun t htH ht => by
      have htt : t * t = 1 := by rw [← pow_two]; exact ht.2
      by_cases hg : CaseC3.Genuine (Subgroup.center J) t
      · exact Or.inl ((d.exists_conj_of_mem_typeD htype hHz hHu htH htt ht.1).1 hg)
      · exact Or.inr ((d.exists_conj_of_mem_typeD htype hHz hHu htH htt ht.1).2 hg)
  obtain ⟨g, hg⟩ := hSE.involutions_conjugate hz2 hu2
  refine d.not_isConj_forty_self (isConj_iff.mpr ⟨g⁻¹, ?_⟩)
  rw [inv_inv]
  exact hg

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
