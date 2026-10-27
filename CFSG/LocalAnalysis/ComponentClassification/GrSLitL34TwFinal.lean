module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwNormC3
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwMap
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwGood
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwCore
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwSmall
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwTrans
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwCentA
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwUU
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwBounds
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwProp41
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwProp42
public import Certificates.Certificate2022
public import Certificates.Certificate3007
public import Certificates.Certificate10005
public import Certificates.Certificate22200
public import Certificates.Certificate22201
public import Certificates.Certificate22202
public import Certificates.Certificate33001
public import Certificates.Certificate33002
public import Certificates.Certificate33101
public import Certificates.Certificate33102
public import Certificates.Certificate33201
public import Certificates.Certificate33209
public import Certificates.Certificate33211
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G] {a x : G} {J S' W K T : Subgroup G} {t : G}

theorem twMain (hMax : MaximalTwoComponentInput) (h : TwHyp G a x J S' W K T t) : False := by
  obtain ⟨ρ, hρ⟩ := exists_twModel h
  have hC : ConcX (imgT T (normalizer (W : Set G)) ρ) := finiteCore _ (goodX_of_twModel h hρ)
  obtain ⟨y, hy2, hyU, hya⟩ := exists_uu_commuting h hρ hC
  obtain ⟨g, m, hm2, hm, hgy⟩ := uu_fusion h hρ hC hy2 hyU
  rcases hm with hmA | hmD
  ·
    obtain ⟨haM, haA⟩ := isA_a h hρ
    have ha2 : a * a = 1 := by
      have hord : orderOf a = 2 := h.hset.2.1.1
      have h2 : a ^ 2 = 1 := by rw [← hord]; exact pow_orderOf_eq_one a
      rwa [pow_two] at h2
    have hm2' : (⟨a, haM⟩ : ↥(normalizer (W : Set G))) * ⟨a, haM⟩ = 1 := Subtype.ext ha2
    obtain ⟨k, hk⟩ := invol_conj_of_type h hρ hm2 hm2' (Or.inl ⟨hmA, haA⟩)
    refine prop42 hMax h hρ hC hy2 hyU hya (g * (k : G))⁻¹ ?_
    have h1 := congrArg Subtype.val hk
    have h3 : (k : G)⁻¹ * (m : G) * k = a := h1
    rw [inv_inv, ← h3, ← hgy]
    group
  · obtain ⟨d, hdT, hd2, hdD, hdZ⟩ := exists_d0 h hρ hC
    obtain ⟨k, hk⟩ := invol_conj_of_type h hρ hm2 hd2 (Or.inr (Or.inl ⟨hmD, hdD⟩))
    refine prop41 hMax h hρ hC hy2 hyU hya hdT hd2 hdD hdZ (g * (k : G)) ?_
    have h1 := congrArg Subtype.val hk
    have h3 : (k : G)⁻¹ * (m : G) * k = (d : G) := h1
    rw [← h3, ← hgy]
    group

end CFSG.ComponentClassification.GrSLit.L34Tw

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

theorem l34Lemma43TwistedInnerStepOfMax_holds :
    MaximalTwoComponentInput → L34Lemma43TwistedInnerStep := by
  intro hMax G _ _ a x J S A hset hcent hrun h3 hZ1 W hW hWodd hWB hNJ K hKM hKc hKL hsup hOK T
    hTsyl hST hTG t htT htK hr2 hQ hinv hu hno haKt hE2 hE3 hE4 hE5 hE6 hE7
  exact L34Tw.twMain hMax ⟨hset, hcent, hZ1, hW, hWodd, hNJ, hKM, hKc, hKL, hsup, hTsyl, hST, hTG,
    htT, htK, hr2, hQ, hinv, hu, haKt, hE4, hE5, hE6, hE7⟩

end CFSG.ComponentClassification.GrSLit
