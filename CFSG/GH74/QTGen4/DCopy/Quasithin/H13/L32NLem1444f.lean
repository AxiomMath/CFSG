module

public import CFSG.Quasithin.H13.L32NLem1444f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1444e

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

open L1444 in

theorem lemma1444Two_of_inputs_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hRest : Lemma14323Rest_F4) (h14446 : Lemma1444Six_F4) : Lemma1444Two_F4 := by
  intro G _ _ T L V h hext h32 hG2 V₂ g hV₂ hgP hgH
  obtain ⟨D, Q₁, Q₂, S⟩ := exists_setup3_F4 h1332 h1334 h1222 h12213 h37 h38 h39 hRest h hext h32 hG2
    hV₂ hgP hgH
  have h6 := (h14446 G T L V h hext h32 hG2).2 V₂ g hV₂ hgP hgH
  have hQ : ∀ {y : G} (hyH : y ∈ l32nH T V), y ∈ pCoreOf 2 (l32nH T V) →
      (⟨y, hyH⟩ : ↥(l32nH T V)) ∈ CFSG.Open.pCore 2 ↥(l32nH T V) := by
    intro y hyH hy
    obtain ⟨y', hy', hy'y⟩ := hy
    have : y' = ⟨y, hyH⟩ := Subtype.ext hy'y
    rwa [← this]
  refine ⟨S.eq_E, S.card_Wg, ?_, ?_⟩
  · rintro _ ⟨⟨x, hxH⟩, hxW, rfl⟩ hx1 _ ⟨⟨k, hkH⟩, hkK, rfl⟩
    have hxW' : x ∈ CFSG.conjugate (l32nW T V V₂) g := hxW
    have hxQ : x ∉ pCoreOf 2 (l32nH T V) := fun h1 => hx1 (by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hQ hxH h1)
    obtain ⟨hx₁, hx₂⟩ := S.not_swap h6 hxW' hxQ
    have hinv := S.inv_of_normalizes hxW' hxQ hx₁ hx₂ (k := k) hkK
    have hcH : x * k * x⁻¹ * k ∈ l32nH T V :=
      (l32nH T V).mul_mem ((l32nH T V).mul_mem ((l32nH T V).mul_mem hxH hkH)
        ((l32nH T V).inv_mem hxH)) hkH
    have h1 : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(l32nH T V))
        ((⟨x, hxH⟩ : ↥(l32nH T V)) * ⟨k, hkH⟩ * ⟨x, hxH⟩⁻¹ * ⟨k, hkH⟩) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hQ hcH hinv
    rw [map_mul, map_mul, map_mul, map_inv] at h1
    exact eq_inv_of_mul_eq_one_left h1
  · intro x hxW hxQ
    obtain ⟨hx₁, hx₂⟩ := S.not_swap h6 hxW hxQ
    exact S.card_of_normalizes hxW hxQ hx₁ hx₂

end CFSG.Quasithin.H13
