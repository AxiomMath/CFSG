module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCA11O
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCA11P
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNFOrbShape

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem signalizerCaseOneConjugateOutsideAltRInput_holds
    (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion) :
    SignalizerCaseOneConjugateOutsideAltRInput := by
  intro X _ _ _ t J n e E D S hn hW M hMH hMpc hJM hHN hsup θ ρ hρ Q hQK hQ2 hQcard htQ hA hNT a g
    ha hgH hs hsNQ hσ2 hσ1 x hxM hxo hx2 hx4 hxf hx' hx'M hs2 hx'5 y hyM hy2 hyx' hρy hyo hko hCk _
  have hodd : Odd n := S.pair.2.1
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply hσ1
    have h1 : (⟨g⁻¹ * 1 * g, hHN hs⟩ : ↥(normalizer (M : Set X))) = 1 :=
      Subtype.ext (show g⁻¹ * 1 * g = 1 by group)
    rw [h1, map_one]
  have hσsq : ρ ⟨g⁻¹ * a * g, hHN hs⟩ ^ 2 = 1 := by rw [sq]; exact hσ2
  obtain ⟨q, hq⟩ := Perm.two_dvd_card_support hσsq
  have hσc : (ρ ⟨g⁻¹ * a * g, hHN hs⟩).support.card ≤ n := by
    have := Finset.card_le_univ (ρ ⟨g⁻¹ * a * g, hHN hs⟩).support
    rwa [Fintype.card_fin] at this
  have hσpos : 0 < (ρ ⟨g⁻¹ * a * g, hHN hs⟩).support.card :=
    Finset.card_pos.mpr (Finset.nonempty_of_ne_empty fun h => hσ1 (Perm.support_eq_empty_iff.mp h))
  obtain ⟨k, hk⟩ := hodd
  by_cases h5f : 5 ≤ n - (ρ ⟨g⁻¹ * a * g, hHN hs⟩).support.card ∧
      ((ρ ⟨g⁻¹ * a * g, hHN hs⟩).support.card < 6 →
        9 ≤ n - (ρ ⟨g⁻¹ * a * g, hHN hs⟩).support.card)
  · exact S.false_of_five_fix hn h33 h35 hT13 hML hSch hMH hMpc hHN hsup hρ hQK hQ2 hA hNT ha ha1
      hs hs2 hxM hxo hx2 hx4 hxf hx' hx'5 h5f.1 h5f.2
  by_cases h114 : n = 11 ∧ (ρ ⟨g⁻¹ * a * g, hHN hs⟩).support.card = 4
  · obtain ⟨h11, h4⟩ := h114
    subst h11
    exact S.false_of_conj_four_eleven h33 h35 hT13 hML hSch hPump hN1 hMH hMpc hJM hHN hsup hρ
      hQK hQ2 hA hNT ha hs hs2 h4
  by_cases h118 : n = 11 ∧ (ρ ⟨g⁻¹ * a * g, hHN hs⟩).support.card = 8
  · obtain ⟨h11, h8⟩ := h118
    subst h11
    exact S.false_of_conj_eight_eleven h33 h35 hT13 hML hSch hPump hN1 hMH hMpc hJM hHN hsup hρ
      hA hs hs2 h8 hxM hxo hx2 hx4 hxf hy2 hyx' hyo hko hCk
  have hCa : centralizer ({a} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
    have hNa := hNT _ (zpowers_le.mpr ha) (fun h => ha1 (zpowers_eq_bot.mp h))
    intro z hz
    apply hNa
    apply Subgroup.centralizer_le_normalizer
    rw [centralizer_zpowers_eq']
    exact hz
  exact false_of_four_fix_orbit hρ hn ⟨k, hk⟩ (hCa.trans hHN) (hHN hs) hs2 hxM hxo hx2 hxf
    (hHN hx') hx'5 (by omega) (by omega)

end CFSG.ComponentClassification.SolMax
