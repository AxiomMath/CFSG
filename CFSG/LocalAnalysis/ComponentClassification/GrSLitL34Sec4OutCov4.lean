module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4OutCov

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
open GrS4.OutCov

theorem l34OuterFixedInvolutionFact :
    L34OuterFixedInvolutionFact := by
  intro E _ q l hQ hkc hk4 ρ hρ β hβ Y hY2 hYR hYN hYρ hρY hYF
  obtain ⟨hI, hcert⟩ := outCov_parts
  obtain ⟨κ, hκK, hκ⟩ := exists_kappa hQ hkc hk4
  obtain ⟨hρR, hρN, ρT, hρT, hρrep⟩ := rho_spec hρ
  obtain ⟨i₀, hi₀, t₀, ht₀, hρdec, hinv, hβE⟩ := exists_betaE hQ hI hκ hρR hρN hβ
  have hρ0 : TabRep (rT t₀ i₀) ρ := hρdec ▸ tabRep_rT hi₀
  have hc4 := (hcert κ (kGensB_eq ▸ hκK) ρT hρT t₀ ht₀ i₀ hi₀ (hρ0.tab_eq hρrep) hinv).2.1
  simp only [c4Case, Bool.and_eq_true] at hc4
  obtain ⟨hA, hB⟩ := hc4
  set Ft := ftabs κ t₀ i₀ with hFt
  set EB := (enumBFS 42 (Ft ++ [rT t₀ i₀]).toArray 64).tabs with hEB
  set L := liftC κ (rT t₀ i₀) with hL
  set W := invsE κ with hW
  have hFY : ∀ s ∈ Ft, ∃ g ∈ Y, TabRep s g := by
    intro s hs
    simp only [hFt, ftabs, List.mem_map] at hs
    obtain ⟨k, hk, rfl⟩ := hs
    simp only [fixK, List.mem_filter, List.mem_range, List.any_eq_true] at hk
    obtain ⟨hk64, a, -, b, -, hab⟩ := hk
    have hx : ((k, a, b) : El).1 < 64 := hk64
    obtain ⟨hβx, hlt⟩ := hβE (k, a, b) hx
    have hfix : β (nfE l (k, a, b)) = nfE l (k, a, b) := hβx.trans ((eqE_iff hQ hκ hlt hx).1 hab)
    have hmem := hYF (nfE l (k, a, b)) (by rw [q_nfE hQ hx]; exact tg_mem_T0 _ hk64) hfix
    rw [q_nfE hQ hx] at hmem
    exact ⟨_, hmem, tabRep_wordTab _⟩
  have hlift : ∀ r ∈ Y, ∀ β' : E ≃* E, (∀ e, q (β' e) = r * q e * r⁻¹) →
      ∃ t < 64, ∃ j < 36, TabRep (rT t j) r ∧ (t, j) ∈ L ∧
        ∀ x : El, x.1 < 64 → β' (nfE l x) = nfE l (betaE t j x) ∧ (betaE t j x).1 < 64 := by
    intro r hr β' hβ'
    obtain ⟨j, hj, t, ht, hrdec, hinvj, hβ'E⟩ := exists_betaE hQ hI hκ (hYR hr) (hYN r hr) hβ'
    have hr0 : TabRep (rT t j) r := hrdec ▸ tabRep_rT hj
    refine ⟨t, ht, j, hj, hr0, ?_, hβ'E⟩
    simp only [hL, liftC, List.mem_filter, List.mem_flatMap, List.mem_map, List.mem_range,
      Bool.and_eq_true]
    exact ⟨⟨t, ht, j, hj, rfl⟩, hinvj, (commB_iff hr0 hρ0).2 (hYρ r hr)⟩
  have hwprop : ∀ w ∈ W, w.1 < 64 ∧ q (nfE l w) ∈ T0 ∧ nfE l w * nfE l w = 1 ∧
      q (nfE l w) ≠ 1 := by
    intro w hw
    simp only [hW, invsE, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne]
      at hw
    obtain ⟨hwe, hww, hw0⟩ := hw
    have hwlt := lt_of_mem_els hwe
    refine ⟨hwlt, by rw [q_nfE hQ hwlt]; exact tg_mem_T0 _ hwlt, ?_,
      by rw [q_nfE hQ hwlt]; exact wordPerm_tg_ne_one hwlt hw0⟩
    have h1 := (eqE_iff hQ hκ (mulE_lt hwlt hwlt) (by decide : oneE.1 < 64)).1 hww
    rwa [nfE_mulE hQ hwlt hwlt, nfE_oneE] at h1
  by_cases hcase : ∃ r₁ ∈ Y, ∃ β₁ : E ≃* E, (∀ e, q (β₁ e) = r₁ * q e * r₁⁻¹) ∧
      ∃ t₁ < 64, ∃ j₁ < 36, TabRep (rT t₁ j₁) r₁ ∧ (t₁, j₁) ∈ L ∧ inTabs EB (rT t₁ j₁) = false
  ·
    obtain ⟨r₁, hr₁, β₁, -, t₁, -, j₁, -, hr₁0, hmem₁, hnb⟩ := hcase
    have hB1 := List.all_eq_true.1 hB (t₁, j₁) hmem₁
    rw [hnb, Bool.false_or, is2_of_mem hY2 hYR hr₁ hr₁0, Bool.not_true, Bool.false_or,
      List.any_eq_true] at hB1
    obtain ⟨w, hwW, hwL⟩ := hB1
    obtain ⟨hwlt, hwT, hww, hw1⟩ := hwprop w hwW
    refine ⟨nfE l w, hwT, hww, hw1, fun r hr β' hβ' => ?_⟩
    obtain ⟨t, -, j, -, hr0, hmem, hβ'E⟩ := hlift r hr β' hβ'
    have h1 := List.all_eq_true.1 hwL (t, j) hmem
    rw [Bool.or_eq_true] at h1
    rcases h1 with hfix | hesc
    · rw [(hβ'E w hwlt).1]
      exact (eqE_iff hQ hκ (hβ'E w hwlt).2 hwlt).1 hfix
    · exfalso
      have htwo : twoOK (rT t j) ([rT t₁ j₁, rT t₀ i₀] ++ Ft) = true := by
        simp only [twoOK, Bool.and_eq_true, List.all_eq_true]
        refine ⟨is2_of_mem hY2 hYR hr hr0, fun s hs => ?_⟩
        obtain ⟨g, hgY, hsg⟩ : ∃ g ∈ Y, TabRep s g := by
          rw [List.mem_append, List.mem_cons, List.mem_cons, List.mem_nil_iff, or_false] at hs
          rcases hs with (rfl | rfl) | hs
          · exact ⟨r₁, hr₁, hr₁0⟩
          · exact ⟨ρ, hρY, hρ0⟩
          · exact hFY s hs
        exact ⟨is2_of_mem hY2 hYR (Y.mul_mem hr hgY) (hr0.comp hsg),
          is2_of_mem hY2 hYR (Y.mul_mem hgY hr) (hsg.comp hr0)⟩
      rw [htwo, Bool.not_true] at hesc
      exact Bool.false_ne_true hesc
  ·
    push Not at hcase
    rw [c4A, List.any_eq_true] at hA
    obtain ⟨w, hwW, hwL⟩ := hA
    obtain ⟨hwlt, hwT, hww, hw1⟩ := hwprop w hwW
    refine ⟨nfE l w, hwT, hww, hw1, fun r hr β' hβ' => ?_⟩
    obtain ⟨t, ht, j, hj, hr0, hmem, hβ'E⟩ := hlift r hr β' hβ'
    have hin : inTabs EB (rT t j) = true := by
      cases h : inTabs EB (rT t j)
      · exact absurd h (hcase r hr β' hβ' t ht j hj hr0 hmem)
      · rfl
    have h1 := List.all_eq_true.1 hwL (t, j) hmem
    rw [hin, Bool.not_true, Bool.false_or] at h1
    rw [(hβ'E w hwlt).1]
    exact (eqE_iff hQ hκ (hβ'E w hwlt).2 hwlt).1 h1

end CFSG.ComponentClassification.GrSLit
