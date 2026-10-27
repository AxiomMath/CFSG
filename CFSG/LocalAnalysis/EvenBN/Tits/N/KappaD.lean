module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.KappaSplit
public import CFSG.LocalAnalysis.EvenBN.Tits.N.KappaDN
public import CFSG.LocalAnalysis.EvenBN.Tits.N.KappaDCert
public import CFSG.LocalAnalysis.EvenBN.Tits.N.KappaLemmaA

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Sporadic.Schreier.Tits KappaD


theorem stepKappaBitD_holds : StepKappaBitD := by
  intro G _ _ d h49 hd hD
  obtain ⟨z₀, hz⟩ := hd.s56_exists_S56Z0 h49
  by_contra hnot
  obtain ⟨e, he, hne⟩ : ∃ e ∈ d.E ⊓ d.F, e ∉ d.s56U10 := by
    by_contra hall
    have hall' : ∀ e ∈ d.E ⊓ d.F, e ∈ d.s56U10 := fun e he => by
      by_contra h
      exact hall ⟨e, he, h⟩
    have hdvd := Subgroup.card_dvd_of_le (fun e he => hall' e he : d.E ⊓ d.F ≤ d.s56U10)
    rw [hd.s56_card_E_inf_F, Data.s56_card_U10] at hdvd
    norm_num at hdvd
  obtain ⟨x, hxV, hxε⟩ := hd.s56_V_eps_surj h49 hz e (mem_inf.1 he).1
  have hxN : x ∈ d.N := (hd.s56_mem_N_iff_eps h49 (hd.s56_Q_le_Q0 hxV.1)).2
    (by rw [hxε]; exact (mem_inf.1 he).2)
  have hxVN : x ∈ d.s56V ⊓ d.N := mem_inf.2 ⟨hxV, hxN⟩
  have hxP0 : x ∈ d.s56P0 := hd.s56_Q2_inf_N_le_P0 h49 hxV.2 hxN
  obtain ⟨e₁, e₂, e₃, e₄, hec, hec4⟩ := coord_EF hd he
  have hε : d.s56Eps x = d.z ^ e₁.val * d.pv 11 ^ e₂.val * d.pv 10 ^ e₃.val * d.pv 9 ^ e₄.val := by
    rw [hxε]; exact hec
  have he4 : e₄ = 1 := by
    by_contra h4
    have h0 : e₄ = 0 := by
      generalize e₄ = a at h4
      revert a; decide
    exact hne (hec4 h0)
  have hδ10 : x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹ ∈ d.s56U10 :=
    hd.s56_P0_comm_F_le_U10 h49 hxP0 hd.s56_pv7_mem_F
  obtain ⟨d₁, d₂, d₃, hδ, hδ3⟩ := coord_U10 hd hδ10
  have hd3 : d₃ = 1 := by
    by_contra h3
    have h0 : d₃ = 0 := by
      generalize d₃ = a at h3
      revert a; decide
    refine hnot ⟨x, hxVN, ?_, ?_⟩
    · rw [hxε]; exact hne
    · exact hδ3 h0
  subst he4
  rcases hd.kappaLemmaA h49 hz hxVN hε hδ with ⟨-, h3⟩ | ⟨h2, -⟩
  · rw [hd3] at h3; exact absurd h3 (by decide)
  · obtain ⟨τ, T, SL, words, h1, h2', h3', h4⟩ := kappaD_model_facts
    exact noBadX h49 hd hD τ h1 T h2' SL h3' words h4 hxVN (e₁ := e₁) (e₂ := e₂) (e₃ := e₃) (d₁ := d₁)
      (by rw [hε]; simp) (by rw [hδ, h2, hd3]; simp)

end CFSG.LocalAnalysis.EvenBN.Tits.N
