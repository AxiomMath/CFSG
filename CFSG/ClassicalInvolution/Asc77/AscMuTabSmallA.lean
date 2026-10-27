module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabFinal
public import CFSG.ClassicalInvolution.Asc77.AscMuTabEdge
public import CFSG.ClassicalInvolution.Asc77.AscIHSectE

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Disconnected

namespace MuTab

section Mod

variable {p f : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem piSign_true_iff : piSign p f = true ↔ p ^ f % 4 = 1 := by
  simp [piSign]

theorem pow_mod_four (hp2 : p ≠ 2) : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
  have hodd : Odd (p ^ f) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  obtain ⟨m, hm⟩ := hodd
  omega

theorem pow_mod_four_of_piSign_false (hp2 : p ≠ 2) (h : piSign p f = false) :
    p ^ f % 4 = 3 := by
  have h1 : ¬ p ^ f % 4 = 1 := fun h' => by
    have := piSign_true_iff.mpr h'
    rw [h] at this
    exact Bool.false_ne_true this
  rcases pow_mod_four (f := f) hp2 with h | h
  · exact absurd h h1
  · exact h

end Mod

section Datum

variable {p f : ℕ} [Fact p.Prime]

theorem exists_datum {X : Type} [Group X] {Φ : Set (Subgroup X)} (hS : TransSection p f Φ)
    {t : StatedLieTag} {k : ℕ} (hL : HasLieType p f Φ t k) :
    ∃ e, Nonempty (Ih8Model p f Φ t k e) := exists_datum_of_hasLieType hS hL

end Datum

section Sp

variable {p f : ℕ} [Fact p.Prime]

theorem muKind_psp_two (π : Bool) : muKind π .PSp 2 = .e4 := by
  cases π <;> simp [muKind]

theorem smallShape_psp2 : SmallShape p f .PSp 2 := by
  intro hp2 hq X _ _ Φ hS hne htop hL
  rw [muKind_psp_two]
  obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieType hS hL
  have hΩ := hS.hyp
  have hG2 : StatedLieTag.PSp ≠ .G2 := by decide
  have hD4 : StatedLieTag.PSp ≠ .trialityD4 := by decide
  have hq' : 5 ≤ p ^ e := (M.exp_eq_f hD4) ▸ hq
  refine ⟨M.muTab_starSubset hΩ hp2 hq hG2 hD4
    (fun R hR S hS' hJ => M.muTab_star_psp hΩ hp2 hq hR hS' hJ),
    M.muTab_noTriangle hΩ hp2 hq hG2 hD4 ?_, ?_⟩
  · intro A hA B hB S hS' hAB hAS hBS cAB cAS cBS
    exact smallNoThree (p := p) _ _ _ M.admissible hp2 hq' (Or.inl ⟨rfl, rfl⟩) A (M.cls_sub hA)
      B (M.cls_sub hB) S (M.cls_sub hS') hAB hAS hBS cAB cAS cBS
  · refine M.muTab_edge hΩ hp2 hq hG2 hD4 ?_
    obtain ⟨R, hR, S, hS', hRS, hc⟩ := ih8SmallEdge p _ _ _ M.admissible hp2 hq'
      (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    exact ⟨R, M.fund_subset_cls hne hG2 hD4 hR, S, M.fund_subset_cls hne hG2 hD4 hS', hRS, hc⟩

end Sp

section Three

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {t : StatedLieTag} {k e : ℕ}

theorem dEdgeless_of_three (M : Ih8Model p f Ω t k e) (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (h3 : (t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3)) : DEdgeless Ω := by
  intro K hK J hJ hadj
  rcases hadj with h | h
  · exact M.not_omegaNbr_of_three_sect hΩ hp2 hq h3 hK h
  · exact M.not_omegaNbr_of_three_sect hΩ hp2 hq h3 hJ h

theorem muKind_psl_three_true : muKind true .PSL 3 = .s3 := by simp [muKind]

theorem muKind_psl_three_false : muKind false .PSL 3 = .z2 := by simp [muKind]

theorem muKind_psu_three_true : muKind true .PSU 3 = .z2 := by simp [muKind]

theorem muKind_psu_three_false : muKind false .PSU 3 = .s3 := by simp [muKind]

theorem smallShape_psl3 : SmallShape p f .PSL 3 := by
  intro hp2 hq X _ _ Φ hS hne htop hL
  obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieType hS hL
  have hΩ := hS.hyp
  have hG2 : StatedLieTag.PSL ≠ .G2 := by decide
  have hD4 : StatedLieTag.PSL ≠ .trialityD4 := by decide
  have hnpsl := M.not_psl_two_sect hp2 hne htop
  have hE := dEdgeless_of_three M hΩ hp2 hq (Or.inl ⟨rfl, rfl⟩)
  cases hπ : piSign p f
  · rw [muKind_psl_three_false]
    have hq3 := pow_mod_four_of_piSign_false hp2 hπ
    intro K hK
    refine Set.eq_empty_of_forall_notMem fun J hJ => ?_
    have h := M.muTab_starSubset hΩ hp2 hq hG2 hD4
      (fun R hR S hS' hJ' => M.muTab_star_psl hΩ hp2 hq (by decide) hq3 hR hS' hJ') K hK hJ
    exact M.not_omegaNbr_of_three_sect hΩ hp2 hq (Or.inl ⟨rfl, rfl⟩) hK h
  · rw [muKind_psl_three_true]
    have hq4 := piSign_true_iff.mp hπ
    refine ⟨hE, ?_⟩
    obtain ⟨R₁, hR₁, R₂, hR₂, W, hW⟩ := M.muTab_linearPair_psl hne (le_refl 3)
    have hadj := M.muTab_dstarAdj_linear hΩ hp2 hq hD4 hnpsl hq4 hR₁ hR₂ hW
    rcases hadj.2 with h | h
    · exact ⟨R₁.map M.ψ, M.map_mem hR₁, _, h⟩
    · exact ⟨R₂.map M.ψ, M.map_mem hR₂, _, h⟩

theorem smallShape_psu3 : SmallShape p f .PSU 3 := by
  intro hp2 hq X _ _ Φ hS hne htop hL
  obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieType hS hL
  have hΩ := hS.hyp
  have hG2 : StatedLieTag.PSU ≠ .G2 := by decide
  have hD4 : StatedLieTag.PSU ≠ .trialityD4 := by decide
  have hnpsl := M.not_psl_two_sect hp2 hne htop
  have hE := dEdgeless_of_three M hΩ hp2 hq (Or.inr ⟨rfl, rfl⟩)
  cases hπ : piSign p f
  · rw [muKind_psu_three_false]
    have hq3 := pow_mod_four_of_piSign_false hp2 hπ
    refine ⟨hE, ?_⟩
    obtain ⟨R₁, hR₁, R₂, hR₂, W, hW⟩ := M.muTab_unitaryPair_psu hp2 hne
    have hadj := M.muTab_dstarAdj_unitary hΩ hp2 hq hD4 hnpsl hq3 hR₁ hR₂ hW
    rcases hadj.2 with h | h
    · exact ⟨R₁.map M.ψ, M.map_mem hR₁, _, h⟩
    · exact ⟨R₂.map M.ψ, M.map_mem hR₂, _, h⟩
  · rw [muKind_psu_three_true]
    have hq4 := piSign_true_iff.mp hπ
    intro K hK
    refine Set.eq_empty_of_forall_notMem fun J hJ => ?_
    have h := M.muTab_starSubset hΩ hp2 hq hG2 hD4
      (fun R hR S hS' hJ' => M.muTab_star_psu hΩ hp2 hq hq4 hR hS' hJ') K hK hJ
    exact M.not_omegaNbr_of_three_sect hΩ hp2 hq (Or.inr ⟨rfl, rfl⟩) hK h

end Three

end MuTab

end CFSG.ClassicalInvolution.Asc77
