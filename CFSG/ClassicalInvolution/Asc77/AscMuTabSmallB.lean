module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabSmallA

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary
  CFSG.LieType.BorelTits
open scoped MatrixGroups

namespace MuTab

section Linear

variable {F : Type} [Field F]

theorem false_of_matching_four (h2 : (2 : F) ≠ 0) {hn : 2 ≤ 4} {L₀ L₁ L₂ : Subgroup SL(4, F)}
    {i₀ i₁ i₂ : SL(4, F)} (h₀ : IsLongRootSL2 hn L₀ i₀) (h₁ : IsLongRootSL2 hn L₁ i₁)
    (h₂' : IsLongRootSL2 hn L₂ i₂) (h01 : L₀ ≠ L₁) (h02 : L₀ ≠ L₂) (h12 : L₁ ≠ L₂)
    (c01 : Commutes L₀ L₁) (c02 : Commutes L₀ L₂) : False := by
  obtain ⟨le01, le10, -⟩ := le_of_commutes h2 (by omega) h₀ h₁ h01 c01
  obtain ⟨le02, le20, -⟩ := le_of_commutes h2 (by omega) h₀ h₂' h02 c02
  have hW0 := finrank_fixSpace_of_isLongRootSL2 h2 h₀
  have hW1 := finrank_fixSpace_of_isLongRootSL2 h2 h₁
  have hW2 := finrank_fixSpace_of_isLongRootSL2 h2 h₂'
  have hV0 := h₀.finrank_minusSpace h2
  have hV1 := h₁.finrank_minusSpace h2
  have hV2 := h₂'.finrank_minusSpace h2
  have e1 : minusSpace i₁ = fixSpace i₀ := Submodule.eq_of_le_of_finrank_eq le10 (by omega)
  have e2 : minusSpace i₂ = fixSpace i₀ := Submodule.eq_of_le_of_finrank_eq le20 (by omega)
  have f1 : minusSpace i₀ = fixSpace i₁ := Submodule.eq_of_le_of_finrank_eq le01 (by omega)
  have f2 : minusSpace i₀ = fixSpace i₂ := Submodule.eq_of_le_of_finrank_eq le02 (by omega)
  apply h12
  ext x
  rw [h₁.mem_iff_vec h2, h₂'.mem_iff_vec h2, ← f1, ← f2, e1, e2]

end Linear

section Models

variable {p : ℕ} [Fact p.Prime]

theorem matching_psl4 (hp2 : p ≠ 2) {e : ℕ} {A B S : Subgroup (modelUniv .PSL 4 p e Fact.out).K}
    (hA : A ∈ ModelFund p .PSL 4 e) (hB : B ∈ ModelFund p .PSL 4 e)
    (hS : S ∈ ModelFund p .PSL 4 e) (hAB : A ≠ B) (hAS : A ≠ S) (hBS : B ≠ S)
    (cAB : Commutes A B) (cAS : Commutes A S) : False := by
  have h := fundamentalSubgroups_psl_eq (p := p) (f := e) (m := 3) (by norm_num)
  have hA' : A ∈ Models.longRootSet (K := GaloisField p e) (by omega : 2 ≤ 3 + 1) := by
    rw [← h]; exact hA
  have hB' : B ∈ Models.longRootSet (K := GaloisField p e) (by omega : 2 ≤ 3 + 1) := by
    rw [← h]; exact hB
  have hS' : S ∈ Models.longRootSet (K := GaloisField p e) (by omega : 2 ≤ 3 + 1) := by
    rw [← h]; exact hS
  obtain ⟨i₀, h₀⟩ := hA'
  obtain ⟨i₁, h₁⟩ := hB'
  obtain ⟨i₂, h₂⟩ := hS'
  exact false_of_matching_four (ModelFacts.two_ne_zero_galoisField e hp2) h₀ h₁ h₂ hAB hAS hBS
    cAB cAS

theorem matching_psu4 (hp2 : p ≠ 2) {e : ℕ} (hadm : StatedLieAdmissible .PSU 4 p e)
    {A B S : Subgroup (modelUniv .PSU 4 p e Fact.out).K} (hA : A ∈ ModelFund p .PSU 4 e)
    (hB : B ∈ ModelFund p .PSU 4 e) (hS : S ∈ ModelFund p .PSU 4 e) (hAB : A ≠ B) (hAS : A ≠ S)
    (hBS : B ≠ S) (cAB : Commutes A B) (cAS : Commutes A S) : False := by
  have hf : 1 ≤ e := hadm.2.1
  have hK := CFSG.LieType.Universal.card_galoisField_two_mul p e hf
  obtain ⟨φ, hφ⟩ := psu_model_equiv hp2 hadm
  have hn : 2 ≤ 4 := by norm_num
  have hn3 : 3 ≤ 4 := by norm_num
  obtain ⟨V₀, n₀, d₀, e₀⟩ := (mem_longRootSetU_iff_plane hK hp2 hn).mp ((hφ A).mp hA)
  obtain ⟨V₁, n₁, d₁, e₁⟩ := (mem_longRootSetU_iff_plane hK hp2 hn).mp ((hφ B).mp hB)
  obtain ⟨V₂, n₂, d₂, e₂⟩ := (mem_longRootSetU_iff_plane hK hp2 hn).mp ((hφ S).mp hS)
  have c01 := (commutes_map_equiv φ).mpr cAB
  have c02 := (commutes_map_equiv φ).mpr cAS
  rw [e₀, e₁] at c01
  rw [e₀, e₂] at c02
  have hV01 : V₀ ≠ V₁ := fun h => hAB (Subgroup.map_injective φ.injective (by rw [e₀, e₁, h]))
  have hV02 : V₀ ≠ V₂ := fun h => hAS (Subgroup.map_injective φ.injective (by rw [e₀, e₂, h]))
  have hV12 : V₁ ≠ V₂ := fun h => hBS (Subgroup.map_injective φ.injective (by rw [e₁, e₂, h]))
  have o01 := (commutes_planeGroupU_iff hK hp2 hn hn3 n₀ d₀ n₁ d₁ hV01).mp c01
  have o02 := (commutes_planeGroupU_iff hK hp2 hn hn3 n₀ d₀ n₂ d₂ hV02).mp c02
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  have hdim := finrank_add_finrank_herm_perp hσ n₀
  have h1 : V₁ ≤ perp (unitaryInvolution (GaloisField p (2 * e)) p e) V₀ := fun v hv s hs =>
    o01.symm hσ v hv s hs
  have h2 : V₂ ≤ perp (unitaryInvolution (GaloisField p (2 * e)) p e) V₀ := fun v hv s hs =>
    o02.symm hσ v hv s hs
  have e1 : V₁ = perp (unitaryInvolution (GaloisField p (2 * e)) p e) V₀ :=
    Submodule.eq_of_le_of_finrank_eq h1 (by omega)
  have e2 : V₂ = perp (unitaryInvolution (GaloisField p (2 * e)) p e) V₀ :=
    Submodule.eq_of_le_of_finrank_eq h2 (by omega)
  exact hV12 (e1.trans e2.symm)

end Models

section Shapes

variable {p f : ℕ} [Fact p.Prime]

theorem muKind_psl_four_true : muKind true .PSL 4 = .s4 := by simp [muKind]

theorem muKind_psl_four_false : muKind false .PSL 4 = .e4 := by simp [muKind]

theorem muKind_psu_four_true : muKind true .PSU 4 = .e4 := by simp [muKind]

theorem muKind_psu_four_false : muKind false .PSU 4 = .s4 := by simp [muKind]

theorem smallShape_psl4 : SmallShape p f .PSL 4 := by
  intro hp2 hq X _ _ Φ hS hne htop hL
  obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieType hS hL
  have hΩ := hS.hyp
  have hG2 : StatedLieTag.PSL ≠ .G2 := by decide
  have hD4 : StatedLieTag.PSL ≠ .trialityD4 := by decide
  have hnpsl := M.not_psl_two_sect hp2 hne htop
  have hq' : 5 ≤ p ^ e := (M.exp_eq_f hD4) ▸ hq
  have hedge : ∃ R ∈ M.cls, ∃ S ∈ M.cls, R ≠ S ∧ Commutes R S := by
    obtain ⟨R, hR, S, hS', hRS, hc⟩ := ih8SmallEdge p _ _ _ M.admissible hp2 hq'
      (Or.inl ⟨rfl, rfl⟩)
    exact ⟨R, M.fund_subset_cls hne hG2 hD4 hR, S, M.fund_subset_cls hne hG2 hD4 hS', hRS, hc⟩
  cases hπ : piSign p f
  · rw [muKind_psl_four_false]
    have hq3 := pow_mod_four_of_piSign_false hp2 hπ
    refine ⟨M.muTab_starSubset hΩ hp2 hq hG2 hD4
      (fun R hR S hS' hJ => M.muTab_star_psl hΩ hp2 hq (by decide) hq3 hR hS' hJ),
      M.muTab_noTriangle hΩ hp2 hq hG2 hD4 ?_, M.muTab_edge hΩ hp2 hq hG2 hD4 hedge⟩
    intro A hA B hB S hS' hAB hAS hBS cAB cAS cBS
    exact smallNoThree (p := p) _ _ _ M.admissible hp2 hq' (Or.inr (Or.inl ⟨rfl, rfl⟩)) A
      (M.cls_sub hA) B (M.cls_sub hB) S (M.cls_sub hS') hAB hAS hBS cAB cAS cBS
  · rw [muKind_psl_four_true]
    have hq4 := piSign_true_iff.mp hπ
    have hMatch : ∀ A ∈ M.cls, ∀ B ∈ M.cls, ∀ S ∈ M.cls, A ≠ B → A ≠ S → B ≠ S → Commutes A B →
        Commutes A S → False := fun A hA B hB S hS' hAB hAS hBS cAB cAS =>
      matching_psl4 hp2 (M.cls_sub hA) (M.cls_sub hB) (M.cls_sub hS') hAB hAS hBS cAB cAS
    obtain ⟨R₁, hR₁, R₂, hR₂, W, hW⟩ := M.muTab_linearPair_psl hne (by norm_num)
    obtain ⟨-, hnc⟩ := M.muTab_linear_ne_nc hp2 hq hD4 hR₁ hR₂ hW
    have hadj := M.muTab_dstarAdj_linear hΩ hp2 hq hD4 hnpsl hq4 hR₁ hR₂ hW
    exact ⟨M.muTab_matching hΩ hp2 hq hG2 hD4 hMatch, M.muTab_edge hΩ hp2 hq hG2 hD4 hedge,
      _, M.map_mem hR₁, M.muTab_dComp_ne hΩ hp2 hq hG2 hD4 hMatch hR₁ hR₂ hnc hadj⟩

theorem smallShape_psu4 : SmallShape p f .PSU 4 := by
  intro hp2 hq X _ _ Φ hS hne htop hL
  obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieType hS hL
  have hΩ := hS.hyp
  have hG2 : StatedLieTag.PSU ≠ .G2 := by decide
  have hD4 : StatedLieTag.PSU ≠ .trialityD4 := by decide
  have hnpsl := M.not_psl_two_sect hp2 hne htop
  have hq' : 5 ≤ p ^ e := (M.exp_eq_f hD4) ▸ hq
  have hedge : ∃ R ∈ M.cls, ∃ S ∈ M.cls, R ≠ S ∧ Commutes R S := by
    obtain ⟨R, hR, S, hS', hRS, hc⟩ := ih8SmallEdge p _ _ _ M.admissible hp2 hq'
      (Or.inr (Or.inl ⟨rfl, rfl⟩))
    exact ⟨R, M.fund_subset_cls hne hG2 hD4 hR, S, M.fund_subset_cls hne hG2 hD4 hS', hRS, hc⟩
  cases hπ : piSign p f
  · rw [muKind_psu_four_false]
    have hq3 := pow_mod_four_of_piSign_false hp2 hπ
    have hMatch : ∀ A ∈ M.cls, ∀ B ∈ M.cls, ∀ S ∈ M.cls, A ≠ B → A ≠ S → B ≠ S → Commutes A B →
        Commutes A S → False := fun A hA B hB S hS' hAB hAS hBS cAB cAS =>
      matching_psu4 hp2 M.admissible (M.cls_sub hA) (M.cls_sub hB) (M.cls_sub hS') hAB hAS hBS
        cAB cAS
    obtain ⟨R₁, hR₁, R₂, hR₂, W, hW⟩ := M.muTab_unitaryPair_psu hp2 hne
    obtain ⟨-, hnc⟩ := M.muTab_unitary_ne_nc hp2 hq hD4 hR₁ hR₂ hW
    have hadj := M.muTab_dstarAdj_unitary hΩ hp2 hq hD4 hnpsl hq3 hR₁ hR₂ hW
    exact ⟨M.muTab_matching hΩ hp2 hq hG2 hD4 hMatch, M.muTab_edge hΩ hp2 hq hG2 hD4 hedge,
      _, M.map_mem hR₁, M.muTab_dComp_ne hΩ hp2 hq hG2 hD4 hMatch hR₁ hR₂ hnc hadj⟩
  · rw [muKind_psu_four_true]
    have hq4 := piSign_true_iff.mp hπ
    refine ⟨M.muTab_starSubset hΩ hp2 hq hG2 hD4
      (fun R hR S hS' hJ => M.muTab_star_psu hΩ hp2 hq hq4 hR hS' hJ),
      M.muTab_noTriangle hΩ hp2 hq hG2 hD4 ?_, M.muTab_edge hΩ hp2 hq hG2 hD4 hedge⟩
    intro A hA B hB S hS' hAB hAS hBS cAB cAS cBS
    exact smallNoThree (p := p) _ _ _ M.admissible hp2 hq' (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      A (M.cls_sub hA) B (M.cls_sub hB) S (M.cls_sub hS') hAB hAS hBS cAB cAS cBS

end Shapes

end MuTab

end CFSG.ClassicalInvolution.Asc77
