module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Small
public import CFSG.ClassicalInvolution.Asc77.AscMuTabEdge
public import CFSG.ClassicalInvolution.Asc77.AscMuTabKind

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

theorem false_of_commutes_three_five (h2 : (2 : F) ≠ 0) {hn : 2 ≤ 5}
    {L₀ L₁ L₂ : Subgroup SL(5, F)} {i₀ i₁ i₂ : SL(5, F)} (h₀ : IsLongRootSL2 hn L₀ i₀)
    (h₁ : IsLongRootSL2 hn L₁ i₁) (h₂' : IsLongRootSL2 hn L₂ i₂) (h01 : L₀ ≠ L₁)
    (h02 : L₀ ≠ L₂) (h12 : L₁ ≠ L₂) (c01 : Commutes L₀ L₁) (c02 : Commutes L₀ L₂)
    (c12 : Commutes L₁ L₂) : False := by
  obtain ⟨le01, le10, hb01⟩ := le_of_commutes h2 (by omega) h₀ h₁ h01 c01
  obtain ⟨le02, le20, hb02⟩ := le_of_commutes h2 (by omega) h₀ h₂' h02 c02
  obtain ⟨le12, le21, hb12⟩ := le_of_commutes h2 (by omega) h₁ h₂' h12 c12
  have c₀ := h₀.isCompl h2
  have c₁ := h₁.isCompl h2
  have hV0 := h₀.finrank_minusSpace h2
  have hV1 := h₁.finrank_minusSpace h2
  have hV2 := h₂'.finrank_minusSpace h2
  have hsum01 := Submodule.finrank_sup_add_finrank_inf_eq (minusSpace i₀) (minusSpace i₁)
  rw [hb01, finrank_bot] at hsum01
  have hbot : (minusSpace i₀ ⊔ minusSpace i₁) ⊓ minusSpace i₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hx2⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    have haW : a ∈ fixSpace i₀ := by
      have h1 : a = (a + b) - b := by abel
      rw [h1]
      exact Submodule.sub_mem _ (le20 hx2) (le10 hb)
    have ha0 : a = 0 := by
      have : a ∈ minusSpace i₀ ⊓ fixSpace i₀ := ⟨ha, haW⟩
      rwa [c₀.inf_eq_bot, Submodule.mem_bot] at this
    have hb0 : b = 0 := by
      have hbx : b ∈ minusSpace i₂ := by simpa [ha0] using hx2
      have : b ∈ minusSpace i₁ ⊓ fixSpace i₁ := ⟨hb, le21 hbx⟩
      rwa [c₁.inf_eq_bot, Submodule.mem_bot] at this
    rw [ha0, hb0, add_zero]
    exact Submodule.zero_mem _
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (minusSpace i₀ ⊔ minusSpace i₁)
    (minusSpace i₂)
  rw [hbot, finrank_bot] at hsum
  have hle := Submodule.finrank_le (minusSpace i₀ ⊔ minusSpace i₁ ⊔ minusSpace i₂)
  rw [Module.finrank_fin_fun] at hle
  omega

end Linear

section Unitary

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem false_of_orth_three_five {σ : K ≃+* K} {V₀ V₁ V₂ : Submodule K (Fin 5 → K)}
    (n₁ : Nondeg σ V₁) (n₂ : Nondeg σ V₂) (d₀ : Module.finrank K V₀ = 2)
    (d₁ : Module.finrank K V₁ = 2) (d₂ : Module.finrank K V₂ = 2) (o01 : Orth σ V₀ V₁)
    (o02 : Orth σ V₀ V₂) (o12 : Orth σ V₁ V₂) : False := by
  have hdisj : Disjoint V₀ V₁ := disjoint_of_orth n₁ o01
  have hsum := finrank_sup_of_disjoint hdisj
  have hdisj2 : Disjoint (V₀ ⊔ V₁) V₂ := by
    rw [Submodule.disjoint_def]
    intro v hv hv₂
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    refine n₂ _ hv₂ fun t ht => ?_
    rw [herm_add_left, o02 x hx t ht, o12 y hy t ht, add_zero]
  have hsum2 := finrank_sup_of_disjoint hdisj2
  have hle := Submodule.finrank_le (V₀ ⊔ V₁ ⊔ V₂)
  rw [Module.finrank_fin_fun] at hle
  omega

end Unitary

section Models

variable {p : ℕ} [Fact p.Prime]

theorem noThree_psl5 (hp2 : p ≠ 2) {e : ℕ} {A B S : Subgroup (modelUniv .PSL 5 p e Fact.out).K}
    (hA : A ∈ ModelFund p .PSL 5 e) (hB : B ∈ ModelFund p .PSL 5 e)
    (hS : S ∈ ModelFund p .PSL 5 e) (hAB : A ≠ B) (hAS : A ≠ S) (hBS : B ≠ S)
    (cAB : Commutes A B) (cAS : Commutes A S) (cBS : Commutes B S) : False := by
  have h := fundamentalSubgroups_psl_eq (p := p) (f := e) (m := 4) (by norm_num)
  have hA' : A ∈ Models.longRootSet (K := GaloisField p e) (by omega : 2 ≤ 4 + 1) := by
    rw [← h]; exact hA
  have hB' : B ∈ Models.longRootSet (K := GaloisField p e) (by omega : 2 ≤ 4 + 1) := by
    rw [← h]; exact hB
  have hS' : S ∈ Models.longRootSet (K := GaloisField p e) (by omega : 2 ≤ 4 + 1) := by
    rw [← h]; exact hS
  obtain ⟨i₀, h₀⟩ := hA'
  obtain ⟨i₁, h₁⟩ := hB'
  obtain ⟨i₂, h₂⟩ := hS'
  exact false_of_commutes_three_five (ModelFacts.two_ne_zero_galoisField e hp2) h₀ h₁ h₂ hAB hAS
    hBS cAB cAS cBS

theorem noThree_psu5 (hp2 : p ≠ 2) {e : ℕ} (hadm : StatedLieAdmissible .PSU 5 p e)
    {A B S : Subgroup (modelUniv .PSU 5 p e Fact.out).K} (hA : A ∈ ModelFund p .PSU 5 e)
    (hB : B ∈ ModelFund p .PSU 5 e) (hS : S ∈ ModelFund p .PSU 5 e) (hAB : A ≠ B) (hAS : A ≠ S)
    (hBS : B ≠ S) (cAB : Commutes A B) (cAS : Commutes A S) (cBS : Commutes B S) : False := by
  have hf : 1 ≤ e := hadm.2.1
  have hK := CFSG.LieType.Universal.card_galoisField_two_mul p e hf
  obtain ⟨φ, hφ⟩ := psu_model_equiv hp2 hadm
  have hn : 2 ≤ 5 := by norm_num
  have hn3 : 3 ≤ 5 := by norm_num
  obtain ⟨V₀, n₀, d₀, e₀⟩ := (mem_longRootSetU_iff_plane hK hp2 hn).mp ((hφ A).mp hA)
  obtain ⟨V₁, n₁, d₁, e₁⟩ := (mem_longRootSetU_iff_plane hK hp2 hn).mp ((hφ B).mp hB)
  obtain ⟨V₂, n₂, d₂, e₂⟩ := (mem_longRootSetU_iff_plane hK hp2 hn).mp ((hφ S).mp hS)
  have c01 := (commutes_map_equiv φ).mpr cAB
  have c02 := (commutes_map_equiv φ).mpr cAS
  have c12 := (commutes_map_equiv φ).mpr cBS
  rw [e₀, e₁] at c01
  rw [e₀, e₂] at c02
  rw [e₁, e₂] at c12
  have hV01 : V₀ ≠ V₁ := fun h => hAB (Subgroup.map_injective φ.injective (by rw [e₀, e₁, h]))
  have hV02 : V₀ ≠ V₂ := fun h => hAS (Subgroup.map_injective φ.injective (by rw [e₀, e₂, h]))
  have hV12 : V₁ ≠ V₂ := fun h => hBS (Subgroup.map_injective φ.injective (by rw [e₁, e₂, h]))
  exact false_of_orth_three_five n₁ n₂ d₀ d₁ d₂
    ((commutes_planeGroupU_iff hK hp2 hn hn3 n₀ d₀ n₁ d₁ hV01).mp c01)
    ((commutes_planeGroupU_iff hK hp2 hn hn3 n₀ d₀ n₂ d₂ hV02).mp c02)
    ((commutes_planeGroupU_iff hK hp2 hn hn3 n₁ d₁ n₂ d₂ hV12).mp c12)

end Models

section Shapes

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {k e : ℕ}

omit [Finite G] in
theorem commutingPair_psu (M : Ih8Model p f Ω .PSU k e) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hne : Ω.Nonempty) (hk : 5 ≤ k) : ∃ R ∈ M.cls, ∃ S ∈ M.cls, R ≠ S ∧ Commutes R S := by
  have hf1 : 1 ≤ e := M.admissible.2.1
  have hK := CFSG.LieType.Universal.card_galoisField_two_mul p e hf1
  have hq' : 5 ≤ p ^ e := (M.exp_eq_f (by decide)) ▸ hq
  have hq2 : p ^ e ≠ 2 := by omega
  obtain ⟨φ, hφ⟩ := psu_model_equiv hp2 M.admissible
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have h0 : 0 < n := by omega
  have h2 : 2 < n := by omega
  have hc := (Phan.weakPhanA_standard hK hq2 n).comm ⟨0, h0⟩ ⟨2, h2⟩ (by show 0 + 1 < 2; omega)
  have hmem : ∀ i : Fin n, (Phan.standardU (GaloisField p (2 * e)) p e n i).map φ.symm.toMonoidHom ∈
      fundamentalSubgroups .PSU (modelUniv .PSU (n + 1) p e Fact.out).D := fun i => by
    rw [hφ, muTab_map_equiv_symm_map]
    exact ⟨_, Models.isLongRootSU2_range_blockEmb hK hp2 (by omega : (i : ℕ) + 2 ≤ n + 1)⟩
  have hcm : Commutes ((Phan.standardU (GaloisField p (2 * e)) p e n ⟨0, h0⟩).map
      φ.symm.toMonoidHom) ((Phan.standardU (GaloisField p (2 * e)) p e n ⟨2, h2⟩).map
      φ.symm.toMonoidHom) := (commutes_map_equiv φ.symm).mpr hc
  refine ⟨_, M.fund_subset_cls hne (by decide) (by decide) (hmem ⟨0, h0⟩), _,
    M.fund_subset_cls hne (by decide) (by decide) (hmem ⟨2, h2⟩), ?_, hcm⟩
  intro h
  refine not_commutes_self_modelFund hp2 M.isFundTag hq' M.admissible (hmem ⟨0, h0⟩) ?_
  intro a ha b hb
  exact hcm a ha b (h ▸ hb)

theorem muKind_psl_five_true : muKind true .PSL 5 = .big10 := by simp [muKind]

theorem muKind_psl_five_false : muKind false .PSL 5 = .e4 := by simp [muKind]

theorem muKind_psu_five_true : muKind true .PSU 5 = .e4 := by simp [muKind]

theorem muKind_psu_five_false : muKind false .PSU 5 = .big10 := by simp [muKind]

theorem shapeE4_psl5 (M : Ih8Model p f Ω .PSL 5 e) (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hne : Ω.Nonempty) (hq3 : p ^ f % 4 = 3) : ShapeE4 Ω := by
  have hG2 : StatedLieTag.PSL ≠ .G2 := by decide
  have hD4 : StatedLieTag.PSL ≠ .trialityD4 := by decide
  have hq' : 5 ≤ p ^ e := (M.exp_eq_f hD4) ▸ hq
  refine ⟨M.muTab_starSubset hΩ hp2 hq hG2 hD4
    (fun R hR S hS' hJ => M.muTab_star_psl hΩ hp2 hq (by decide) hq3 hR hS' hJ),
    M.muTab_noTriangle hΩ hp2 hq hG2 hD4 ?_, M.muTab_edge hΩ hp2 hq hG2 hD4 ?_⟩
  · intro A hA B hB S hS' hAB hAS hBS cAB cAS cBS
    exact noThree_psl5 hp2 (M.cls_sub hA) (M.cls_sub hB) (M.cls_sub hS') hAB hAS hBS cAB cAS cBS
  · obtain ⟨R, hR, S, hS', hRS, hc⟩ := ih8_exists_commuting_of_orth_nodes hp2 hq' M.isFundTag
      M.admissible (i := (⟨0, by omega⟩ : Fin 4)) (j := (⟨2, by omega⟩ : Fin 4)) trivial trivial
      (by
        show CartanMatrix.A 4 _ _ = 0
        simp [CartanMatrix.A])
    exact ⟨R, M.fund_subset_cls hne hG2 hD4 hR, S, M.fund_subset_cls hne hG2 hD4 hS', hRS, hc⟩

theorem shapeE4_psu5 (M : Ih8Model p f Ω .PSU 5 e) (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hne : Ω.Nonempty) (hq1 : p ^ f % 4 = 1) : ShapeE4 Ω := by
  have hG2 : StatedLieTag.PSU ≠ .G2 := by decide
  have hD4 : StatedLieTag.PSU ≠ .trialityD4 := by decide
  refine ⟨M.muTab_starSubset hΩ hp2 hq hG2 hD4
    (fun R hR S hS' hJ => M.muTab_star_psu hΩ hp2 hq hq1 hR hS' hJ),
    M.muTab_noTriangle hΩ hp2 hq hG2 hD4 ?_, M.muTab_edge hΩ hp2 hq hG2 hD4 ?_⟩
  · intro A hA B hB S hS' hAB hAS hBS cAB cAS cBS
    exact noThree_psu5 hp2 M.admissible (M.cls_sub hA) (M.cls_sub hB) (M.cls_sub hS') hAB hAS hBS
      cAB cAS cBS
  · exact commutingPair_psu M hp2 hq hne (le_refl 5)

end Shapes

end MuTab

end CFSG.ClassicalInvolution.Asc77
