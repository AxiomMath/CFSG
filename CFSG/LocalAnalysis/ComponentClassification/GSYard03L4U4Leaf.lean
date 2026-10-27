module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard03Cat
public import CFSG.LocalAnalysis.ComponentClassification.GSYard03L4U4
import CFSG.LocalAnalysis.ComponentClassification.GSYard02CoverL4U4

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard03

open CFSG Subgroup Blueprint GSYard02
open CFSG.Open (StatedSL StatedSU StatedProj StatedScalars)

theorem exists_mulEquiv_statedSL4_of_coverHyp (hG : CFSG.GH74.Generic.GenericKnownFacts)
    {Q : Type} [Group Q] [Finite Q] (hQ : CoverHyp Q) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : LieModel (Q ⧸ center Q) .PSL 4 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), (2 : F) ≠ 0 ∧
      Nonempty (↥(StatedSL 4 F) ≃* Q) := by
  obtain ⟨hquasi, hz, h2z, -, -, hgen⟩ := hQ
  obtain ⟨F, hFf, hFfin, hF, ⟨e⟩⟩ := l4u_iso_psl4 (Q ⧸ Subgroup.center Q) h
  have hodd : Odd (Nat.card F) := by
    rw [hF]; exact (hp.odd_of_ne_two hp2).pow
  have h2F : (2 : F) ≠ 0 := CFSG.GH74.L5U5.two_ne_zero_of_odd_card hodd
  obtain ⟨π, hπs, hπe⟩ := hG.psl4_cover Q hquasi h2z F hodd e
  have hker := l4u_ker_scalar e π hπe
  have hZ : Subgroup.center (StatedProj (StatedSL 4 F)) = ⊥ := l4u_centre_statedProj_SL4
  have hnonker := l4u_exists_nonker hZ π hπs hker hz
  by_cases h4 : Nat.card F % 4 = 3
  · have hinj : Function.Injective π := by
      rw [injective_iff_map_eq_one]
      intro g hg
      obtain ⟨c, hc⟩ := hker g hg
      have hcen : g ∈ Subgroup.center (StatedSL 4 F) := by
        rw [CFSG.GH74.L5U5.center_statedSL_eq, Subgroup.mem_subgroupOf]
        rw [StatedScalars, MonoidHom.mem_range]
        exact ⟨c, hc.symm⟩
      rcases (CFSG.GH74.L5U5.mem_center_statedSL_four_iff h4 g).1 hcen with h1 | h1
      · exact Subtype.ext h1
      · obtain ⟨g₀, hg₀, hπg₀⟩ := hnonker
        have hcen₀ : g₀ ∈ Subgroup.center (StatedSL 4 F) := by
          rw [CFSG.GH74.L5U5.center_statedSL_eq, Subgroup.mem_subgroupOf]
          rw [StatedScalars, MonoidHom.mem_range]
          obtain ⟨c₀, hc₀⟩ := hg₀
          exact ⟨c₀, hc₀.symm⟩
        rcases (CFSG.GH74.L5U5.mem_center_statedSL_four_iff h4 g₀).1 hcen₀ with h0 | h0
        · have hg₁ : g₀ = 1 := Subtype.ext h0
          exact (hπg₀ (by rw [hg₁, map_one])).elim
        · have hg₁ : g₀ = g := Subtype.ext (h0.trans h1.symm)
          exact (hπg₀ (by rw [hg₁, hg])).elim
    exact ⟨F, hFf, hFfin, h2F, ⟨MulEquiv.ofBijective π ⟨hinj, hπs⟩⟩⟩
  · exfalso
    have hi : ∃ i : F, i * i = -1 := by
      haveI := Fintype.ofFinite F
      have hsq : IsSquare (-1 : F) := by
        rw [FiniteField.isSquare_neg_one_iff, Fintype.card_eq_nat_card]
        omega
      obtain ⟨r, hr⟩ := hsq
      exact ⟨r, hr.symm⟩
    obtain ⟨i, hi⟩ := hi
    have hpm := l4u_ker_pm_one (fun g hg => CFSG.Open.StatedAPI.det_of_mem_statedSL hg) π hker
      hnonker
    exact not_gen4_of_SL4 hi h2F π (fun g hg => hpm g (MonoidHom.mem_ker.1 hg)) hgen

theorem exists_mulEquiv_statedSU4_of_coverHyp (hG : CFSG.GH74.Generic.GenericKnownFacts)
    {Q : Type} [Group Q] [Finite Q] (hQ : CoverHyp Q) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (h : LieModel (Q ⧸ center Q) .PSU 4 p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K p), Nat.card K = (p ^ f) ^ 2 ∧
      Nonempty (↥(StatedSU 4 (p ^ f) K) ≃* Q) := by
  obtain ⟨hquasi, hz, h2z, -, -, hgen⟩ := hQ
  obtain ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ := l4u_iso_psu4 (Q ⧸ Subgroup.center Q) h
  have hq_odd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hKodd : Odd (Nat.card K) := by
    rw [hK]; exact hq_odd.pow
  have h2K : (2 : K) ≠ 0 := CFSG.GH74.L5U5.two_ne_zero_of_odd_card hKodd
  obtain ⟨π, hπs, hπe⟩ := hG.psu4_cover Q hquasi h2z K (p ^ f) hK hq_odd e
  have hker := l4u_ker_scalar e π hπe
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ : Subgroup.center (StatedProj (StatedSU 4 (p ^ f) K)) = ⊥ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.ka_center_bot_pu hK (by norm_num) (by simp)
  have hnonker := l4u_exists_nonker hZ π hπs hker hz
  by_cases h4 : p ^ f % 4 = 1
  · have hUFD : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
      { prime := hp, one_le := hf, card := by rw [hK, ← pow_mul, mul_comm] }
    have hinj : Function.Injective π := by
      rw [injective_iff_map_eq_one]
      intro g hg
      obtain ⟨c, hc⟩ := hker g hg
      have hsc : Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ StatedSU 4 (p ^ f) K := by
        rw [← hc]; exact g.2
      have hcen : g ∈ Subgroup.center (StatedSU 4 (p ^ f) K) := by
        have hg_eq : g = ⟨Matrix.GeneralLinearGroup.scalar (Fin 4) c, hsc⟩ := Subtype.ext hc
        rw [hg_eq]
        exact l4u_scalar_central c hsc
      rcases (CFSG.GH74.L5U5.mem_center_statedSU_four_iff hK h4 g).1 hcen with h1 | h1
      · exact Subtype.ext h1
      · obtain ⟨g₀, hg₀, hπg₀⟩ := hnonker
        have hcen₀ : g₀ ∈ Subgroup.center (StatedSU 4 (p ^ f) K) := by
          obtain ⟨c₀, hc₀⟩ := hg₀
          have hsc₀ : Matrix.GeneralLinearGroup.scalar (Fin 4) c₀ ∈ StatedSU 4 (p ^ f) K := by
            rw [← hc₀]; exact g₀.2
          have hg_eq₀ : g₀ = ⟨Matrix.GeneralLinearGroup.scalar (Fin 4) c₀, hsc₀⟩ :=
            Subtype.ext hc₀
          rw [hg_eq₀]
          exact l4u_scalar_central c₀ hsc₀
        rcases (CFSG.GH74.L5U5.mem_center_statedSU_four_iff hK h4 g₀).1 hcen₀ with h0 | h0
        · have hg₁ : g₀ = 1 := Subtype.ext h0
          exact (hπg₀ (by rw [hg₁, map_one])).elim
        · have hg₁ : g₀ = g := Subtype.ext (h0.trans h1.symm)
          exact (hπg₀ (by rw [hg₁, hg])).elim
    exact ⟨K, hKf, hKfin, hUFD.charP, hK, ⟨MulEquiv.ofBijective π ⟨hinj, hπs⟩⟩⟩
  · exfalso
    have h4' : p ^ f % 4 = 3 := by
      have hodd := hq_odd
      rw [Nat.odd_iff] at hodd
      omega
    have hq2 : (p ^ f) ^ 2 % 4 = 1 := by
      rw [Nat.pow_mod, h4']
    have hi : ∃ i : K, i * i = -1 := by
      haveI := Fintype.ofFinite K
      have hsq : IsSquare (-1 : K) := by
        rw [FiniteField.isSquare_neg_one_iff, Fintype.card_eq_nat_card, hK, hq2]
        norm_num
      obtain ⟨r, hr⟩ := hsq
      exact ⟨r, hr.symm⟩
    obtain ⟨i, hi⟩ := hi
    have hpm := l4u_ker_pm_one (fun g hg => CFSG.Open.StatedAPI.det_of_mem_statedSU hg) π hker
      hnonker
    exact not_gen4_of_SU4 hq_odd h4' hK hi h2K π (fun g hg => hpm g (MonoidHom.mem_ker.1 hg)) hgen

theorem f1LeafL4_holds
    : CoverLeafL4For F1Concl := by
  intro Q _ _ hQ p f hp hp2 _ _ h _ _
  have hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  obtain ⟨F, _, _, h2F, ⟨e⟩⟩ :=
    exists_mulEquiv_statedSL4_of_coverHyp (CFSG.GH74.Generic.genericKnownFacts_of_griess hGA) hQ
      hp hp2 h
  exact CentralSquareFour.of_mulEquiv e (centralSquareFour_statedSL4 h2F)

theorem f1LeafU4_holds
    : CoverLeafU4For F1Concl := by
  intro Q _ _ hQ p f hp hp2 hf _ h _ _
  have hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ :=
    exists_mulEquiv_statedSU4_of_coverHyp (CFSG.GH74.Generic.genericKnownFacts_of_griess hGA) hQ
      hp hp2 hf h
  haveI : Fact p.Prime := ⟨hp⟩
  exact CentralSquareFour.of_mulEquiv e (centralSquareFour_statedSU4 hp2 hK)

end CFSG.ComponentClassification.Sol76.Sig.GSYard03
