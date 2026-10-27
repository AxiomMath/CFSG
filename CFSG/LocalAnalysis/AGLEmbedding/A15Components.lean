module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA15Defs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
import CFSG.LocalAnalysis.AGLEmbedding.A15ComponentsAux
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeBlockRank
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveComponents
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section A15

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M H R : Subgroup G} {c : Fin 3 → G}
  {σ τ : G}

theorem D1A15Data.pRank_three_le (h : D1A15Data P M H R c σ τ) :
    Open.pRank 3 (H ⊓ M) ≤ 3 := by
  by_contra h4
  exact h.surv.ph3.false_of_four_le_pRank' h.ind Nat.prime_three (by decide) (by norm_num)
    (by omega)

theorem D1A15Data.pRank_five_le (h : D1A15Data P M H R c σ τ) :
    Open.pRank 5 (H ⊓ M) ≤ 3 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨E, hE, hEel, hEcard⟩ := pRank_attained 5 (by norm_num) (H ⊓ M)
  obtain ⟨T, hT⟩ := h.surv.ph3.isSylow
  have hEH : E ≤ H := hE.trans inf_le_left
  have hEp : IsPGroup 5 (E.subgroupOf H) := by
    intro x
    exact ⟨1, Subtype.ext (Subtype.ext (by simpa using hEel.2 _ (Subgroup.mem_subgroupOf.mp x.2)))⟩
  obtain ⟨T', hT'⟩ := hEp.exists_le_sylow
  have hTcard : Nat.card (T : Subgroup H) = 5 ^ 3 := by
    rw [← h.card_R, ← hT, Subgroup.card_map_of_injective H.subtype_injective]
  have hcard : 5 ^ Open.pRank 5 (H ⊓ M) ≤ 5 ^ 3 := by
    rw [← hEcard, ← hTcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv.symm,
      Nat.card_congr (Sylow.equiv T T').toEquiv]
    exact Subgroup.card_le_of_le hT'
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hcard

theorem D1A15Data.le_normalizer_component (h : D1A15Data P M H R c σ τ)
    (hB3 : StmtBlockThree) (hα : KFactThreeOrFiveDvd) {W : Subgroup G} (hWK : W ≤ H ⊓ M)
    (hW : ⁅W, W⁆ = W) {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lb ⊤) :
    barM M W ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have h3 := h.surv.ph3
  obtain ⟨L, hL2, rfl, hL⟩ := h3.exists_weakSBlock_or_le_inf hLb
  rcases hL with hw | hLK
  ·
    have hidx := h3.relIndex_le_pRank_three (fun L' hL' => hB3 h3 hL') hWK hw
    have hWN : W ≤ Subgroup.normalizer (L : Set G) := by
      refine le_of_relIndex_le_four_of_perfect hW ?_
      rw [← Subgroup.inf_relIndex_left]
      exact hidx.trans (h.pRank_three_le.trans (by norm_num))
    exact barM_le_normalizer_barM hWN
  ·
    have hMtop : M ≠ ⊤ := fun hM => h3.not_le (hM ▸ le_top)
    have hcat : CatalogSimpleSections (↥M ⧸ CFSG.pCore 2 ↥M) :=
      (catalogSimpleSections_of_isKProper h3.glob.kProper M hMtop).quotient _
    have hLcat := hcat.isCatalogGroup_center_quotient hLb
    obtain ⟨q, hq, hq2, hqK, hqdvd⟩ : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ Open.pRank q (H ⊓ M) ≤ 3 ∧
        q ∣ Nat.card (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := by
      rcases hα _ hLb.2.2.2 (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian
        _ hLb.2.2) hLcat with h3d | h5d
      · exact ⟨3, Nat.prime_three, by decide, h.pRank_three_le, h3d⟩
      · exact ⟨5, Nat.prime_five, by decide, h.pRank_five_le, h5d⟩
    obtain ⟨y, hyL, hyq, l, hlL, hyl⟩ := exists_qElement_not_central hq hqdvd
    obtain ⟨g, hg, hinj⟩ := exists_injective_conj_relIndex (barM M W) (barM M L)
    have hidx := le_pRank_of_injective_conj stmtComponentRank stmtBarPRankLift inf_le_right hq
      hq2 hLb (barM_mono hLK) hyL hyq hlL hyl g (fun j => barM_mono hWK (hg j)) hinj
    exact le_of_relIndex_le_four_of_perfect (commutator_barM_eq_self (hWK.trans inf_le_right) hW)
      (hidx.trans (hqK.trans (by norm_num)))

theorem D1A15Data.isSolvable_outer_component (h : D1A15Data P M H R c σ τ)
    (hS : CatalogOuterSolvable) {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hLb : IsComponentOf Lb ⊤) :
    Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer Lb) := by
  have hMtop : M ≠ ⊤ := fun hM => h.surv.ph3.not_le (hM ▸ le_top)
  have hcat : CatalogSimpleSections (↥M ⧸ CFSG.pCore 2 ↥M) :=
    (catalogSimpleSections_of_isKProper h.surv.ph3.glob.kProper M hMtop).quotient _
  have : IsSimpleGroup (↥Lb ⧸ Subgroup.center ↥Lb) := hLb.2.2.2
  have : Group.IsPerfect Lb := ⟨hLb.2.2.1⟩
  have : Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (↥Lb ⧸ Subgroup.center ↥Lb)) :=
    hS _ (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hLb.2.2)
      (hcat.isCatalogGroup_center_quotient hLb)
  exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient Lb

theorem D1A15Data.le_sup_centralizer_component (h : D1A15Data P M H R c σ τ)
    (hB3 : StmtBlockThree) (hα : KFactThreeOrFiveDvd) (hS : CatalogOuterSolvable)
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lb ⊤) :
    barM M R ≤ Lb ⊔ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  obtain ⟨J, hJ, -, hRJ⟩ := h.normal_closure (H ⊓ M) le_rfl Subgroup.le_normalizer
    h.surv.ph3.le_inf
  have hWK : (⨆ i, J i) ≤ H ⊓ M := iSup_le fun i => (hJ i).1
  have hW : ⁅⨆ i, J i, ⨆ i, J i⁆ = ⨆ i, J i := by
    refine le_antisymm ?_ (iSup_le fun i => ?_)
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
        (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
    · calc J i = ⁅J i, J i⁆ := (hJ i).2.1.symm
        _ ≤ ⁅⨆ i, J i, ⨆ i, J i⁆ := Subgroup.commutator_mono (le_iSup J i) (le_iSup J i)
  exact (barM_mono hRJ).trans (perfect_le_sup_centralizer_of_outer
    (h.isSolvable_outer_component hS hLb) (commutator_barM_eq_self (hWK.trans inf_le_right) hW)
    (h.le_normalizer_component hB3 hα hWK hW hLb))

end A15

end CFSG.AGLEmbedding
