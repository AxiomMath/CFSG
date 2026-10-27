module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5Fix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5Four
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5L35M
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatOddLinear

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.EvenSporadicStandard.SolomonRed CFSG.LocalAnalysis.EvenBN.GMSK
  CFSG.LocalAnalysis.ComponentInitial

variable {Y : Type} [Group Y] {τ : Y}

theorem z2a5_not_L35 [Finite Y] (h : Z2A5Hyp Y τ) {S : Subgroup Y} (hS : FixedData Y S) :
    ¬ LieModel ↥S .PSL 3 5 1 := by
  intro hL
  haveI := hS.normal
  obtain ⟨k, _, _, d⟩ := z2a5_datum h hS
  have hM := OddClassicalRankOne.statedClassicalModel_of_lieModel (by decide) hL
  obtain ⟨hSs, hSnab, hSK', -⟩ := OddClassicalRankOne.subgroupOf_fixedRoot_data le_rfl d.card_eq
    d.le_fixed d.nonempty_mulEquiv
  obtain ⟨-, -, -, -, -, hall⟩ := odd_higher_linear_fixed_root_rankOne_selector k le_rfl
    (by rw [Nat.card_eq_fintype_card, d.card_eq]) _ d.orderOf_eq _ d.normal hSs hSnab hSK'
    (OddClassicalRankOne.two_bound_of_fixedRootRankOne d.le_fixed d.rankOne) 3 5 1 (by decide)
    le_rfl hM
  obtain ⟨-, F₀, _, _, hF₀, ⟨θ₀⟩⟩ := hM
  let η₀ := θ₀.trans
    (CFSG.ComponentClassification.SymmetricLocal.statedProjEquivProjectiveSL 3 F₀)
  obtain ⟨A, hA, hαA⟩ := hall F₀ hF₀ η₀
  have : Fintype F₀ := Fintype.ofFinite F₀
  obtain ⟨x, hx, hx4⟩ := psl35_graph_fixed_order_four (F := F₀)
    (by rw [← Nat.card_eq_fintype_card, hF₀]; norm_num) A hA
  apply z2a5_eqLocus_no_four h (η₀.symm x) ?_ (by rw [MulEquiv.orderOf_eq, hx4])
  change MulAut.conjNormal τ (η₀.symm x) = η₀.symm x
  apply η₀.injective
  rw [hαA, MulEquiv.apply_symm_apply, hx]

end CFSG.OddStandard.SmallF3.Omega
