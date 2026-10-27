module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5Fix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5Four
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5U35M
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatOddUnitary

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.EvenSporadicStandard.SolomonRed CFSG.LocalAnalysis.EvenBN.GMSK
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {Y : Type} [Group Y] {τ : Y}

theorem z2a5_not_U35 [Finite Y] (h : Z2A5Hyp Y τ) {S : Subgroup Y} (hS : FixedData Y S) :
    ¬ LieModel ↥S .PSU 3 5 1 := by
  intro hL
  haveI := hS.normal
  obtain ⟨k, _, _, d⟩ := z2a5_datum h hS
  have hM := OddClassicalRankOne.statedClassicalModel_of_lieModel (by decide) hL
  obtain ⟨hSs, hSnab, hSK', -⟩ := OddClassicalRankOne.subgroupOf_fixedRoot_data le_rfl d.card_eq
    d.le_fixed d.nonempty_mulEquiv
  obtain ⟨-, -, -, -, -, ⟨E, _, hU, θ, A, σ, hx, hAU, hα⟩, hall⟩ :=
    odd_unitary_fixed_root_rankOne_selector k le_rfl
    (by rw [Nat.card_eq_fintype_card, d.card_eq]) _ d.orderOf_eq _ d.normal hSs hSnab hSK'
    (OddClassicalRankOne.two_bound_of_fixedRootRankOne d.le_fixed d.rankOne) 3 5 1 (by decide) hM
  obtain ⟨hσ, -, -, -, hk5, hdim, hbij, Bf, hBf, hs, hnd, Φ, hΦ⟩ :=
    hall E hU θ A σ hx hAU hα
  obtain ⟨g, hg, hg4⟩ := psu35_fixed_order_four hx hσ hk5 hdim hbij Bf hBf hs hnd Φ hΦ
  apply z2a5_eqLocus_no_four h (θ.symm (hypProj hU 1 1 g)) ?_ (by rw [MulEquiv.orderOf_eq, hg4])
  change MulAut.conjNormal τ (θ.symm (hypProj hU 1 1 g)) = θ.symm (hypProj hU 1 1 g)
  apply θ.injective
  have := congrArg (fun φ : MulAut (hypPSU hU 1 1) => φ (hypProj hU 1 1 g)) hα
  rw [MulEquiv.apply_symm_apply]
  change semilinearAutHom hU le_rfl le_rfl ⟨_, hx⟩ (hypProj hU 1 1 g) =
    θ ((MulAut.conjNormal τ : MulAut S) (θ.symm (hypProj hU 1 1 g))) at this
  rw [← this]
  exact hg

end CFSG.OddStandard.SmallF3.Omega
