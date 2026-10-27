module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Partner
public import CFSG.RankThree.PartOne.AUTSL.CycInv
public import CFSG.RankThree.PartOne.AUTSL.OmegaDickson

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup QuadraticMap Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ClassicalGroups.Orthogonal (elementaryGroup)
open CFSG.RankThree.OrthogonalInvolutions (commSpace)
open CFSG.RankThree.PartOne.AUTSL (mem_matrixDerived_iff_even)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

theorem fixed_centreless_of_le {G : Type} [Group G] {L G₀ : Subgroup G} {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hLS : L ≤ G₀) (htN : t ∈ normalizer (G₀ : Set G))
    (hout : G₀.normalizerMonoidHom ⟨t, htN⟩ ∉ (MulAut.conj : G₀ →* MulAut G₀).range) :
    ∀ y : G₀, G₀.normalizerMonoidHom ⟨t, htN⟩ y = y →
      (∀ z : G₀, G₀.normalizerMonoidHom ⟨t, htN⟩ z = z → z * y = y * z) → y = 1 := by
  intro y hy hz
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hyt : t * (y : G) = (y : G) * t := by
    have h1 := congrArg Subtype.val hy
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
    calc t * (y : G) = t * y * t⁻¹ * t := by group
      _ = (y : G) * t := by rw [h1]
  have hyL : (y : G) ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    have hθl : G₀.normalizerMonoidHom ⟨t, htN⟩ ⟨l, hLS hl⟩ = ⟨l, hLS hl⟩ := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      change t * l * t⁻¹ = l
      rw [← mem_centralizer_iff.1 htC l hl, mul_inv_cancel_right]
    exact congrArg Subtype.val (hz _ hθl)
  have hmem : (y : G) ∈ zpowers t := by
    rw [← hKt]
    exact ⟨hyL, mem_centralizer_singleton_iff.2 hyt.symm⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hk2 : t ^ (k % 2) = (y : G) := by
    rw [← hk]
    have h1 := zpow_mod_orderOf t k
    rw [ht] at h1
    exact_mod_cast h1
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [h0, zpow_zero] at hk2
    exact Subtype.ext hk2.symm
  · rw [h1, zpow_one] at hk2
    exfalso
    have htS : t ∈ G₀ := hk2 ▸ y.2
    apply hout
    rw [normalizerMonoidHom_eq_conj_of_mem htS htN]
    exact ⟨_, rfl⟩

theorem congr_trans_inv_eq {X P : Type*} [Group X] [Group P] (ε : X ≃* P) (β : MulAut P)
    (θ : MulAut X) : MulAut.congr (ε.trans (β⁻¹ : MulAut P)) θ = β⁻¹ * MulAut.congr ε θ * β := by
  ext x
  simp [MulAut.congr_apply]

end CFSG.SeitzReduction.SymplecticPilot
