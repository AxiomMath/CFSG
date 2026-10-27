module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54F3E7Theta
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54F3Defs
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Ord
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Std
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.IVK.L2.Lemma19c
public import CFSG.GH74.GLS.IVK.L2.SylowAux
public import CFSG.GH74.GLS.IVK.L2.Torus
public import CFSG.GH74.GLS.IVK.L2.TorusGeneral
public import CFSG.GH74.GLS.IVK.Prod.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OrdU2
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInitial
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitStep
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35AltConf
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35AltSmall
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54F3Raw
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma36Inputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36AltPerm
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCoreBasics
public import CFSG.LocalAnalysis.ComponentClassification.TBLitStepFour
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.F3

open CFSG Subgroup Assembly.LowTwoRank
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Levi
  CFSG.ClassicalInvolution.ModelFacts.E7Model CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Q3.Q3W


namespace E7Three

local notation "M₇" => E7sc 3 1
local notation "D₇" => e7Datum (GaloisField 3 1)

theorem rawF3_E7sc {t : M₇} (ht : t ∈ center M₇) (ht2 : orderOf t = 2) : RawF3 M₇ t := by
  have : Finite M₇ := by
    have : Finite (Module.End (GaloisField 3 1) (Fin e7Data.d →₀ GaloisField 3 1)) :=
      Module.finite_of_finite (GaloisField 3 1)
    infer_instance
  have hRθF := e7_fund_class3.2
  obtain ⟨u, hu, hu2⟩ := exists_involution_std3 isRoot_thetaE7
  have huZ : u ∉ center M₇ := fun hc => by
    rw [no_central_fund3 hRθF hu hc, orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  obtain ⟨e⟩ := nonempty_theta_equiv3
  obtain ⟨eK⟩ := ClassicalInvolution.nonempty_mulEquiv_sl2Three_of_natCard_eq_three
    (F := GaloisField 3 1) card_gf3
  have hJ₁Z : stdRankOne D₇ thetaE7 ⊓ center M₇ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx₁, hx₂⟩
    exact mem_bot.2 (no_central_fund3 hRθF hx₁ hx₂)
  have hJ₁le := theta_le_centralizer3 hu hu2
  have hn₁ : ∀ g ∈ centralizer {u}, ∀ j ∈ stdRankOne D₇ thetaE7,
      g * j * g⁻¹ ∈ stdRankOne D₇ thetaE7 := by
    intro g hg j hj
    rw [← conjSub_theta3 hu hu2 (Subgroup.mem_centralizer_singleton_iff.1 hg)]
    exact conj_mem_conjSub hj
  have hJ₁n : ((stdRankOne D₇ thetaE7).subgroupOf (centralizer {u})).Normal :=
    (Subgroup.normal_subgroupOf_iff hJ₁le).2 fun j a hj ha => hn₁ a ha j hj
  obtain ⟨hQ₂, hZ₂, hL₂⟩ := hj_facts3
  have htJ : t ∈ HJ 3 1 := E7Row.center_le_HJ ht
  have ht2' : orderOf (⟨t, htJ⟩ : ↥(HJ 3 1)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact ht2
  have hn₂ : ∀ g ∈ centralizer {u}, ∀ j ∈ HJ 3 1, g * j * g⁻¹ ∈ HJ 3 1 := fun g hg j hj =>
    conjSub_HJ_le3 hu hu2 (Subgroup.mem_centralizer_singleton_iff.1 hg) (conj_mem_conjSub hj)
  exact ⟨u, hu2, huZ, stdRankOne D₇ thetaE7, HJ 3 1, hJ₁le, hJ₁n.isSubnormal, hu, hJ₁Z,
    ⟨e.trans eK⟩,
    .inl ⟨E7Row.isTwoComponentIn_of_normalizes (HJ_le_centralizer3 hu) hn₂
      (E7Row.isTwoQuasisimple_of_quasisimple hQ₂ hZ₂ ht2'), hQ₂, .POmegaPlus, 6, hL₂⟩,
    .inl htJ⟩

end E7Three

theorem rowE7Three : RowE7Three := by
  intro Y _ _ hY hZ τ n hτ hL _ t ht2 htZ
  obtain rfl : τ = .E7 := hτ
  obtain ⟨e⟩ := E7Three.nonempty_mulEquiv_E7sc_three hY hZ hL ht2 htZ
  have hc : e.symm t ∈ center (E7sc 3 1) := by
    rw [← Subgroup.map_center_eq e.symm]
    exact mem_map_of_mem _ htZ
  have h2 : orderOf (e.symm t) = 2 := by rw [MulEquiv.orderOf_eq, ht2]
  have hk : (e : E7sc 3 1 →* Y).ker ≤ center (E7sc 3 1) := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
    exact bot_le
  have h := (E7Three.rawF3_E7sc hc h2).concl3 (LieType.CurtisTits.isQuasisimple_e7 _)
    e.surjective hk (by simpa using ht2) hc
  simpa using h

end CFSG.ComponentClassification.HarrisLit.T1.P54.F3
