module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieRF4Field
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieRF4SLayer
import CFSG.HardMathSupport.Dickson.SuzukiReeB.LargeRee
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain
import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwisted
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i
import CFSG.RankThree.PartOne.KLC.Transport
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLie

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

open CFSG.LieType.Ree (ReeTag)

open CFSG.LocalAnalysis.GLTheoremA.LevelLieRF4SLayer
open scoped commutatorElement

private theorem rf4_suzuki_two_valid : (TauCeti.LieTypeIndex.suzuki 2).Valid := by
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  norm_num

private theorem rf4_suzuki_simple
    (hv : (TauCeti.LieTypeIndex.suzuki 2).Valid) :
    IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group ∧
      ∃ a b : (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group, a * b ≠ b * a := by
  obtain ⟨-, a, ha, K, _, _, hf, hK', ⟨θ⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index 2 hv
  have ha2 : a = 2 := by omega
  subst ha2
  obtain ⟨-, hsimp, hncSz⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suzukiGroup_simple_nonab (b := 2)
      (by norm_num) hK'
  refine ⟨(MulEquiv.isSimpleGroup_congr θ).mpr hsimp, ?_⟩
  obtain ⟨x, y, hxy⟩ := hncSz
  exact ⟨θ.symm x, θ.symm y, fun h => hxy (by simpa using congrArg θ h)⟩

section Cert

set_option linter.unusedSectionVars false


theorem rf4_five_component_level
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * 2 + 1))
    (hv : (TauCeti.LieTypeIndex.reeF4 2).Valid)
    (e : (TauCeti.CFSGIndex.lie ⟨.reeF4 2, hv⟩).Group ≃* ReeTag.F4.reeGamma K 2)
    (x : ReeTag.F4.reeGamma K 2) (hx : orderOf x = 5) (I : Subgroup (ReeTag.F4.reeGamma K 2))
    (hI : GLAPComponent 5 (fixSubgroup (MulAut.conj x)) I) :
    kLevel 5 (PSimple 5 I) ≤ 2 := by
  classical
  haveI : Finite (ReeTag.F4.reeGamma K 2) := Subtype.finite
  have hsimp : IsSimpleGroup (ReeTag.F4.reeGamma K 2) :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 (b := 2) (by norm_num) hK
  have hΓ := (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
    2 K hK).1
  have hnc : ∃ a b : ReeTag.F4.reeGamma K 2, a * b ≠ b * a := by
    apply rf4_nonab_of_not_prime
    intro hp
    have h2 : 2 ∣ Nat.card (ReeTag.F4.reeGamma K 2) := by
      rw [hΓ]
      norm_num
    rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h
    · norm_num at h
    · rw [hΓ] at h
      norm_num at h
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    norm_num at hx
  have hβ : MulAut.conj x ^ 5 = 1 := by
    rw [← map_pow, show x ^ 5 = 1 from by rw [← hx]; exact pow_orderOf_eq_one x, map_one]
  have hβ1 : MulAut.conj x ≠ 1 := by
    intro h
    have hcen : x ∈ Subgroup.center (ReeTag.F4.reeGamma K 2) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg := DFunLike.congr_fun h g
      simp only [MulAut.conj_apply, MulAut.one_apply] at hg
      rw [mul_inv_eq_iff_eq_mul] at hg
      exact hg.symm
    rw [CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hnc, Subgroup.mem_bot] at hcen
    exact hx1 hcen
  have hPIL : CFSG.HardMathSupport.Solomon.Coordinator.PerfectInLayer (MulAut.conj x) :=
    CFSG.HardMathSupport.Dickson.SuzukiReeB.perfectInLayer_reeF4 2 hv hnc ⟨e.symm⟩
      (by norm_num : Nat.Prime 5) (by norm_num) hβ hβ1
  have hle : I ≤ CFSG.Open.GLALayer (fixSubgroup (MulAut.conj x)) :=
    hPIL I hI.1 (glaPComponent_perfect hI)
  obtain ⟨hcomp, hnot⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hI hle
  rw [CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj x] at hcomp hnot hI
  set C : Subgroup (ReeTag.F4.reeGamma K 2) :=
    Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K 2)) with hCdef
  obtain ⟨N, hN, hT⟩ := largeRee_typed (a := 2) (by norm_num) hK (by norm_num : Nat.Prime 5)
    (by norm_num) x hx
  have hIN : I = N := hN I (isComponentOf_rankThree_of_open hcomp)
  have hIq : CFSG.Open.IsQuasisimple ↥I := hcomp.2.2
  have hIne : I ≠ ⊥ := glaPComponent_ne_bot' hI
  have hIC : I ≤ C := hcomp.1
  have hconj : ∀ g ∈ C, ∀ n ∈ I, g * n * g⁻¹ ∈ I := by
    intro g hg n hn
    have hC : C.map (MulAut.conj g).toMonoidHom = C := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact C.mul_mem (C.mul_mem hg hz) (C.inv_mem hg)
      · intro hy
        refine ⟨g⁻¹ * y * g, C.mul_mem (C.mul_mem (C.inv_mem hg) hy) hg, ?_⟩
        show g * (g⁻¹ * y * g) * g⁻¹ = y
        group
    have h1 := CFSG.RankThree.PartOne.KLC.isComponentOf_map_mulEquiv' (MulAut.conj g)
      (isComponentOf_rankThree_of_open hcomp)
    rw [hC] at h1
    have h2 : I.map (MulAut.conj g).toMonoidHom = I := (hN _ h1).trans hIN.symm
    rw [← h2]
    exact ⟨n, hn, rfl⟩
  have hInorm : (I.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff hIC).2 fun h k hh hk => hconj k hk h hh
  rw [← hIN] at hT
  rcases hT with hbot | hSL | hSz
  · exact absurd hbot hIne
  ·
    exfalso
    obtain ⟨eSL⟩ := hSL
    have hcard : Nat.card ↥I = 32736 := by
      rw [← Nat.card_congr eSL.toEquiv, CFSG.OrderReductions.LinearOrders.card_specialLinear K 2
        (by norm_num), hK]
      norm_num
    have hcop : Nat.Coprime 5 (Nat.card ↥(I.subgroupOf C)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIC).toEquiv, hcard]
      norm_num
    have hsub : I.subgroupOf C ≤ CFSG.pPrimeCore 5 ↥C := le_sSup ⟨hInorm, hcop⟩
    apply hnot
    have h3 := Subgroup.map_mono (f := C.subtype) hsub
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hIC] at h3
    exact h3
  ·
    obtain ⟨eSz⟩ := hSz
    have hszV : (TauCeti.LieTypeIndex.suzuki 2).Valid := rf4_suzuki_two_valid
    obtain ⟨g⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_suzukiGroup_equiv_cat
      (b := 2) (by norm_num) hK
    let f : ↥I ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hszV⟩).Group := eSz.symm.trans g
    obtain ⟨hszS, hszNc⟩ := rf4_suzuki_simple hszV
    haveI hIs : IsSimpleGroup ↥I := (MulEquiv.isSimpleGroup_congr f).mpr hszS
    have hncI : ∃ a b : ↥I, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hszNc
      exact ⟨f.symm a, f.symm b, fun h => hab (by simpa using congrArg f h)⟩
    have hZI : Subgroup.center ↥I = ⊥ :=
      CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hncI
    obtain ⟨g1⟩ := rf4_pSimple_equiv_center (by norm_num : Nat.Prime 5) hI hIq
    let g2 : (↥I ⧸ Subgroup.center ↥I) ≃* ↥I :=
      (QuotientGroup.quotientMulEquivOfEq hZI).trans QuotientGroup.quotientBot
    exact rf4_kLevel_le_two ⟨TauCeti.CFSGIndex.lie ⟨.suzuki 2, hszV⟩, by simp [k2, k2Lie],
      ⟨g1.trans (g2.trans f)⟩⟩

theorem rf4_downLe_five_typed (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * 2 + 1)) (hv : (TauCeti.LieTypeIndex.reeF4 2).Valid)
    (e : (TauCeti.CFSGIndex.lie ⟨.reeF4 2, hv⟩).Group ≃* ReeTag.F4.reeGamma K 2)
    (hk : kLevel 5 (ReeTag.F4.reeGamma K 2) ≤ 2) :
    DownLe 5 2 (ReeTag.F4.reeGamma K 2) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hsimp : IsSimpleGroup (ReeTag.F4.reeGamma K 2) :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 (b := 2) (by norm_num) hK
  haveI : Finite (ReeTag.F4.reeGamma K 2) := Subtype.finite
  have hΓ := (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
    2 K hK).1
  have hdvd : 5 ∣ Nat.card (ReeTag.F4.reeGamma K 2) := by
    rw [hΓ]
    norm_num
  have hnc : ∃ a b : ReeTag.F4.reeGamma K 2, a * b ≠ b * a := by
    apply rf4_nonab_of_not_prime
    intro hp
    have h2 : 2 ∣ Nat.card (ReeTag.F4.reeGamma K 2) := by
      rw [hΓ]
      norm_num
    rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h
    · norm_num at h
    · rw [hΓ] at h
      norm_num at h
  intro α hα I hI
  by_cases h1 : α = 1
  · subst h1
    exact rf4_claim_one (by norm_num : Nat.Prime 5) hnc hdvd hk I hI
  · rcases CFSG.HardMathSupport.Solomon.Coordinator.LieComp.reeF4_inner_or_field (a := 2)
        (by norm_num) hK (by norm_num : Nat.Prime 5) hα h1 with
      ⟨x, rfl, hx5, hx1⟩ | ⟨σ, g, hσ, rfl⟩
    · exact rf4_five_component_level hK hv e x (orderOf_eq_prime hx5 hx1) I hI
    · rw [show MulAut.conj g * ReeTag.F4.reeGammaFieldAut K 2 σ * (MulAut.conj g)⁻¹ =
          MulAut.congr (MulAut.conj g : ReeTag.F4.reeGamma K 2 ≃* ReeTag.F4.reeGamma K 2)
            (ReeTag.F4.reeGammaFieldAut K 2 σ) from (rf4_congr_self _ _).symm] at hI
      exact rf4_claim_congr (by norm_num : Nat.Prime 5)
        (MulAut.conj g : ReeTag.F4.reeGamma K 2 ≃* ReeTag.F4.reeGamma K 2) _
        (rf4_claim_field hK (by norm_num : Nat.Prime 5) (by norm_num) (by norm_num) (Or.inr rfl)
          σ hσ) I hI

theorem kdLieRowReeF4ThirtyTwoFive_holds : KDLieRowReeF4ThirtyTwoFive := by
  unfold KDLieRowReeF4ThirtyTwoFive
  intro hv
  have hR := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_twistedF4_of_index 2 hv
    (MulEquiv.refl _)
  obtain ⟨-, a, ha, hfa, K, _, _, _, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma hR
  obtain rfl : a = 2 := by omega
  have hk : kLevel 5 (ReeTag.F4.reeGamma K 2) ≤ 2 := by
    rw [← kLevel_congr 5 e]
    exact rf4_kLevel_le_two ⟨TauCeti.CFSGIndex.lie ⟨.reeF4 2, hv⟩, by simp [k2, k2Lie],
      ⟨MulEquiv.refl _⟩⟩
  exact downLe_of_mulEquiv e.symm (rf4_downLe_five_typed K hK hv e hk)

end Cert

end CFSG.LocalAnalysis.GLTheoremA
