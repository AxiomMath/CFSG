module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubCore
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SuzukiReeTits
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSmallReeDescent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubRed
public import CFSG.RankThree.Chevalley.SteinbergCFSmallReeComponentCores

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1429Sub

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open scoped commutatorElement


theorem exists_simple_normal_reeGamma {S : Type} [Group S] {β : MulAut S} {b : ℕ} {k : Type}
    [Field k] [Finite k] [CharP k ReeTag.G2.prime] (hk : Nat.card k = 3 ^ (2 * b + 1))
    (eC : ↥(fixSubgroup β) ≃* ReeTag.G2.reeGamma k b) :
    ∃ M : Subgroup S, M ≤ fixSubgroup β ∧ ∃ _ : (M.subgroupOf (fixSubgroup β)).Normal,
      Group.IsSolvable (↥(fixSubgroup β) ⧸ M.subgroupOf (fixSubgroup β)) ∧ IsSimpleGroup ↥M ∧
      (∃ x y : ↥M, x * y ≠ y * x) ∧ 3 ∣ Nat.card ↥M ∧
      (Nat.card ↥M = 504 ∨ 3 ^ 9 ∣ Nat.card ↥M) := by
  have : Finite (ModGL ReeTag.G2.tag k) := finite_modGL
  set C := fixSubgroup β with hC
  set D := commutator ↥C with hD
  set M := D.map C.subtype with hM
  have hNC : M.subgroupOf C = D := Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  let eD : ↥D ≃* ↥(commutator (ReeTag.G2.reeGamma k b)) :=
    (D.equivMapOfInjective eC.toMonoidHom eC.injective).trans
      (MulEquiv.subgroupCongr
        (CFSG.ComponentClassification.CatalogueBSmallRee.map_commutator_mulEquiv eC))
  let eMD : ↥D ≃* ↥M := D.equivMapOfInjective C.subtype C.subtype_injective
  let eM : ↥M ≃* ↥(commutator (ReeTag.G2.reeGamma k b)) := eMD.symm.trans eD
  obtain ⟨hs, hnc, -, -, -, -⟩ :=
    CFSG.ComponentClassification.CatalogueBSmallRee.small_Ree_whole_group_p_components b k hk
  haveI hMn : (M.subgroupOf C).Normal := by
    rw [hNC]
    infer_instance
  refine ⟨M, Subgroup.map_subtype_le _, hMn, ?_, eM.isSimpleGroup, ?_, ?_, ?_⟩
  · refine Group.isSolvable_of_comm fun x y => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hNC]
    have h1 : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by simp [commutatorElement_def, mul_assoc]
    rw [h1, hD, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨eM.symm x, eM.symm y, fun h => hxy (by simpa using congrArg eM h)⟩
  · rw [Nat.card_congr eM.toEquiv]
    exact SuzukiReeTits.three_dvd_card_commutator_reeGamma b k hk
  · rcases Nat.eq_zero_or_pos b with rfl | hb
    · left
      obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
      obtain ⟨-, -, -, -, hzero, -⟩ :=
        CFSG.ComponentClassification.CatalogueBSmallRee.small_Ree_whole_group_p_components 0 k hk
      obtain ⟨-, h504, -⟩ := hzero rfl w₀ hw₀
      rw [Nat.card_congr eM.toEquiv]
      exact h504
    · right
      obtain ⟨htop, -, -⟩ :=
        CFSG.ComponentClassification.CatalogueBSmallRee.reeGamma_G2_simple hb k hk
      rw [Nat.card_congr eM.toEquiv, htop, Subgroup.card_top,
        CFSG.ComponentClassification.LiteratureLocal.G2_card_reeGamma b hk]
      have h9 : 3 ^ 9 ∣ (3 ^ (2 * b + 1)) ^ 3 := by
        rw [← pow_mul]
        exact pow_dvd_pow 3 (by omega)
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right h9 _) _

theorem false_of_reeGamma {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) {S : Type} [Group S] [Finite S]
    (θ : S ≃* ReeTag.G2.reeGamma K a) {β : MulAut S} (hβ : orderOf β = 3)
    (hout : β ∉ (MulAut.conj : S →* MulAut S).range) {I : Subgroup S}
    (hI : GLAPComponent 3 (fixSubgroup β) I) (hU : Nat.card (PSimple 3 I) = 25920) : False := by
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  set β' : MulAut (ReeTag.G2.reeGamma K a) := MulAut.congr θ β with hβ'def
  have hβ'ord : orderOf β' = 3 := by rw [hβ'def, MulEquiv.orderOf_eq]; exact hβ
  have hβ'3 : β' ^ 3 = 1 := by rw [← hβ'ord]; exact pow_orderOf_eq_one β'
  have hβ'out : β' ∉ innerAut (ReeTag.G2.reeGamma K a) := fun hin =>
    hout ((congr_mem_range_conj_iff θ β).1 hin)
  obtain ⟨-, δ, σ, hσ, hδ, -, -⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.small_Ree_odd_prime_field_descent a ha K hK
      Nat.prime_three (by norm_num) β' hβ'3 hβ'out
  obtain ⟨b, -, hk, hchar, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.reeG2_fixed_data hK Nat.prime_three
      (by norm_num) hσ
  haveI := hchar
  let eC' : ↥(fixSubgroup (ReeTag.G2.reeGammaFieldAut K a σ)) ≃*
      ReeTag.G2.reeGamma (fixSubfield σ) b :=
    (MulEquiv.subgroupCongr (SuzukiReeTits.fixSubgroup_eq_fixSub _)).trans eC
  obtain ⟨M, hMC, hMn, hMsol, hMs, hMnc, hMdvd, hMcard⟩ := exists_simple_normal_reeGamma hk eC'
  haveI := hMn
  let ψ : S ≃* ReeTag.G2.reeGamma K a :=
    θ.trans (δ : ReeTag.G2.reeGamma K a ≃* ReeTag.G2.reeGamma K a)
  have hψ : MulAut.congr ψ β = ReeTag.G2.reeGammaFieldAut K a σ := by
    have h1 : MulAut.congr ψ β = δ * β' * δ⁻¹ := by
      ext x
      rfl
    rw [h1, hδ]
  obtain ⟨e⟩ := exists_equiv_of_conj ψ hψ hMC hMsol hMs hMnc hMdvd hI
  have hc : Nat.card ↥M = 25920 := by rw [← hU]; exact (Nat.card_congr e.toEquiv).symm
  rcases hMcard with h | h
  · omega
  · rw [hc] at h
    norm_num at h

end CFSG.LocalAnalysis.GLTheoremA.H1429Sub

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.H1429Sub
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree


theorem i1429SubRee_holds : I1429SubLieAt SubIsRee := by
  intro S _ _ hS hnc d hchar ⟨m, hd⟩ ⟨e⟩ β hβ hout I hI hU
  have hord : orderOf β = 3 := orderOf_three_of_not_inner hβ hout
  obtain ⟨d, hv⟩ := d
  cases hd
  exfalso
  obtain ⟨a, K, _, _, _, ha, hK, ⟨e'⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_reeGamma_G2_of_reeTitsModel
      (CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m ⟨hv, ⟨e⟩⟩)
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  exact false_of_reeGamma ha hK e' hord hout hI (I1431Z.card_eq_of_u4two hU)

end CFSG.LocalAnalysis.GLTheoremA

end
