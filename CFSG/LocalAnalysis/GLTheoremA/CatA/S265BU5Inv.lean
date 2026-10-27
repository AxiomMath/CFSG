module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTy
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTwE6Tr
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTwE6Line
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTwE6Card
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTwE6A4A1
import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct
import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.TE6

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Timmesfeld.CrossChar (twistedE6InndiagConj)
open scoped commutatorElement


theorem twE6U5Inv_holds : TwE6U5Inv := by
  intro X _ _ S a hS hcore hcat ha ha3 hout J hJ hJcat
  have hap : IsPGroup 3 (Subgroup.zpowers a) :=
    CFSG.LocalAnalysis.GLTheoremA.isPGroup_zpowers_of_pow_eq_one ha3
  have hβ3 : chevAut 3 S ⟨a, ha⟩ ^ 3 = 1 := chevAut_pow_eq_one 3 S ha ha3
  have hβ1 : chevAut 3 S ⟨a, ha⟩ ≠ 1 := by
    intro h1
    obtain ⟨-, hcm⟩ := (chevAut_eq_one_iff Nat.prime_three
      (CFSG.HardMathSupport.Timmesfeld.Proving.glaPComponent_self hS hcore) ha).1 h1
    refine hout ⟨1, S.one_mem, ?_⟩
    rw [inv_one, one_mul, Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨y, hy, hys⟩ := hcm (Subgroup.commutator_mem_commutator hs (Subgroup.mem_zpowers a))
    rw [hcore, SetLike.mem_coe, Subgroup.mem_bot] at hy
    exact commutatorElement_eq_one_iff_mul_comm.1 (hys.symm.trans (by simp [hy]))
  obtain ⟨K, _, _, σ, hK, hσ, e, h, hh3, hh1, _D, _i, hβe, -, -, hcomp, ⟨e3⟩⟩ :=
    exists_twE6LineModel_of_glaPComponent hcat hβ3 hβ1
      (glaPComponent_chevTransfer Nat.prime_three ha hap hJ)
  obtain ⟨e0⟩ := nonempty_pSimple_equiv_chevTransfer Nat.prime_three ha hap hJ
  have hb : CatDistinct.OrderBridge := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
  have hc : Nat.card (↥((chevTransfer 3 S J).map e.toMonoidHom) ⧸
      Subgroup.center ↥((chevTransfer 3 S J).map e.toMonoidHom)) = 13685760 := by
    rw [← Nat.card_congr (e0.trans e3).toEquiv]
    exact CatDistinct.card_isU5two hb hJcat
  obtain ⟨t', ht', htJ, htt, ht1⟩ := exists_involution_centralizing_of_dim28 hK hσ hh3 hh1
    (twE6MatFixDim_eq_28_of_card_u5two hK hσ hh3 hh1 hcomp hc) hcomp
  have hvβ : chevAut 3 S ⟨a, ha⟩ (e.symm t') = e.symm t' := by
    have h1 : twistedE6InndiagConj K σ h t' = t' := ht' _ (Subgroup.mem_zpowers _)
    rw [← hβe] at h1
    change e (chevAut 3 S ⟨a, ha⟩ (e.symm t')) = t' at h1
    exact e.injective (h1.trans (e.apply_symm_apply t').symm)
  have hvv : e.symm t' * e.symm t' = 1 := by rw [← map_mul, htt, map_one]
  have hv1 : e.symm t' ≠ 1 := fun h1 => ht1 (e.symm.injective (h1.trans (map_one e.symm).symm))
  have hvJ : ∀ y ∈ chevTransfer 3 S J, y * e.symm t' = e.symm t' * y := by
    intro y hy
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact Subgroup.mem_centralizer_iff.1 htJ (e y) (Subgroup.mem_map_of_mem e.toMonoidHom hy)
  obtain ⟨s, hsv, hss⟩ := exists_mul_self_lift_chevQuotHom hS hcore hvv
  have hsa : a * (s : X) = s * a :=
    conj_eq_of_chevAut_fix_of_mul_self hS hcore ha hss (by rw [hsv]; exact hvβ)
  have hsJ : (s : X) ∈ Subgroup.centralizer (J : Set X) :=
    mem_centralizer_of_commute_chevQuotHom hS hcore (hJ.1.trans inf_le_left)
      (glaPComponent_perfect hJ) fun y hy => by
        rw [hsv]
        exact (hvJ _ (Subgroup.mem_map_of_mem (chevQuotHom 3 S)
          ((Subgroup.mem_subgroupOf).2 hy))).symm
  have hs1 : (s : X) ≠ 1 := fun h1 => hv1 (by rw [← hsv, (Subtype.ext h1 : s = 1), map_one])
  refine ⟨s, Subgroup.mem_inf.2 ⟨s.2, Subgroup.mem_centralizer_singleton_iff.2 hsa.symm⟩, hsJ,
    orderOf_eq_prime ?_ hs1⟩
  rw [sq, ← Subgroup.coe_mul, hss, Subgroup.coe_one]

end CFSG.LocalAnalysis.GLTheoremA.S265.TE6

end
