module

public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Gen
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.LinearTwo

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KDCentre

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCLinearSubfield
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export
  (exists_conj_fieldAut_of_outer_two fixSubgroup_fieldAut_eq_range not_dvd_card_units_of_card_eq
    noComponent_of_solvable)

theorem not_glaPComponent_fixSubgroup_of_l227 {S : Type} [Group S] [Finite S]
    (h : CFSG.HardMathSupport.Solomon.Coordinator.IsLTwoTwentySeven S) {β : MulAut S}
    (hβ : orderOf β = 3) (hout : β ∉ CFSG.HardMathSupport.Solomon.LocalBalance.innerAut S) :
    ∀ I : Subgroup S, ¬ GLAPComponent 3 (fixSubgroup β) I := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let eS : projectiveSL 2 F ≃* CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSL 2 F) :=
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 F).symm.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F)
  let e' : S ≃* projectiveSL 2 F := e.trans eS.symm
  have hK : Nat.card F = 3 ^ 3 := by
    rw [hF]
    norm_num
  have hβ' : orderOf (MulAut.congr e' β) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact hβ
  have hout' : MulAut.congr e' β ∉
      CFSG.HardMathSupport.Solomon.LocalBalance.innerAut (projectiveSL 2 F) := by
    rintro ⟨g, hg⟩
    apply hout
    refine ⟨e'.symm g, ?_⟩
    apply (MulAut.congr e').injective
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e'.apply_symm_apply]
    exact hg
  obtain ⟨τ, g, hτ, hβeq⟩ :=
    exists_conj_fieldAut_of_outer_two Nat.prime_three (by norm_num) hK hβ' hout'
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CharP F 3 := finite_field_prime_power_characteristic Nat.prime_three (by norm_num) hK
  set k : Subfield F := semilinearFixedSubfield τ with hk_def
  obtain ⟨-, hkcard⟩ := card_semilinearFixedSubfield Nat.prime_three (by norm_num) hK hτ
  have hτp : τ ^ 3 = 1 := hτ ▸ pow_orderOf_eq_one τ
  have hC : fixSubgroup (fieldAut 2 F τ) = (linearSubfieldInclusion 2 k).range :=
    fixSubgroup_fieldAut_eq_range (by norm_num) Nat.prime_three hτp
      (not_dvd_card_units_of_card_eq Nat.prime_three (by norm_num) hK)
  have hinj := linearSubfieldInclusion_injective (by norm_num : 0 < 2) k
  have hk3 : Nat.card k = 3 := hkcard.trans (by norm_num)
  have hsolv : Group.IsSolvable (projectiveSL 2 k) := by
    let eSk : projectiveSL 2 k ≃* CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSL 2 k) :=
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 k).symm.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 k)
    have hodd3 : Odd (Nat.card k) := by
      rw [hk3]
      exact ⟨1, rfl⟩
    have hcard12 : Nat.card (projectiveSL 2 k) = 12 := by
      rw [Nat.card_congr eSk.toEquiv,
        CFSG.Open.StatedAPI.card_statedProj_statedSL_two_of_odd hodd3, hk3]
      norm_num
    refine isSolvable_of_card_primeFactors_le_two ?_
    rw [hcard12, show (12 : ℕ) = 2 ^ 2 * 3 ^ 1 by norm_num,
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
    decide
  have hCs : Group.IsSolvable ↥(fixSubgroup (fieldAut 2 F τ)) := by
    rw [hC]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (MonoidHom.ofInjective hinj).symm.toMonoidHom)
      (MonoidHom.ofInjective hinj).symm.injective
  have hmem : ∀ s : ↥(fixSubgroup β),
      (g⁻¹ : MulAut (projectiveSL 2 F)) (e' s) ∈ fixSubgroup (fieldAut 2 F τ) := by
    intro s
    rw [mem_fixSubgroup]
    have hs : β s = s := s.2
    have h1 : MulAut.congr e' β (e' s) = e' s := by
      simp [MulAut.congr_apply, hs]
    rw [hβeq, MulAut.mul_apply, MulAut.mul_apply] at h1
    have h2 := congrArg (⇑(g⁻¹ : MulAut (projectiveSL 2 F))) h1
    rwa [MulAut.inv_apply_self] at h2
  let ψ : ↥(fixSubgroup β) →* ↥(fixSubgroup (fieldAut 2 F τ)) :=
    ((g⁻¹ : MulAut (projectiveSL 2 F)).toMonoidHom.comp
      (e'.toMonoidHom.comp (fixSubgroup β).subtype)).codRestrict _ hmem
  have hψ : Function.Injective ψ := by
    intro a b hab
    have h3 : (g⁻¹ : MulAut (projectiveSL 2 F)) (e' a) =
        (g⁻¹ : MulAut (projectiveSL 2 F)) (e' b) := congrArg Subtype.val hab
    exact Subtype.ext (e'.injective ((g⁻¹ : MulAut (projectiveSL 2 F)).injective h3))
  have hCβ : Group.IsSolvable ↥(fixSubgroup β) := Group.isSolvable_of_isSolvable_injective hψ
  exact noComponent_of_solvable hCβ

end CFSG.LocalAnalysis.GLTheoremA.KDCentre
