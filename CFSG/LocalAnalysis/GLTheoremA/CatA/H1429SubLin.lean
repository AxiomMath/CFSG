module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubCore
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.LinearTwo
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubRed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1429Sub

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCLinearSubfield
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.Assembly.LowTwoRank

noncomputable def projSLEquivStated (n : ℕ) (K : Type) [Field K] :
    projectiveSL n K ≃* StatedProj (StatedSL n K) :=
  (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K).symm.trans
    (projectiveSpecialLinearGroupEquivStatedProj n K)

theorem exists_fixModel_psl_ge3 {S : Type} [Group S] [Finite S] {n f : ℕ} (hn : 3 ≤ n)
    (h : StatedClassicalModel S .PSL n 3 f) {β : MulAut S} (hβ : orderOf β = 3)
    (hout : β ∉ (MulAut.conj : S →* MulAut S).range) {I : Subgroup S}
    (hI : GLAPComponent 3 (fixSubgroup β) I) :
    ∃ a : ℕ, 1 ≤ a ∧ f = 3 * a ∧ StatedClassicalModel (PSimple 3 I) .PSL n 3 a := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨hadm, K, hfield, hfin, hK, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfin
  have hf : 1 ≤ f := hadm.2.1
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  haveI : CharP K 3 := finite_field_prime_power_characteristic hp hf hK
  let θ' : S ≃* projectiveSL n K := θ.trans (projSLEquivStated n K).symm
  set β' : MulAut (projectiveSL n K) := MulAut.congr θ' β with hβ'def
  have hβ'ord : orderOf β' = 3 := by rw [hβ'def, MulEquiv.orderOf_eq]; exact hβ
  have hβ'out : β' ∉ innerAut (projectiveSL n K) := fun hin =>
    hout ((congr_mem_range_conj_iff θ' β).1 hin)
  have hβ'p : β' ^ 3 = 1 := hβ'ord ▸ pow_orderOf_eq_one β'
  obtain ⟨τ, h', hτ, hβeq⟩ := exists_conj_fieldAut_of_outer hn hp hp2 hf hK hβ'p hβ'out
  set a : MulAut (projectiveSL n K) := fieldAut n K τ with ha_def
  set k : Subfield K := semilinearFixedSubfield τ with hk_def
  obtain ⟨hpf, hkcard⟩ := card_semilinearFixedSubfield hp hf hK hτ
  have hτp : τ ^ 3 = 1 := hτ ▸ pow_orderOf_eq_one τ
  have hf3 : 3 ≤ f := Nat.le_of_dvd (by omega) hpf
  have hfp : 1 ≤ f / 3 := (Nat.one_le_div_iff (by norm_num)).mpr hf3
  have hq3' : 3 ≤ 3 ^ (f / 3) := Nat.le_self_pow (by omega) 3
  have hC : fixSubgroup a = (linearSubfieldInclusion n k).range :=
    fixSubgroup_fieldAut_eq_range (by omega) hp hτp (not_dvd_card_units_of_card_eq hp hf hK)
  have hinj := linearSubfieldInclusion_injective (by omega : 0 < n) k
  obtain ⟨hsimp, hnab⟩ := simple_nonabelian_range_linearSubfieldInclusion hn k
  have hs : IsSimpleGroup ↥(fixSubgroup a) := by
    rw [hC]
    exact hsimp
  have hnc : ∃ x y : ↥(fixSubgroup a), x * y ≠ y * x := by
    rw [hC]
    by_contra hcon
    push Not at hcon
    exact hnab fun x y => hcon x y
  have hdvd : 3 ∣ Nat.card ↥(fixSubgroup a) := by
    rw [hC, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    refine CFSG.SignalizerFunctorTheorem.CatalogBridge.dvd_card_projectiveSL_of_dvd (by omega) hp ?_
    rw [hkcard]
    exact dvd_pow_self 3 (by omega)
  let eC : ↥(fixSubgroup a) ≃* StatedProj (StatedSL n k) :=
    ((MulEquiv.subgroupCongr hC).trans (MonoidHom.ofInjective hinj).symm).trans (projSLEquivStated n k)
  have hmodel : StatedClassicalModel ↥(fixSubgroup a) .PSL n 3 (f / 3) :=
    ⟨⟨hp, hfp, hn.trans' (by norm_num), fun h => by
      have := (Prod.mk.inj h).2
      omega, fun h => by
      have := (Prod.mk.inj h).1
      omega⟩, ↥k, inferInstance, inferInstance, hkcard, ⟨eC⟩⟩
  let ψ : S ≃* projectiveSL n K := θ'.trans (h'⁻¹ : projectiveSL n K ≃* projectiveSL n K)
  have hψ : MulAut.congr ψ β = a := by
    have h1 : MulAut.congr ψ β = h'⁻¹ * β' * h' := by
      ext x
      rfl
    rw [h1, hβeq]
    group
  haveI hnormC := normal_subgroupOf_self (fixSubgroup a)
  obtain ⟨e⟩ := exists_equiv_of_conj ψ hψ (J := fixSubgroup a) le_rfl (isSolvable_quotient_self _)
    hs hnc hdvd hI
  exact ⟨f / 3, hfp, by omega, hmodel.1, ↥k, inferInstance, inferInstance, hkcard, ⟨e.trans eC⟩⟩

theorem solvable_projectiveSL_two_of_card_three {k : Type} [Field k] [Finite k] (hk3 : Nat.card k = 3) :
    Group.IsSolvable (projectiveSL 2 k) := by
  have hodd3 : Odd (Nat.card k) := by rw [hk3]; exact ⟨1, rfl⟩
  have hcard12 : Nat.card (projectiveSL 2 k) = 12 := by
    rw [Nat.card_congr (projSLEquivStated 2 k).toEquiv,
      CFSG.Open.StatedAPI.card_statedProj_statedSL_two_of_odd hodd3, hk3]
    norm_num
  refine isSolvable_of_card_primeFactors_le_two ?_
  rw [hcard12, show (12 : ℕ) = 2 ^ 2 * 3 ^ 1 by norm_num,
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
  decide

theorem exists_fixModel_psl_two {S : Type} [Group S] [Finite S] {f : ℕ}
    (h : StatedClassicalModel S .PSL 2 3 f) {β : MulAut S} (hβ : orderOf β = 3)
    (hout : β ∉ (MulAut.conj : S →* MulAut S).range) {I : Subgroup S}
    (hI : GLAPComponent 3 (fixSubgroup β) I) :
    ∃ a : ℕ, 1 ≤ a ∧ f = 3 * a ∧ StatedClassicalModel (PSimple 3 I) .PSL 2 3 a := by
  have hp : Nat.Prime 3 := Nat.prime_three
  obtain ⟨hadm, K, hfield, hfin, hK, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfin
  have hf : 1 ≤ f := hadm.2.1
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  haveI : CharP K 3 := finite_field_prime_power_characteristic hp hf hK
  let θ' : S ≃* projectiveSL 2 K := θ.trans (projSLEquivStated 2 K).symm
  set β' : MulAut (projectiveSL 2 K) := MulAut.congr θ' β with hβ'def
  have hβ'ord : orderOf β' = 3 := by rw [hβ'def, MulEquiv.orderOf_eq]; exact hβ
  have hβ'out : β' ∉ innerAut (projectiveSL 2 K) := fun hin =>
    hout ((congr_mem_range_conj_iff θ' β).1 hin)
  obtain ⟨τ, h', hτ, hβeq⟩ := exists_conj_fieldAut_of_outer_two hp hf hK hβ'ord hβ'out
  set a : MulAut (projectiveSL 2 K) := fieldAut 2 K τ with ha_def
  set k : Subfield K := semilinearFixedSubfield τ with hk_def
  obtain ⟨hpf, hkcard⟩ := card_semilinearFixedSubfield hp hf hK hτ
  have hτp : τ ^ 3 = 1 := hτ ▸ pow_orderOf_eq_one τ
  have hf3 : 3 ≤ f := Nat.le_of_dvd (by omega) hpf
  have hfp : 1 ≤ f / 3 := (Nat.one_le_div_iff (by norm_num)).mpr hf3
  have hq3' : 3 ≤ 3 ^ (f / 3) := Nat.le_self_pow (by omega) 3
  have hC : fixSubgroup a = (linearSubfieldInclusion 2 k).range :=
    fixSubgroup_fieldAut_eq_range (by norm_num) hp hτp (not_dvd_card_units_of_card_eq hp hf hK)
  have hinj := linearSubfieldInclusion_injective (by norm_num : 0 < 2) k
  let ψ : S ≃* projectiveSL 2 K := θ'.trans (h'⁻¹ : projectiveSL 2 K ≃* projectiveSL 2 K)
  have hψ : MulAut.congr ψ β = a := by
    have h1 : MulAut.congr ψ β = h'⁻¹ * β' * h' := by
      ext x
      rfl
    rw [h1, hβeq]
    group
  by_cases h3 : 3 ^ (f / 3) = 3
  ·
    exfalso
    have hk3 : Nat.card k = 3 := by rw [hkcard, h3]
    have hsolv := solvable_projectiveSL_two_of_card_three (k := k) hk3
    have hCs : Group.IsSolvable ↥(fixSubgroup a) := by
      rw [hC]
      exact Group.isSolvable_of_isSolvable_injective
        (f := (MonoidHom.ofInjective hinj).symm.toMonoidHom)
        (MonoidHom.ofInjective hinj).symm.injective
    obtain ⟨hI', -⟩ := component_transport ψ hψ hI
    exact false_of_solvable hCs hI'
  · have hk4 : 4 ≤ Nat.card k := by rw [hkcard]; omega
    obtain ⟨hsimp, hnab⟩ := simple_nonabelian_projectiveSL_two hk4
    have hs : IsSimpleGroup ↥(fixSubgroup a) := by
      rw [hC]
      exact (MonoidHom.ofInjective hinj).symm.isSimpleGroup
    have hnc : ∃ x y : ↥(fixSubgroup a), x * y ≠ y * x := by
      rw [hC]
      obtain ⟨x, y, hxy⟩ := hnab
      exact ⟨MonoidHom.ofInjective hinj x, MonoidHom.ofInjective hinj y, fun h =>
        hxy (by simpa using congrArg (MonoidHom.ofInjective hinj).symm h)⟩
    have hdvd : 3 ∣ Nat.card ↥(fixSubgroup a) := by
      rw [hC, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
      refine CFSG.SignalizerFunctorTheorem.CatalogBridge.dvd_card_projectiveSL_of_dvd le_rfl hp ?_
      rw [hkcard]
      exact dvd_pow_self 3 (by omega)
    let eC : ↥(fixSubgroup a) ≃* StatedProj (StatedSL 2 k) :=
      ((MulEquiv.subgroupCongr hC).trans (MonoidHom.ofInjective hinj).symm).trans
        (projSLEquivStated 2 k)
    have hmodel : StatedClassicalModel ↥(fixSubgroup a) .PSL 2 3 (f / 3) :=
      ⟨⟨hp, hfp, le_rfl, fun h => by
        have := (Prod.mk.inj h).2
        omega, fun h => by
        have := (Prod.mk.inj h).2
        omega⟩, ↥k, inferInstance, inferInstance, hkcard, ⟨eC⟩⟩
    haveI hnormC := normal_subgroupOf_self (fixSubgroup a)
    obtain ⟨e⟩ := exists_equiv_of_conj ψ hψ (J := fixSubgroup a) le_rfl (isSolvable_quotient_self _)
      hs hnc hdvd hI
    exact ⟨f / 3, hfp, by omega, hmodel.1, ↥k, inferInstance, inferInstance, hkcard, ⟨e.trans eC⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.H1429Sub

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremA.H1429Sub

theorem i1429SubLin_holds : I1429SubLieAt SubIsLin := by
  intro S _ _ hS hnc d hchar ⟨n, q, hd⟩ ⟨e⟩ β hβ hout I hI hU
  have hord : orderOf β = 3 := orderOf_three_of_not_inner hβ hout
  obtain ⟨d, hv⟩ := d
  cases hd
  have hq3 : q.p = 3 := by simpa using hchar
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hm : StatedClassicalModel S .PSL (n + 1) q.p q.exponent :=
    (CFSG.Models.lieModel_A n q hv e).statedClassicalModel_of_ne_zero (by omega)
  rw [hq3] at hm
  obtain ⟨a, ha, hf, hmI⟩ : ∃ a : ℕ, 1 ≤ a ∧ q.exponent = 3 * a ∧
      StatedClassicalModel (PSimple 3 I) .PSL (n + 1) 3 a := by
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · obtain rfl : n = 1 := by omega
      exact exists_fixModel_psl_two hm hord hout hI
    · exact exists_fixModel_psl_ge3 (by omega) hm hord hout hI
  obtain ⟨ht, -, -⟩ := finish_classical hmI hU
  exact absurd ht (by decide)

end CFSG.LocalAnalysis.GLTheoremA

end
