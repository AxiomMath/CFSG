module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubRed
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartOne.KC.SymplecticNoninnerPlaneDescent
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1429Sub

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Sporth
open CFSG.RankThree.CASymplecticSubfield CFSG.RankThree.PartOne.KCSpComm
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.UnbalancedCatalog (descentField mem_descentField mem_zpowers_of_fixed)

theorem exists_fixModel_psp {S : Type} [Group S] [Finite S] {r f : ℕ}
    (h : StatedClassicalModel S .PSp r 3 f) {β : MulAut S} (hβ : orderOf β = 3)
    (hout : β ∉ (MulAut.conj : S →* MulAut S).range) {I : Subgroup S} (hI : GLAPComponent 3 (fixSubgroup β) I) :
    ∃ a : ℕ, 1 ≤ a ∧ f = 3 * a ∧ StatedClassicalModel (PSimple 3 I) .PSp r 3 a := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨hadm, K, hfield, hfin, hK, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfin
  have hf : 1 ≤ f := hadm.2.1
  have hr : 2 ≤ r := hadm.2.2.1
  set β' : MulAut (StatedProj (StatedSp r K)) := MulAut.congr θ β with hβ'def
  have hβ'ord : orderOf β' = 3 := by rw [hβ'def, MulEquiv.orderOf_eq]; exact hβ
  have hβ'out : β' ∉ (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range :=
    fun hin => hout ((congr_mem_range_conj_iff θ β).1 hin)
  have hβ'p : β' ^ 3 = 1 := hβ'ord ▸ pow_orderOf_eq_one β'
  have hO := spOuter hp hf hr hK
  have hodd : Odd (orderOf β') := hβ'ord ▸ hp.odd_of_ne_two hp2
  have hE : β' ∈ spSemilinearAutGroup r K :=
    mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd hodd
  have hD : β' ∉ spLinearAutGroup r K := by
    intro hD
    have hrel : (CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) ∣ 2 :=
      hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)
    exact hβ'out (mem_of_pow_eq_one_of_relIndex_dvd_two hrel hp hp2 hD hβ'p)
  obtain ⟨-, σ, hσ, h', -, hβeq⟩ := hO.descent 3 hp β' hE hD hβ'ord
  set a : MulAut (StatedProj (StatedSp r K)) := fieldAut r K σ with ha_def
  set k : Subfield K := descentField σ with hkdef
  obtain ⟨hpf, hkcard⟩ := CFSG.RankThree.PartOne.card_semilinearFixedSubfield hp hf hK hσ
  have hk : Nat.card k = 3 ^ (f / 3) := hkcard
  have hpf' : 3 ≤ f := Nat.le_of_dvd (by omega) hpf
  have hfp : 1 ≤ f / 3 := (Nat.one_le_div_iff (by norm_num)).mpr hpf'
  have hq3' : 3 ≤ 3 ^ (f / 3) := Nat.le_self_pow (by omega) 3
  have hr1 : 1 ≤ r := by omega
  have hodd' : Odd (orderOf σ) := hσ ▸ hp.odd_of_ne_two hp2
  have hfixSub : fixSubgroup a = subfieldFixedGroup K r σ :=
    Subgroup.ext fun x => mem_fixSubgroup.trans (fieldAut_apply_eq_self_iff hr1 hodd' x)
  have hinj : Function.Injective (subfieldSpProj r k) := subfieldSpProj_injective hr1 k
  let eH : StatedProj (StatedSp r k) ≃* subfieldFixedGroup K r σ := MonoidHom.ofInjective hinj
  let eC : ↥(fixSubgroup a) ≃* StatedProj (StatedSp r k) :=
    (MulEquiv.subgroupCongr hfixSub).trans eH.symm
  have hmodel : StatedClassicalModel ↥(fixSubgroup a) .PSp r 3 (f / 3) :=
    ⟨⟨hp, hfp, hr, fun h => by
      have := (Prod.mk.inj h).2
      omega⟩, ↥k, inferInstance, inferInstance, hk, ⟨eC⟩⟩
  obtain ⟨-, hsimpC, hnabC⟩ := finite_simple_nonab_of_model hmodel (Or.inl ⟨rfl, hr⟩)
  have hdvd := dvd_card hmodel (Or.inl ⟨rfl, hr⟩)
  let ψ : S ≃* StatedProj (StatedSp r K) :=
    θ.trans (h'⁻¹ : StatedProj (StatedSp r K) ≃* StatedProj (StatedSp r K))
  have hψ : MulAut.congr ψ β = a := by
    have h1 : MulAut.congr ψ β = h'⁻¹ * β' * h' := by
      ext x
      rfl
    rw [h1, hβeq]
    group
  haveI hnormC := normal_subgroupOf_self (fixSubgroup a)
  obtain ⟨e⟩ := exists_equiv_of_conj ψ hψ (J := fixSubgroup a) le_rfl (isSolvable_quotient_self _)
    hsimpC hnabC hdvd hI
  exact ⟨f / 3, hfp, by omega, hmodel.1, ↥k, inferInstance, inferInstance, hk, ⟨e.trans eC⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.H1429Sub

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremA.H1429Sub

theorem i1429SubSymp_holds : I1429SubLieAt SubIsSymp := by
  intro S _ _ hS hnc d hchar hP ⟨e⟩ β hβ hout I hI hU
  have hord : orderOf β = 3 := orderOf_three_of_not_inner hβ hout
  obtain ⟨d, hv⟩ := d
  rcases hP with ⟨q, rfl⟩ | ⟨n, q, rfl⟩
  · have hq3 : q.p = 3 := by simpa using hchar
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    have hm : StatedClassicalModel S .PSp 2 q.p q.exponent := by
      rcases CFSG.Models.lieModel_B 2 q hv e with hm | hm
      · exact hm.statedClassicalModel_of_ne_zero (by norm_num)
      · exact absurd hm.admissible.2.2.1 (by norm_num)
    rw [hq3] at hm
    obtain ⟨a, ha, hf, hmI⟩ := exists_fixModel_psp hm hord hout hI
    obtain ⟨-, -, ha1⟩ := finish_classical hmI hU
    subst ha1
    refine ⟨.lie ⟨.B 2 q, hv⟩, ?_, ⟨e⟩⟩
    show q.card = 27
    rw [TauCeti.PrimePower.card_def, hq3, hf]
    norm_num
  · have hq3 : q.p = 3 := by simpa using hchar
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    have hm : StatedClassicalModel S .PSp n q.p q.exponent :=
      (CFSG.Models.lieModel_C n q hv e).statedClassicalModel_of_ne_zero (by omega)
    rw [hq3] at hm
    obtain ⟨a, ha, hf, hmI⟩ := exists_fixModel_psp hm hord hout hI
    obtain ⟨-, hn2, -⟩ := finish_classical hmI hU
    omega

end CFSG.LocalAnalysis.GLTheoremA

end
