module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthChev
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthGeneric
public import CFSG.RankThree.PartOne.KC.SymplecticNoninnerPlaneDescent

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Sporth

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export
open CFSG.RankThree.CASymplecticSubfield CFSG.RankThree.PartOne.KCSpComm
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.UnbalancedCatalog (descentField mem_descentField
  mem_zpowers_of_fixed)
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

section Sp

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem sp_fixing_le_zpowers (hK2 : ringChar K ≠ 2) (hr : 2 ≤ r) (σ : K ≃+* K) :
    ∀ w : MulAut (StatedProj (StatedSp r K)),
      (∀ x ∈ subfieldFixedGroup K r σ, w x = x) → w ∈ Subgroup.zpowers (fieldAut r K σ) := by
  intro w hw
  have hr1 : 1 ≤ r := by omega
  obtain ⟨A, τ, rfl⟩ := (odd_symplectic_automorphism_semilinear_representation hK2 hr).1 w
  obtain ⟨heq, hτ⟩ := eq_fieldAut_of_fixes hr1 (k := descentField σ) A τ hw
  rw [heq]
  have hτσ : τ ∈ Subgroup.zpowers σ :=
    mem_zpowers_of_fixed fun x hx => hτ x (mem_descentField.mpr hx)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτσ
  exact ⟨n, (map_zpow (fieldAut r K) σ n).symm⟩

theorem outerCentData_fieldAut_sp {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hr : 2 ≤ r) (hK : Nat.card K = p ^ f) {σ : K ≃+* K} (hσ : orderOf σ = p)
    (hout : fieldAut r K σ ∉ innerAut (StatedProj (StatedSp r K))) :
    OuterCentData p (fieldAut r K σ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hr1 : 1 ≤ r := by omega
  haveI : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  set a : MulAut (StatedProj (StatedSp r K)) := fieldAut r K σ with ha_def
  set k : Subfield K := descentField σ with hkdef
  obtain ⟨hpf, hkcard⟩ := CFSG.RankThree.PartOne.card_semilinearFixedSubfield hp hf hK hσ
  have hk : Nat.card k = p ^ (f / p) := hkcard
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpf' : p ≤ f := Nat.le_of_dvd (by omega) hpf
  have hfp : 1 ≤ f / p := (Nat.one_le_div_iff hp.pos).mpr hpf'
  have hq3 : 3 ≤ p ^ f := hp3.trans (Nat.le_self_pow (by omega) p)
  have hq3' : 3 ≤ p ^ (f / p) := hp3.trans (Nat.le_self_pow (by omega) p)
  have hmodelT : StatedClassicalModel (StatedProj (StatedSp r K)) .PSp r p f :=
    ⟨⟨hp, hf, hr, fun h => by
      have := (Prod.mk.inj h).2
      omega⟩, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, hTsimp, hTnab⟩ := finite_simple_nonab_of_model hmodelT (Or.inl ⟨rfl, hr⟩)
  haveI := hTsimp
  have hZ : Subgroup.center (StatedProj (StatedSp r K)) = ⊥ := b3Lie_center_eq_bot hTnab
  have hodd : Odd (orderOf σ) := hσ ▸ hp.odd_of_ne_two hp2
  have hfixSub : fixSubgroup a = subfieldFixedGroup K r σ :=
    Subgroup.ext fun x => mem_fixSubgroup.trans (fieldAut_apply_eq_self_iff hr1 hodd x)
  have hinj : Function.Injective (subfieldSpProj r k) := subfieldSpProj_injective hr1 k
  let eH : StatedProj (StatedSp r k) ≃* subfieldFixedGroup K r σ := MonoidHom.ofInjective hinj
  let eC : ↥(fixSubgroup a) ≃* StatedProj (StatedSp r k) :=
    (MulEquiv.subgroupCongr hfixSub).trans eH.symm
  have hmodel : StatedClassicalModel ↥(fixSubgroup a) .PSp r p (f / p) :=
    ⟨⟨hp, hfp, hr, fun h => by
      have := (Prod.mk.inj h).2
      omega⟩, ↥k, inferInstance, inferInstance, hk, ⟨eC⟩⟩
  obtain ⟨-, hsimpC, hnabC⟩ := finite_simple_nonab_of_model hmodel (Or.inl ⟨rfl, hr⟩)
  have ha : a ^ p = 1 := by
    rw [ha_def, ← map_pow, ← hσ, pow_orderOf_eq_one, map_one]
  haveI hnormC := normal_subgroupOf_self (fixSubgroup a)
  refine OuterCentData.of_fieldType hp ha hout hZ (J := fixSubgroup a) le_rfl
    hnormC (isSolvable_quotient_self _) hsimpC hnabC
    (isChevSimple_of_psp hp2 hmodel) (dvd_card hmodel (Or.inl ⟨rfl, hr⟩))
    (not_isLTwoTwentySeven hmodel (Or.inl ⟨rfl, hr⟩)) ?_
  intro w hw
  exact sp_fixing_le_zpowers hK2 hr σ w fun x hx => hw x (hfixSub ▸ hx)

end Sp

section Psp

theorem outerCentData_psp {S : Type} [Group S] [Finite S] {r p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : StatedClassicalModel S .PSp r p f) {β : MulAut S} (hβ : orderOf β = p)
    (hout : β ∉ innerAut S) : OuterCentData p β := by
  obtain ⟨hadm, K, hfield, hfin, hK, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfin
  have hf : 1 ≤ f := hadm.2.1
  have hr : 2 ≤ r := hadm.2.2.1
  refine OuterCentData.of_congr hp θ ?_
  set β' : MulAut (StatedProj (StatedSp r K)) := MulAut.congr θ β with hβ'def
  have hβ'ord : orderOf β' = p := by rw [hβ'def, MulEquiv.orderOf_eq]; exact hβ
  have hβ'out : β' ∉ innerAut (StatedProj (StatedSp r K)) := fun hin =>
    hout ((congr_mem_innerAut_iff θ β).1 hin)
  have hβ'p : β' ^ p = 1 := hβ'ord ▸ pow_orderOf_eq_one β'
  have hO := spOuter hp hf hr hK
  have hodd : Odd (orderOf β') := hβ'ord ▸ hp.odd_of_ne_two hp2
  have hE : β' ∈ spSemilinearAutGroup r K :=
    mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd hodd
  have hD : β' ∉ spLinearAutGroup r K := by
    intro hD
    have := inner_normal (StatedProj (StatedSp r K))
    have hrel : (inner (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) ∣ 2 :=
      hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)
    exact hβ'out (mem_of_pow_eq_one_of_relIndex_dvd_two hrel hp hp2 hD hβ'p)
  obtain ⟨-, σ, hσ, h', -, hβeq⟩ := hO.descent p hp β' hE hD hβ'ord
  have hout_a : fieldAut r K σ ∉ innerAut (StatedProj (StatedSp r K)) := by
    intro hin
    have := inner_normal (StatedProj (StatedSp r K))
    apply hβ'out
    rw [hβeq]
    exact this.conj_mem _ hin h'
  have hdata := outerCentData_fieldAut_sp hp hp2 hf hr hK hσ hout_a
  refine OuterCentData.of_conj hp h'⁻¹ β' ?_
  have : h'⁻¹ * β' * h'⁻¹⁻¹ = fieldAut r K σ := by
    rw [hβeq]
    group
  rw [this]
  exact hdata

end Psp

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Sporth
