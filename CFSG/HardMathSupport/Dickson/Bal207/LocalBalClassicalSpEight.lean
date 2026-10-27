module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalSpCent
import CFSG.HardMathSupport.Dickson.Bal207.CoreFreeInner
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.OrthOuterThreeAux.SympPrimeSubfieldOdd
import CFSG.RankThree.Classical.SteinbergR3EHigherSymplecticOuterOrder
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalInner

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.RankThree.CASymplecticSubfield CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

section Outer

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem outer_conj_fieldAut_eight (hr : 2 ≤ r) (hK : Nat.card K = 8)
    {x : MulAut (StatedProj (StatedSp r K))} (hx3 : x ^ 3 = 1)
    (hout : x ∉ innerAut (StatedProj (StatedSp r K))) :
    ∃ (σ : K ≃+* K) (h : MulAut (StatedProj (StatedSp r K))), orderOf σ = 3 ∧
      x = h * fieldAut r K σ * h⁻¹ := by
  have hK' : Nat.card K = 2 ^ 3 := by rw [hK]; norm_num
  have O := CFSG.RankThree.PartOne.KCSpComm.spOuter Nat.prime_two (by norm_num : 1 ≤ 3) hr hK'
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx1 : x ≠ 1 := fun h => hout (h ▸ one_mem _)
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hxE : x ∈ spSemilinearAutGroup r K :=
    CFSG.RankThree.PartOne.KCSpComm.mem_of_odd_orderOf_of_index_dvd_two _ O.index_dvd
      (by rw [hxord]; decide)
  have hxD : x ∉ spLinearAutGroup r K := by
    intro hD
    have := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal
      (StatedProj (StatedSp r K))
    exact hout (CFSG.RankThree.PartOne.KCSpComm.mem_of_pow_eq_one_of_relIndex_dvd_two
      (O.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)) Nat.prime_three (by norm_num) hD hx3)
  obtain ⟨-, σ, hσ, h, -, hxh⟩ := O.descent 3 Nat.prime_three x hxE hxD hxord
  exact ⟨σ, h, hσ, hxh⟩

theorem fieldCoreAt_fieldAut_sp_eight (hr : 3 ≤ r) (hK : Nat.card K = 8) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) : FieldCoreAt 3 (fieldAut r K σ) := by
  have hK' : Nat.card K = 2 ^ 3 := by rw [hK]; norm_num
  obtain ⟨-, hkcard, -, -, hinjk, hJfix, -, hJs, -, hfixing, hzp, hzcard, -, -⟩ :=
    symplectic_prime_subfield_fixed_group_and_full_centralizer_odd (K := K) Nat.prime_two
      Nat.prime_three (by norm_num) (by norm_num) (by norm_num) (by omega : 2 ≤ r) hK' σ hσ
  obtain ⟨hJsimple, hJnc⟩ := hJs (fun h => absurd h.1 (by omega))
  have hJq : CFSG.IsQuasisimple (subfieldFixedGroup K r σ) :=
    isQuasisimple_of_simple_nonabelian (fun hc => by
      obtain ⟨a, b, hab⟩ := hJnc
      exact hab (hc a b))
  have hδp : orderOf (fieldAut r K σ) = 3 := by rw [← Nat.card_zpowers, hzcard]
  refine fieldCoreAt_of_fixSub_eq hδp hJq (fun g => hJfix g) (fun β hβ => ?_) ?_
  · have hβmem : β ∈ fixingSubgroup (MulAut (StatedProj (StatedSp r K)))
        ((subfieldFixedGroup K r σ : Subgroup (StatedProj (StatedSp r K))) :
          Set (StatedProj (StatedSp r K))) :=
      (mem_fixingSubgroup_iff _).2 fun u hu => hβ u hu
    rw [hfixing, hzp] at hβmem
    exact hβmem
  ·
    have hk2 : Nat.card (descentField σ) = 2 := by rw [hkcard]; norm_num
    haveI : CharP (descentField σ) 2 := W2.charP_two_of_card_two hk2
    have h3 : 3 ∣ Nat.card (StatedSp r (descentField σ)) :=
      W2.three_dvd_card_statedSp hk2 (by omega)
    have e1 : StatedProj (StatedSp r (descentField σ)) ≃* subfieldFixedGroup K r σ :=
      MonoidHom.ofInjective hinjk
    have hcardJ : Nat.card (subfieldFixedGroup K r σ) =
        Nat.card (StatedSp r (descentField σ)) :=
      (Nat.card_congr e1.toEquiv).symm.trans (Nat.card_congr (Equiv.ofBijective
        (proj r (descentField σ))
        ⟨proj_injective_of_charP_two r, QuotientGroup.mk'_surjective _⟩)).symm
    rw [hcardJ]
    intro hcop
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop h3) (by norm_num)

end Outer

section SpEight

variable {r : ℕ} {K : Type} [Field K]

theorem isLocallyBalancedAbs_one_psp_three_eight (hK : Nat.card K = 8) (hr : 3 ≤ r) :
    IsLocallyBalancedAbs 3 1 (StatedProj (StatedSp r K)) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK' : Nat.card K = 2 ^ 3 := by rw [hK]; norm_num
  have hrq : ¬ (r = 2 ∧ 2 ^ 3 = 2) := fun h => by omega
  have hinj := CFSG.RankThree.PartOne.KCSpFull.spConj_injective Nat.prime_two (by norm_num)
    hK' (by omega) hrq
  have hO : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (StatedProj (StatedSp r K))) ∣ 3 := by
    have h := (CFSG.RankThree.Classical.higher_symplectic_outer_order_divides_field_multiplier_bound
      Nat.prime_two (by norm_num : 1 ≤ 3) hr hK').1
    simpa using h
  refine isLocallyBalancedAbs_one_of_hom_pGroup (n := 1) Nat.prime_three hinj
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner _))
    (fun α hα => (QuotientGroup.eq_one_iff α).1 hα)
    (fun y => by
      rw [pow_one]
      exact orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_natCard y).trans hO))
    fun x hx hx1 => ?_
  by_cases hin : x ∈ innerAut (StatedProj (StatedSp r K))
  · obtain ⟨s, rfl⟩ := hin
    right
    have hs3 : s ^ 3 = 1 := hinj (by rw [map_pow, hx, map_one])
    have hs1 : s ≠ 1 := fun h => hx1 (by rw [h, map_one])
    rw [fixSub_conj_eq_centralizer]
    exact noNormalPPrime_three_centralizer_statedProj_eight hK (by omega)
      (orderOf_eq_prime hs3 hs1)
  · left
    obtain ⟨σ, h, hσ, hxh⟩ := outer_conj_fieldAut_eight (by omega) hK hx hin
    exact fieldCoreAt_of_conj (fieldCoreAt_fieldAut_sp_eight hr hK hσ) h⁻¹ (by rw [hxh]; group)

theorem isLocallyBalancedAbs_three_one_B_eight_of_three_le {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hq : IsTwoPow q 3) (hr : 3 ≤ r) :
    IsLocallyBalancedAbs 3 1 (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩).Group := by
  have hq8 : q.card = 8 := by
    rw [TauCeti.PrimePower.card_def, hq.1, hq.2]
    norm_num
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
    (⟨.B r q, hv⟩ : TauCeti.ValidLieTypeIndex)
  have hK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField
      (⟨.B r q, hv⟩ : TauCeti.ValidLieTypeIndex)) = 8 := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField]
    simpa [TauCeti.ValidLieTypeIndex.fieldOrder] using hq8
  exact IsLocallyBalancedAbs.of_mulEquiv
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq.1 hr)
    (isLocallyBalancedAbs_one_psp_three_eight hK hr)

end SpEight

end CFSG.HardMathSupport.Dickson.Bal207

end
