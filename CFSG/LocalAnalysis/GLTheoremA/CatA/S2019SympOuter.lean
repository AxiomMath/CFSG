module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalPartsSO
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticDescent
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019FixTransport
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Outer
import CFSG.SignalizerFunctorTheorem.NonLocal.SpMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne.KCSpComm
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

section Field

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem s2019FixCentralizes_conj_fieldAut_sp (hr : 2 ≤ r) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (σ : K ≃+* K) (hσ : σ ^ p = 1) (hk : ¬(r = 2 ∧ Nat.card (descentField σ) = 2))
    (γ : MulAut (StatedProj (StatedSp r K))) :
    S2019FixCentralizes p (γ * fieldAut r K σ * γ⁻¹) := by
  haveI : NeZero r := ⟨by omega⟩
  have hX : fixSubgroup (fieldAut r K σ) = (subfieldProj (r := r) σ).range := by
    rw [← spFixedGroup_fieldAut_eq_range (hp.odd_of_ne_two hp2) hσ]
    exact Subgroup.ext fun x => mem_fixSubgroup.trans mem_spFixedGroup.symm
  obtain ⟨hs, -⟩ := simple_perfect_statedProj (k := descentField σ) hr hk
  have eJ : ↥(subfieldProj (r := r) σ).range ≃* StatedProj (StatedSp r (descentField σ)) :=
    (MulEquiv.subgroupCongr (range_subfieldInj (r := r) σ).symm).trans
      (MonoidHom.ofInjective (subfieldInj_injective (r := r) σ)).symm
  refine s2019FixCentralizes_conj_of_nonLocalized p (fieldAut r K σ) γ hX.ge ?_
    (eJ.isSimpleGroup_congr.2 hs)
    (CFSG.SignalizerFunctorTheorem.NonLocal.nonLocalized_spSubfield hr σ)
  rw [hX, Subgroup.commutator_le]
  intro g hg h hh
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hh) (Subgroup.inv_mem _ hg))
    (Subgroup.inv_mem _ hh)

end Field

theorem s2019SympOuter (Qs : ℕ → Prop) : S2019SympOuter Qs := by
  intro p q hp hp2 hq hq2 hqp _ G _ n f hG β hβ hnot
  obtain ⟨⟨-, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hG
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K q := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  haveI : Finite G := Finite.of_equiv _ e.toEquiv.symm
  refine s2019FixCentralizes_of_congr hp e β ?_
  set β' := MulAut.congr e β with hβ'def
  have hβ' : β' ^ p = 1 := by rw [hβ'def, ← map_pow, hβ, map_one]
  have hnot' : ∀ a, β' ≠ MulAut.conj a := by
    intro a ha
    apply hnot (e.symm a)
    have h1 := congrArg (MulAut.congr e).symm ha
    rw [hβ'def, MulEquiv.symm_apply_apply] at h1
    rw [h1]
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hO := spOuter (K := K) hq hf hn hK
  have hodd : Odd (orderOf β') :=
    (hp.odd_of_ne_two hp2).of_dvd_nat (orderOf_dvd_of_pow_eq_one hβ')
  have hE : β' ∈ spSemilinearAutGroup n K :=
    mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd hodd
  have hD : β' ∉ spLinearAutGroup n K := by
    intro hD
    have : (inner (StatedProj (StatedSp n K))).Normal := inner_normal _
    have hrel : (inner (StatedProj (StatedSp n K))).relIndex (spLinearAutGroup n K) ∣ 2 :=
      hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)
    obtain ⟨t, ht⟩ := mem_of_pow_eq_one_of_relIndex_dvd_two hrel hp hp2 hD hβ'
    exact hnot' t ht.symm
  have hord : orderOf β' = p := orderOf_eq_prime hβ' fun h => hD (h ▸ one_mem _)
  obtain ⟨-, σ, hσ, h, -, hβeq⟩ := hO.descent p hp β' hE hD hord
  have hk : ¬(n = 2 ∧ Nat.card (descentField σ) = 2) := by
    rintro ⟨-, h2⟩
    have h2' : ((2 : ℕ) : descentField σ) = 0 := by
      haveI := Fintype.ofFinite (descentField σ)
      have := FiniteField.cast_card_eq_zero (descentField σ)
      rwa [← Nat.card_eq_fintype_card, h2] at this
    have h2K : ((2 : ℕ) : K) = 0 := by
      have := congrArg (descentField σ).subtype h2'
      rwa [map_natCast, map_zero] at this
    rw [CharP.cast_eq_zero_iff K q] at h2K
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h2K)
  rw [hβeq]
  exact s2019FixCentralizes_conj_fieldAut_sp hn hp hp2 σ
    (by rw [← hσ]; exact pow_orderOf_eq_one σ) hk h

end CFSG.LocalAnalysis.GLTheoremA.S2019
