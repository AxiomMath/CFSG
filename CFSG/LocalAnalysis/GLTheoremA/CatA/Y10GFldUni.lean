module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldUniMark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldUniTw
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldUniLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinFldLang
public import CFSG.LieType.SemisimpleCentralizers.HeldLangPSU
public import CFSG.LieType.SemisimpleCentralizers.HeldLangUnitFix
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.Assembly.OpenBridges
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GFldUni

open CFSG.Open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.HeldLang
open CFSG.LocalAnalysis.GLTheoremA.Y10GField CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.LocalAnalysis.GLTheoremA.Y10GFldUniMark CFSG.LocalAnalysis.GLTheoremA.Y10GFldUniTw
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnLinFld
open CFSG.ClassicalGroups.Unitary CFSG.StandardType
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU heldGU mem_heldGU hct_isSolvable_of_natCard_eq)
open CFSG.HardMathSupport.Foote.ModuleExclusions (Ai)

theorem fldUni_of_sigmaPow_rig (hSig : UniSigmaPowOne) (hRig : GGLabelRigidInput) : FldUni := by
  intro S _ _ p α J labK labJ hFam hp hp2 hcen hfld hα hlabJ hJ
  haveI := Fact.mk hp
  obtain ⟨K, hK, hKf, d, τ, hτ, hτq, hcard, hd3, hd3n, htag, hrank, hnK, A, σ, u, e, hA, hαu, hgraph,
    hσ1⟩ := fieldKind_unitary_data hcen hFam hfld
  have hn1 : 1 ≤ labK.n := by
    rcases Nat.eq_zero_or_pos labK.n with h0 | h0
    · exfalso
      have h1 : Nat.card K = 1 := by rw [hcard, h0, pow_zero, one_pow]
      have : 1 < Nat.card K := Finite.one_lt_card
      omega
    · exact h0
  have hK2 : Nat.card K = 2 ^ (2 * labK.n) := by rw [hcard, ← pow_mul, mul_comm]
  have hdQ : (d, 2 ^ labK.n) ≠ (3, 2) := by
    intro h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    have h3 : labK.n = 1 := Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm)
    have := hd3n h1
    omega
  have hMEq : MulAut.congr e α = u := by
    ext r
    have h1 := hαu (e.symm r)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  have hpow : u ^ p = 1 := by rw [← hMEq, ← map_pow, hα, map_one]
  have hσp : σ ^ p = 1 := hSig K labK.n d τ hτ hτq hcard hd3 hdQ A hA σ p hp hp2 u hgraph hpow
  have hσord : orderOf σ = p := orderOf_eq_prime hσp hσ1
  have hodd : Odd (orderOf σ) := by rw [hσord]; exact hp.odd_of_ne_two hp2
  have hpn : p ∣ 2 * labK.n := by
    have h := orderOf_dvd_of_card Nat.prime_two (by omega : 1 ≤ 2 * labK.n) hK2 σ
    rwa [hσord] at h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2
    (by exact_mod_cast two_eq_zero_of_card hcard)
  have hbar : IsUnitaryInvolution τ := by
    have h := isUnitaryInvolution_unitaryInvolution (K := K) (p := 2) (f := labK.n) hcard
    have heq : CFSG.LieType.BorelTits.unitaryInvolution K 2 labK.n = τ :=
      RingEquiv.ext (fun c => by rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, hτq])
    rw [← heq]
    exact h
  have hcomm : ∀ x, σ (τ x) = τ (σ x) := fun x => by rw [hτq, hτq, map_pow]
  obtain ⟨j, hj2, hFcard, hbarform⟩ :=
    exists_barFix_eq Nat.prime_two (by omega : 1 ≤ 2 * labK.n) hK2 hbar hcomm hodd
  have hτ₀ : IsUnitaryInvolution (barFix σ τ hcomm hbar.invol) :=
    isUnitaryInvolution_barFix Nat.prime_two (by omega : 1 ≤ 2 * labK.n) hK2 hbar hcomm hodd
  have hnj : p * j = labK.n := by
    rw [hσord] at hj2
    have h1 : 2 * labK.n / p * p = 2 * labK.n := Nat.div_mul_cancel hpn
    rw [← hj2] at h1
    have h2 : 2 * (p * j) = 2 * labK.n := by rw [← h1]; ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨c, hc⟩ := normProd_scalar_of_sigma_pow hτ hτq hcard hd3 hdQ σ hA u hgraph hpow hσp
  have hc' : Ai σ (A : Matrix (Fin d) (Fin d) K) (orderOf σ) = c • (1 : Matrix (Fin d) (Fin d) K) := by
    rw [hσord]; exact hc
  obtain ⟨Y, hYC, hYn, hCY, ⟨eY⟩⟩ :=
    exists_psu_fix_of_eq (p := 2) (e := 2 * labK.n) Nat.prime_two (by omega) hK2 hbar hcomm hodd
      (StatedSU d (2 ^ labK.n) K) (statedSU_eq_SUid hτ hτq) A (mem_heldGU.1 hA) hc'
      u.toMonoidHom (fun x x' h => hgraph x x' h)
  have hJ' : GLAPComponent p (fixSubgroup u) (J.map e.toMonoidHom) := by
    rw [← hMEq, ← fixSubgroup_map_congr]
    exact (glaPComponent_map_iff hp e.injective).mpr hJ
  have hlabJ' : HasLabel ↥(J.map e.toMonoidHom) (fun l : GLALabel => l = labJ) :=
    hasLabel_transport e hlabJ
  have hfixC : fixHom u.toMonoidHom = fixSubgroup u := by
    ext x
    rw [mem_fixHom, mem_fixSubgroup]
    rfl
  rw [hfixC] at hYC hYn hCY
  have hSU0 : StatedSU d (2 ^ j) (fixField σ) =
      CFSG.LieType.Universal.Unitary.SUid (barFix σ τ hcomm hbar.invol) d :=
    statedSU_eq_SUid hτ₀.invol hbarform
  rw [← hSU0] at eY
  have hJperf : ⁅J.map e.toMonoidHom, J.map e.toMonoidHom⁆ = J.map e.toMonoidHom :=
    Lemma53Ns.glaPComponent_perfect hJ'
  by_cases hdj : (d, 2 ^ j) = (3, 2)
  ·
    exfalso
    obtain ⟨rfl, h2⟩ := Prod.mk.inj hdj
    have hj1 : j = 1 := Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm)
    have hcardSU : Nat.card ↥(StatedSU 3 (2 ^ j) (fixField σ)) = 2 ^ 3 * 3 ^ 3 := by
      have hc := CFSG.RankThree.PartTwo.Sec8.Item87Proof.card_statedSU_three_two (F := fixField σ)
        (f := j) hFcard
      rw [hc, hj1]
      norm_num
    have hsolSU : Group.IsSolvable ↥(StatedSU 3 (2 ^ j) (fixField σ)) :=
      hct_isSolvable_of_natCard_eq Nat.prime_two Nat.prime_three (by norm_num) hcardSU
    haveI := hsolSU
    haveI : Group.IsSolvable (StatedProj (StatedSU 3 (2 ^ j) (fixField σ))) := inferInstance
    have hsolY : Group.IsSolvable ↥Y :=
      solvable_of_surjective (f := eY.symm.toMonoidHom) eY.symm.surjective
    have hJY : J.map e.toMonoidHom ≤ Y :=
      calc J.map e.toMonoidHom = ⁅J.map e.toMonoidHom, J.map e.toMonoidHom⁆ := hJperf.symm
        _ ≤ ⁅fixSubgroup u, fixSubgroup u⁆ := Subgroup.commutator_mono hJ'.1 hJ'.1
        _ ≤ Y := hCY
    haveI : Group.IsSolvable ↥(J.map e.toMonoidHom) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJY) (Subgroup.inclusion_injective hJY)
    haveI := (ggHasLabel_of_hasLabel hlabJ').2.1
    exact not_isSolvable_quot_center (J := ↥(J.map e.toMonoidHom)) inferInstance
  ·
    haveI : IsSimpleGroup (StatedProj (StatedSU d (2 ^ j) (fixField σ))) :=
      isSimpleGroup_statedProj_statedSU (fixField σ) 2 j hFcard d hd3 hdj
    haveI : Group.IsPerfect (StatedSU d (2 ^ j) (fixField σ)) :=
      isPerfect_statedSU hFcard hd3 hdj
    haveI : Group.IsPerfect (StatedProj (StatedSU d (2 ^ j) (fixField σ))) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    haveI : IsSimpleGroup ↥Y := eY.isSimpleGroup
    haveI : Group.IsPerfect ↥Y :=
      Group.IsPerfect.ofSurjective (f := eY.symm.toMonoidHom) eY.symm.surjective
    have hJY : J.map e.toMonoidHom = Y := component_eq_of_fixed hJ' hYC hYn hCY
    obtain ⟨χ⟩ : Nonempty (↥(J.map e.toMonoidHom) ⧸ Subgroup.center ↥(J.map e.toMonoidHom) ≃*
        StatedProj (StatedSU d (2 ^ j) (fixField σ))) := by
      rw [hJY]
      exact nonempty_quotCenter_equiv eY
    obtain ⟨ψ⟩ := nonempty_quot_heldSU_equiv_statedProj uniScalar_holds
      (barFix σ τ hcomm hbar.invol) hτ₀.invol hbarform hFcard hd3 hdj
    have hlabel := canonLabel_uni_of_ggLabelRigidInput hRig (barFix σ τ hcomm hbar.invol) hτ₀.invol hbarform
      hFcard hd3 hlabJ' (χ.trans ψ.symm)
    have hJn : (canonLabel labJ).n = j := by rw [hlabel]
    have hJtag : (canonLabel labJ).tag = .twA := by rw [hlabel]
    have hJrank : (canonLabel labJ).rank = d - 1 := by rw [hlabel]
    refine ⟨?_, ?_, ?_⟩
    · rw [hnK, hJn, hnj]
    · rw [htag, hJtag]
    · rw [hJrank]
      omega

section Certificates


theorem fldUni_of_sigmaPow (hSig : UniSigmaPowOne) : FldUni :=
  fldUni_of_sigmaPow_rig hSig ggLabelRigidInput_holds

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.Y10GFldUni

end
