module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaGlue
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaGlueU
import CFSG.Quasithin.Background.GoldschmidtListedSolv

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.RankThree.PartTwo.KFacts
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

@[expose] def PSUModel : Prop :=
  ∀ {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K), 2 < p ^ f →
    ∀ {D H : Subgroup (MulAut (unitaryPSU h 3))}, CFSG.Open.IsElemAbelian 3 D →
      Nat.card D = 9 → innerAut (unitaryPSU h 3) ≤ H → ∀ {A : unitaryIsom3 h},
        psuConj h A ∈ localDeltaIn 3 H D → psuConj h A = 1

@[expose] def InnDiagPSU3Trivial : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    ∀ D H : Subgroup (MulAut Y), IsEkIn 3 2 ⊤ D → innerAut Y ≤ H →
      ∀ α ∈ localDeltaIn 3 H D, Lemma53Ns.IsInnDiagPSU3 α → α = 1

theorem two_lt_of_quasisimple {p f : ℕ} {K : Type} [Field K] {Y : Type*} [Group Y] [Finite Y]
    (hY : CFSG.Open.IsQuasisimple Y) (h : UnitaryFieldData p f K)
    (θ : (Y ⧸ Subgroup.center Y) ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ f) K)) :
    2 < p ^ f := by
  have := h.finite
  have hp := h.prime
  have hf := h.one_le
  by_contra hle
  push Not at hle
  have h2 : p ^ f = 2 := by
    have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    omega
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by
    rw [h.card, show 2 * f = f * 2 from mul_comm _ _, pow_mul, h2]
    norm_num
  have e' : (Y ⧸ Subgroup.center Y) ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ 1) K) := by
    have := θ
    rw [show p ^ f = 2 ^ 1 from h2] at this
    exact this
  have hsolP : Group.IsSolvable (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ 1) K)) :=
    CFSG.Quasithin.isSolvable_statedProj_one hF
  have hsolQ : Group.IsSolvable (Y ⧸ Subgroup.center Y) :=
    Group.isSolvable_of_isSolvable_injective (f := e'.toMonoidHom) e'.injective
  have hsolY : Group.IsSolvable Y :=
    CFSG.Quasithin.isSolvable_of_ker_le_center (QuotientGroup.mk' (Subgroup.center Y))
      (by rw [QuotientGroup.ker_mk'])
  have : Group.IsPerfect Y := (Group.isPerfect_def (G := Y)).2 hY.1
  have : Nontrivial Y := by
    have := hY.2.toNontrivial
    exact (QuotientGroup.mk'_surjective (Subgroup.center Y)).nontrivial
  exact Group.IsPerfect.not_isSolvable Y hsolY

theorem innDiagPSU3Trivial_of_model (hmodel : PSUModel) : InnDiagPSU3Trivial := by
  intro Y _ _ hY D H hD hH α hα hinn
  obtain ⟨K, _, _, q, θ, φ, hcard, hφ, hcomp⟩ := hinn
  obtain ⟨p, f, rfl, ⟨h⟩⟩ := exists_unitaryFieldData hcard
  have hq := two_lt_of_quasisimple hY h θ
  obtain ⟨A, hA⟩ := exists_psuConj_of_isConjByGL h hq φ hφ
  let ψ := unitaryPSUEquiv h (n := 3) (by norm_num)
  let e : (Y ⧸ Subgroup.center Y) ≃* unitaryPSU h 3 := θ.trans ψ.symm
  refine eq_one_of_transport hY.1 e hD hH hα
    (φ := MulAut.congr ψ.symm φ) (fun y => ?_) (fun D' H' hD' hc hH' hmem => ?_)
  · exact (congrArg ψ.symm (hcomp y)).trans (congr_apply_apply ψ.symm φ _).symm
  · rw [hA] at hmem ⊢
    exact hmodel h hq hD' hc hH' hmem

theorem input19_7_3b_of_psu (hpsu : InnDiagPSU3Trivial) : Lemma53Ns.Input19_7_3b := by
  intro K _ _ hK _ D H hD hH _ _ α hα hinn
  rcases hinn with h | h
  · exact isInnDiagPSL3_eq_one hK.1 hD hH hα h
  · exact hpsu K hK D H hD hH α hα h

theorem input19_7_3b_of_model (hmodel : PSUModel) : Lemma53Ns.Input19_7_3b :=
  input19_7_3b_of_psu (innDiagPSU3Trivial_of_model hmodel)

end CFSG.HardMathSupport.Solomon.Coordinator
