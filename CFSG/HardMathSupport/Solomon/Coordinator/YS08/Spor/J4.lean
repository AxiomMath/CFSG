module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Numerics
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4CentCEQuasisimple
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4ThreeClass

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.AGLEmbeddingD2.Wilson.NormalizerAction CFSG.HardMathSupport.Solomon.Coordinator

section


theorem j4_noL3Comp_cE :
    NoL3Comp (Subgroup.centralizer ({CFSG.Quasithin.J4M2.cE} : Set ↥CFSG.Sporadic.J4.J)) := by
  obtain ⟨hq, hz, ⟨hm⟩⟩ := centralizer_cE_quasisimple CFSG.Sporadic.J4.j4Facts
  have hcard : Nat.card ↥(Subgroup.centralizer ({CFSG.Quasithin.J4M2.cE} : Set ↥CFSG.Sporadic.J4.J))
      = 2661120 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center ↥(Subgroup.centralizer ({CFSG.Quasithin.J4M2.cE} : Set ↥CFSG.Sporadic.J4.J)))
    rw [Nat.card_congr hm.toEquiv, CFSG.Sporadic.Mathieu.card_M22, hz] at h
    omega
  refine noL3Comp_of_quasisimple_central (isQuasisimple_open_of_native hq) ?_
  intro d hd hcop
  rw [hz] at hd
  rw [hcard]
  have hd6 : d ≤ 6 := Nat.le_of_dvd (by norm_num) hd
  have key : ∀ d : ℕ, d ≤ 6 → d ∣ 6 → Nat.Coprime d 3 → d = 1 ∨ d = 2 := by decide
  have hd12 : d = 1 ∨ d = 2 := key d hd6 hd hcop
  rcases hd12 with rfl | rfl
  · exact noL3Eq_2661120
  · exact noL3Eq_1330560


theorem nonempty_j4_equiv (hbr : SporadicBridges) :
    Nonempty (↥CFSG.Sporadic.J4.J ≃* (TauCeti.CFSGIndex.sporadic .J4).Group) :=
  ⟨((CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat).symm.trans (hbr .J4).some)⟩

theorem sporL3DownInner_J4 (hbr : SporadicBridges) : SporL3DownInner .J4 := by
  haveI : Finite ↥CFSG.Sporadic.J4.J := Nat.finite_of_card_ne_zero (by
    rw [CFSG.Sporadic.J4.card_J CFSG.Sporadic.J4.j4Facts]; norm_num)
  have h1 := @sporL3DownInner_of_comp .J4 ↥CFSG.Sporadic.J4.J inferInstance inferInstance
    (nonempty_j4_equiv hbr)
  have hcard : NoL3Eq (Nat.card ↥CFSG.Sporadic.J4.J) := by
    rw [CFSG.Sporadic.J4.card_J CFSG.Sporadic.J4.j4Facts]
    exact noL3Eq_86775571046077562880
  have h2 := h1 hcard
  refine h2 ?_
  intro x hx
  obtain ⟨g, hg⟩ := exists_conj_cE_of_orderThree x (hx ▸ pow_orderOf_eq_one x) (by
    intro h1
    rw [h1, orderOf_one] at hx
    exact absurd hx (by norm_num))
  refine noL3Comp_centralizer_of_isConj (x := CFSG.Quasithin.J4M2.cE) ?_ j4_noL3Comp_cE
  exact isConj_iff.2 ⟨g⁻¹, by rw [← hg]; group⟩
end

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
