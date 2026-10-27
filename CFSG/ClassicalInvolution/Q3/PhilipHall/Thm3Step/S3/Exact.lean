module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S3.Classes
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S3.Rows

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)} {K : Subgroup Y}

theorem isSubnormal_inf_centralizer (hΦ : HypOmegaGen Φ) {M : Subgroup Y} (hM : M ∈ Φ)
    {P : Subgroup Y} (hMP : M ≤ P) {z : Y} (hz : IsUniqueInvolution M z) :
    IsSubnormal M (P ⊓ Subgroup.centralizer ({z} : Set Y)) := by
  have h := (QuaternionBridge.CentQ.isSubnormal_centralizer_gen hΦ hM hz).inf P
  rwa [inf_eq_left.mpr hMP, inf_comm] at h

theorem oddCoreOf_eq_bot_of_centralizer (hΦ : HypOmegaGen Φ) {M : Subgroup Y} (hM : M ∈ Φ)
    {P : Subgroup Y} (hMP : M ≤ P) {z : Y} (hz : IsUniqueInvolution M z)
    (hC : classicalInvolutionOddCore ↥(P ⊓ Subgroup.centralizer ({z} : Set Y)) = ⊥) :
    oddCoreOf M = ⊥ := by
  have h := Balance.oddCoreIn_le_of_isSubnormal (isSubnormal_inf_centralizer hΦ hM hMP hz)
  rw [oddCoreIn_eq_bot hC, le_bot_iff] at h
  exact h

omit [Finite Y] in
theorem oddCoreOf_conjSub_eq_bot {M : Subgroup Y} (hM : oddCoreOf M = ⊥) (g : Y) :
    oddCoreOf (conjSub g M) = ⊥ := by
  let e : ↥M ≃* ↥(conjSub g M) :=
    Subgroup.equivMapOfInjective M (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact oddCoreIn_eq_bot (oddCore_eq_bot_of_mulEquiv e.symm (oddCore_eq_bot_of_oddCoreIn hM))

omit [Finite Y] in
theorem mem_aStar_of_mem_twinSet {J : Subgroup Y} (hJ : J ∈ twinSet Φ K) : J ∈ aStar Φ K := by
  by_cases hJK : J = K
  · rw [hJK]
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨hJ.1, Or.inr (Or.inr ⟨hJ, hJK⟩)⟩

theorem oddCoreOf_eq_bot_of_mem_twinOrbit (hF : RowCentralizerFacts) (hΦ : TypeRHyp Φ)
    (hK : K ∈ Φ) (hA : ¬ AEmpty Φ K) (hin : InnerIH Y Φ) (htw : ¬ TwinOrbits Φ K)
    (hO : classicalInvolutionOddCore Y = ⊥) {M : Subgroup Y} (hM : M ∈ twinOrbit Φ K) :
    oddCoreOf M = ⊥ := by
  obtain ⟨z, hz⟩ := (hΦ.hyp.omega1 K hK).1
  have hKΔ : K ∈ twinOrbit Φ K := mem_twinOrbit_self hK hz
  have hsub : twinOrbit Φ K ⊆ Φ := twinOrbit_subset hΦ.hyp.conjInvariant
  have hΔ : TypeRHyp (twinOrbit Φ K) := typeRHyp_of_subset hΦ hsub twinOrbit_conjInvariant
  have hC := thm3RConclG_twinOrbit hΦ hK hA hin htw 1
  rw [conjSub_one] at hC
  have hst : aStar (twinOrbit Φ K) K = aStar Φ K := aStar_twinOrbit hΦ.hyp hKΔ
  have hrows : Thm3RowsG (twinOrbit Φ K) (omegaGen (aStar Φ K)) := by
    have := hC.2
    rwa [hst] at this
  have hOP := oddCore_omegaGen_aStar_eq_bot hΦ hK hA hin htw hO
  have key : ∀ N ∈ aStar Φ K, oddCoreOf N = ⊥ := by
    intro N hN
    have hNΔ : N ∈ twinOrbit Φ K := aStar_subset_twinOrbit hΦ.hyp hKΔ hN
    obtain ⟨w, hw⟩ := (hΦ.hyp.omega1 N (hsub hNΔ)).1
    have hNP : N ≤ omegaGen (aStar Φ K) := le_omegaGen hN
    exact oddCoreOf_eq_bot_of_centralizer hΔ.hyp hNΔ hNP hw
      (oddCore_inf_centralizer_eq_bot_of_rows hF hΔ hOP hrows hNΔ hNP hw)
  obtain ⟨g, J, hJ, rfl⟩ := hM
  exact oddCoreOf_conjSub_eq_bot (key J (mem_aStar_of_mem_twinSet hJ)) g

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S3
