module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CDPhi
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEInd1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFStarCent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
  [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

theorem sec5c_isEven_add_single (i : Fin 6) {v : Fin 6 → ZMod 2} (hv : ¬ IsEvenVec v) :
    IsEvenVec (v + Pi.single i 1) := by
  have hv1 : ∑ j, v j = 1 := by
    have hv' : ∑ j, v j ≠ 0 := hv
    generalize ∑ j, v j = a at hv'
    revert a
    decide
  change ∑ j, ((v + Pi.single i 1 : Fin 6 → ZMod 2)) j = 0
  have hmm : (v + Pi.single i 1 : Fin 6 → ZMod 2) = v + (∑ j, v j) • Pi.single i 1 := by
    rw [hv1, one_smul]
  rw [hmm]
  exact sec5c_sum_ev i v

theorem sec5c_simHasType_one (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1)
    {K : Finset (Fin 6)} (hK : K.card = 1 ∨ K.card = 5) :
    ∃ α : ℤˣ, SimHasType (projOrthToProjSim Q (toProj Q (fr.signChange K))) 1 α := by
  rcases hK with h1 | h5
  · obtain ⟨α, hα⟩ := ff_simHasType_signChange hQ fr (Or.inl h1)
    rw [h1] at hα
    exact ⟨α, hα⟩
  · have hc : Kᶜ.card = 1 := by rw [Finset.card_compl, Fintype.card_fin, h5]
    obtain ⟨α, hα⟩ := ff_simHasType_signChange hQ fr (K := Kᶜ) (Or.inl hc)
    rw [hc, ff_toProj_signChange_compl] at hα
    exact ⟨α, hα⟩

theorem sec5c_simHasType_three (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1)
    {K : Finset (Fin 6)} (hK : K.card = 3) :
    ∃ α : ℤˣ, SimHasType (projOrthToProjSim Q (toProj Q (fr.signChange K))) 3 α := by
  obtain ⟨α, hα⟩ := ff_simHasType_signChange hQ fr (Or.inr hK)
  rw [hK] at hα
  exact ⟨α, hα⟩

namespace Sec5CDAbs

variable {L B : Subgroup G} {r : G} {i : Fin 6} {fr : NFrame Q (Fin 6) 1}
  {φc : ↥L →* omegaGroup hQ} (h : Sec5CDAbs L B r i fr φc)

include h

theorem liftL_induces {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ}
    (he : ∀ l : ↥L, e (QuotientGroup.mk l) = omegaToProj hQ (φc l)) {J : Finset (Fin 6)}
    (hJ : Even J.card) :
    InducesViaP L (Subgroup.center ↥L) hQ e (sec5c_liftL L B φc (fr.signChange J) : G)
      (projOrthToProjSim Q (toProj Q (fr.signChange J))) := by
  have h1 := inducesViaP_of_mem e (sec5c_liftL L B φc (fr.signChange J))
  rwa [he, coe_omegaToProj, h.map_liftL (signChange_mem_ffB0 fr hJ)] at h1

theorem phi_induces {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ}
    (he : ∀ l : ↥L, e (QuotientGroup.mk l) = omegaToProj hQ (φc l))
    (hx : InducesViaP L (Subgroup.center ↥L) hQ e r
      (projOrthToProjSim Q (toProj Q (fr.signChange {i})))) (v : Fin 6 → ZMod 2) :
    InducesViaP L (Subgroup.center ↥L) hQ e (sec5c_phi L B r i fr φc v)
      (projOrthToProjSim Q (toProj Q (fr.signChange (sec5c_supp v)))) := by
  by_cases hv : IsEvenVec v
  · rw [h.phi_even hv]
    exact h.liftL_induces he ((sec5c_isEvenVec_iff v).mp hv)
  · rw [h.phi_odd hv]
    have hw := (sec5c_isEvenVec_iff _).mp (sec5c_isEven_add_single i hv)
    have h1 := inducesViaP_mul hx (h.liftL_induces he hw)
    have hsd : symmDiff ({i} : Finset (Fin 6)) (sec5c_supp (v + Pi.single i 1)) =
        sec5c_supp v := by
      rw [sec5c_supp_add, sec5c_supp_single, symmDiff_comm (sec5c_supp v) {i},
        symmDiff_symmDiff_cancel_left]
    have hmul : projOrthToProjSim Q (toProj Q (fr.signChange {i})) *
        projOrthToProjSim Q (toProj Q (fr.signChange (sec5c_supp (v + Pi.single i 1)))) =
        projOrthToProjSim Q (toProj Q (fr.signChange (sec5c_supp v))) := by
      rw [← map_mul, ← map_mul, fr.signChange_mul, hsd]
    rwa [hmul] at h1

end Sec5CDAbs

end CFSG.OddStandard.SmallF3.Omega
