module

public import CFSG.CGT.PushingUpLit.BHS6.ThreeEightPerf
public import CFSG.CGT.PushingUpLit.BHS6.ThreeEightComm

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.RankThree.PartOne CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.Campbell CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem isBTBlock_of_short {G T E : Subgroup Γ} (hEG : E ≤ G) (hshort : IsShort2 E)
    (hperf : ⁅pCoreOf 2 E, E⁆ = pCoreOf 2 E) (hcomm : ⁅E, baum T⁆ = E)
    (htype : (∃ n : ℕ, 2 ≤ n ∧ IsNaturalSLTwoModule ↥E n) ∨
      ∃ m : ℕ, 1 ≤ m ∧ IsNaturalAltModule ↥E m)
    (hnotC : ¬ E ≤ Subgroup.centralizer (omegaOneCenterOf T : Set Γ)) : IsBTBlock G T E := by
  have hU : ∀ x ∈ pCoreOf 2 E, x ∈ pCoreOf 2 E ⊓ Subgroup.centralizer (pCoreOf 2 E : Set Γ) ∧
      x ^ 2 = 1 := by
    intro x hx
    have hxU : x ∈ CFSG.QuasithinUnique.blockU E := by
      show x ∈ ⁅pCoreOf 2 E, E⁆
      rw [hperf]
      exact hx
    exact ⟨hshort.2.2.1.1 hxU, hshort.2.2.1.2 x hxU⟩
  refine ⟨hEG, oResidualTwo_eq_top_of_isShort2 hshort, hcomm, hperf, ⟨fun x hx y hy => ?_,
    fun x hx => (hU x hx).2⟩, ?_, htype⟩
  · have h1 : x ∈ Subgroup.centralizer (pCoreOf 2 E : Set Γ) :=
      (Subgroup.mem_inf.1 (hU x hx).1).2
    rw [Subgroup.mem_centralizer_iff] at h1
    exact (h1 y hy).symm
  · intro h
    apply hnotC
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 : ⁅e, z⁆ ∈ (⁅E, omegaOneCenterOf T⁆ : Subgroup Γ) :=
      Subgroup.commutator_mem_commutator he hz
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm

theorem isBTBlock_of_alt_three [Finite Γ] {G T P' E : Subgroup Γ} (hP'G : P' ≤ G)
    (hmin : IsMinParabolic2 (baum T) P') (hE : E = twoResidual P') (hshort : IsShort2 E)
    (hA : IsAltType E 3)
    (hnotC : ¬ E ≤ Subgroup.centralizer (omegaOneCenterOf T : Set Γ)) :
    IsBTBlock G T E ∧ IsNaturalAltModule ↥E 1 := by
  have hperf := perfect_of_isAltType_three hshort hA
  have hnat : IsNaturalAltModule ↥E 1 := isNaturalAltModule_of_isAltType (m := 1) hA
  have hEG : E ≤ G := by
    rw [hE]
    exact (twoResidual_le P').trans hP'G
  refine ⟨isBTBlock_of_short hEG hshort hperf ?_ (Or.inr ⟨1, le_rfl, hnat⟩) hnotC, hnat⟩
  obtain ⟨α, hαs, hαk, -⟩ := hA
  have hcard : Nat.card ↥(alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have : IsSimpleGroup ↥(alternatingGroup (Fin 3)) := isSimpleGroup_of_prime_card hcard
  exact commutator_eq_of_isShort2 hmin hE hshort α hαs hαk

end CFSG.CGT.PushingUpLit.BHS6
