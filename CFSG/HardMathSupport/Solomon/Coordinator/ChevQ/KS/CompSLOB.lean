module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209F4

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSCompSLOB

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  Bal209F4Aux
open scoped commutatorElement

theorem sLOB_of_bal207_component {X : Type} [Group X] [Finite X]
    (h207 : CFSG.HardMathSupport.Dickson.Bal207.Bal207Corr) (hKG : CFSG.Open.IsKGroup X)
    {B J : Subgroup X} {a : X} (hBSC : IsSCp 3 ⊤ B) (ha : a ∈ B)
    (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({a} : Set X)))
    (hBJ : B ≤ Subgroup.normalizer (J : Set X)) {P : TauCeti.LieTypeIndex → Prop}
    (hP : ∀ d, P d → Bal207Index 3 d ∧ ¬ CFSG.HardMathSupport.Dickson.Bal207.IsG2EightIndex d)
    (hL : IsLieQuot ↥J P) :
    IsStronglyLocallyOneBalanced 3 B a J := by
  have hBel : CFSG.Open.IsElemAbelian 3 B := hBSC.2.1
  have hBC : B ≤ Subgroup.centralizer ({a} : Set X) := le_centralizer_of_elemAbelian hBel ha
  set C := Subgroup.centralizer ({a} : Set X) with hCdef
  obtain ⟨hJC, hsubJ, hJq⟩ := hJ
  have hsub' : CFSG.Open.IsSubnormal (J.subgroupOf C) ⊤ :=
    CFSG.Open.IsSubnormal.of_mathlib ((CFSG.Open.IsSubnormal.iff_subgroupOf hJC).1 hsubJ)
  have hq' : CFSG.Open.IsQuasisimple ↥(J.subgroupOf C) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJC) hJq
  have hcomp : CFSG.Open.IsComponentOf (J.subgroupOf C) ⊤ := ⟨le_top, hsub', hq'⟩
  have hSC' : IsSCp 3 ⊤ (B.subgroupOf C) := isSCp_subgroupOf hBC hBSC
  have hBN' : B.subgroupOf C ≤
      Subgroup.normalizer (((J.subgroupOf C : Subgroup ↥C)) : Set ↥C) := by
    intro b' hb'
    have hbB : (b' : X) ∈ B := Subgroup.mem_subgroupOf.1 hb'
    have hN := Subgroup.mem_normalizer_iff.1 (hBJ hbB)
    rw [Subgroup.mem_normalizer_iff]
    intro k
    simpa [Subgroup.mem_subgroupOf] using hN (k : X)
  have hLie : IsLieQuot ↥(J.subgroupOf C) P :=
    isLieQuot_mulEquiv (Subgroup.subgroupOfEquivOfLe hJC).symm hL
  have hbal := CFSG.HardMathSupport.Dickson.Bal207.Bal207Corr.of_index h207 (hKG.subgroup C)
    Nat.prime_three (by decide) hcomp hSC' hBN' hP hLie
  intro S hS hcop hBS
  have hSC : S ≤ C := fun s hs => (Subgroup.mem_inf.1 (hS hs)).2
  have hS'N : S.subgroupOf C ≤
      Subgroup.normalizer (((J.subgroupOf C : Subgroup ↥C)) : Set ↥C) := by
    intro s' hs'
    have hsS : (s' : X) ∈ S := Subgroup.mem_subgroupOf.1 hs'
    have hsN : (s' : X) ∈ Subgroup.normalizer (J : Set X) := (Subgroup.mem_inf.1 (hS hsS)).1
    have hN := Subgroup.mem_normalizer_iff.1 hsN
    rw [Subgroup.mem_normalizer_iff]
    intro k
    simpa [Subgroup.mem_subgroupOf] using hN (k : X)
  have hcard : Nat.Coprime 3 (Nat.card (S.subgroupOf C)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv]
    exact hcop
  have hB'N' : B.subgroupOf C ⊓
      Subgroup.normalizer (((J.subgroupOf C : Subgroup ↥C)) : Set ↥C) ≤
      Subgroup.normalizer (((S.subgroupOf C : Subgroup ↥C)) : Set ↥C) := by
    intro b' hb'
    have hb'B : b' ∈ B.subgroupOf C := (Subgroup.mem_inf.1 hb').1
    have hbB : (b' : X) ∈ B := Subgroup.mem_subgroupOf.1 hb'B
    have hbS : (b' : X) ∈ Subgroup.normalizer (S : Set X) :=
      hBS (Subgroup.mem_inf.2 ⟨hbB, hBJ hbB⟩)
    have hN := Subgroup.mem_normalizer_iff.1 hbS
    rw [Subgroup.mem_normalizer_iff]
    intro k
    simpa [Subgroup.mem_subgroupOf] using hN (k : X)
  have hcent := hbal (S.subgroupOf C) hS'N hcard hB'N'
  refine Subgroup.commutator_le.2 (fun h hh s hs => ?_)
  have hcomm : h * s = s * h := by
    have hsC : (⟨s, hSC hs⟩ : ↥C) ∈ S.subgroupOf C := Subgroup.mem_subgroupOf.2 hs
    have hhC : (⟨h, hJC hh⟩ : ↥C) ∈ J.subgroupOf C := Subgroup.mem_subgroupOf.2 hh
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 (hcent hsC) _ hhC)
  rw [commutatorElement_eq_one_iff_mul_comm.2 hcomm]
  exact Subgroup.one_mem _

end KSCompSLOB

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
