module

public import CFSG.ClassicalInvolution.Q3.Q3T6DStmt
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIC7

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section C7


theorem c20_7Three : C20_7Three := by
  intro G _ _ _ K K' J S R R' W V z t d c3 _c4 c5
  have hΩg : HypOmegaGen (CoreAssembly.conjClass K) := d.hypGen
  have hV2 : IsPGroup 2 V := Sec6Gen.isPGroup_of_mem_USet hΩg d.hV
  have tw : Twin20 (CoreAssembly.conjClass K) K K' z (S : Subgroup G) V :=
    ⟨hΩg.conjInvariant, d.viol.hzK, d.twins, d.ne, d.hSz, d.hV, d.hVS, hV2⟩
  have c3' : sec20X (CoreAssembly.conjClass K) z K K' =
      oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (V ⊔ (K ⊔ K')) := c3
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hRmem : R ∈ RSet (CoreAssembly.conjClass K) := mem_RSet_of_isSylow2In hKΩ d.hR
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩg hRmem
  have hzR : z ∈ R := mem_of_isPGroup d.viol.hzK d.hR.1 d.hR.2.1 (by omega)
  have hzS : z ∈ (S : Subgroup G) := d.hRS hzR
  have hzM : K ⊔ K' ≤ Subgroup.centralizer ({z} : Set G) :=
    sup_le (fun w hw => Subgroup.mem_centralizer_singleton_iff.mpr
      (d.viol.hzK.commute_of_mem hw).symm)
      (fun w hw => Subgroup.mem_centralizer_singleton_iff.mpr (tw.hz'.commute_of_mem hw).symm)
  have hzMem : z ∈ K ⊔ K' := Subgroup.mem_sup_left d.viol.hzK.mem
  show centralizerModOdd (S : Subgroup G) (K ⊔ K') = Subgroup.zpowers z
  apply le_antisymm
  · intro u hu
    obtain ⟨huS, huM, huOM, hucomm⟩ := hu
    have huX : u ∈ Subgroup.normalizer
        (sec20X (CoreAssembly.conjClass K) z K K' : Set G) :=
      le_normalizer_sec20X hΩg.conjInvariant d.viol.hzK d.twins (d.hSz huS)
    have huOX := mem_normalizer_oddCore_of_mem_normalizer huX
    have hL := tw.sec20O2_sup_eq c3'
    have hOL := tw.oddCoreOf_sup_eq c3'
    have hOM := tw.oddCoreOf_pair_le c3'
    have hu5 : u ∈ centralizerModOdd (S : Subgroup G)
        (K ⊔ K' ⊔ sec20O2 (sec20X (CoreAssembly.conjClass K) z K K')) := by
      rw [hL]
      refine ⟨huS, mem_normalizer_sup huOX huM, ?_, ?_⟩
      · rw [hOL]
        exact huOX
      · intro l hl
        rw [hOL]
        rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _
          (fun m hm => sec20X_le_normalizer_oddCore (le_sec20X_pair hm))] at hl
        obtain ⟨a, ha, b, hb, rfl⟩ := hl
        rw [commutatorElement_mul_right']
        refine (oddCoreOf _).mul_mem ?_ ((oddCoreOf _).mul_mem
          ((oddCoreOf _).mul_mem ha (hOM (hucomm b hb))) ((oddCoreOf _).inv_mem ha))
        have h1 := mem_normalizer_oddCoreOf_of_mem_normalizer huX ha
        rw [commutatorElement_def]
        exact (oddCoreOf _).mul_mem h1 ((oddCoreOf _).inv_mem ha)
    rw [c5] at hu5
    exact hu5
  · refine Subgroup.zpowers_le.mpr ⟨hzS, Subgroup.le_normalizer hzMem,
      mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer hzMem), ?_⟩
    intro l hl
    have := commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hzM hl)).symm
    rw [this]
    exact (oddCoreOf _).one_mem

end C7

end CFSG.ClassicalInvolution.Q3.Q3T6D
