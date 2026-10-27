module

public import CFSG.ClassicalInvolution.Q3.Q3TIYAtT
public import CFSG.ClassicalInvolution.Q3.Q3TIYDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIV

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinElt TwinElt.u IsTwinAt TwinRow TwinDatumOn
  TwinMFCommutantOn)


theorem twinYNoCentral3_of_model {P : StatedLieTag → ℕ → Prop}
    (hMF : ∀ tY nY, TwinRow tY nY → P tY nY →
      TwinMFCommutantOn tY (modelUniv tY nY 3 1 Nat.prime_three)) :
    Q3TIY.TwinYNoCentral3On P := by
  intro h3 G _ _ _ hnab K z hR tY nY hrow hP hshape T hT clsT e M hM
  by_contra hno
  push Not at hno
  have hex : ExactMembers3 (conjClass3 K) := hR.setup.1
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hKT' : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hncs := not_commutes_self_of_mem3 hR
  obtain ⟨c⟩ := TwinLoc3.of_setup (twinRowFacts3_of_row hrow) h3 hR hshape
  obtain ⟨J, hJ, hJK, hJT⟩ := c.exists_big_member (fun N hN hNK => hT.comm_K N hN hNK)
    (fun N hN hNT => hT.comm_T N hN hNT)
  obtain ⟨t, hJt⟩ := hR.inClass.classical J hJ.1
  have htz : t ≠ z := involution_ne_of_member3 h3 hnab hR hrow hshape hT hJ hJK hJT hJt
  obtain ⟨A⟩ := exists_atT3 h3 hR hrow hshape hT clsT hJ hJK hJT hJt htz
  have hMJ : Commutes M J := hno J hJ hJK hJT
  have hMJ₂ : Commutes M A.J₂ := hno A.J₂ A.hJ₂z A.hJ₂K A.hJ₂T
  have hMt : M ∈ centralizingMembers (conjClass3 K) {t} :=
    ⟨hM.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hMJ y hy t hJt.mem)⟩
  have hMJne : M ≠ J := fun h => hncs J hJ.1 (by rw [h] at hMJ; exact hMJ)
  have hMJ₂ne : M ≠ A.J₂ := fun h => hncs A.J₂ A.hJ₂t.1 (by rw [h] at hMJ₂; exact hMJ₂)
  obtain ⟨RM, hRM, hMR⟩ := A.c.big_of_ne A.hJt A.hJ₂t A.hJ₂J.symm A.hJiso A.hJ₂iso hMt hMJne
    hMJ₂ne
  have hcomm : ∀ S' ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
      Commutes S' A.RK → Commutes S' A.RT → Commutes RM S' := by
    intro S' hS' hcK hcT
    obtain ⟨L, hLmem, hLS⟩ := mem_locFamily_iff.mp (A.c.d.mem_fam S' hS')
    have hLJ : L ≠ J := by
      intro h
      subst h
      exact A.c.not_fund_of_isolated hLmem A.hJiso hS' hLS
    have hLJ₂ : L ≠ A.J₂ := by
      intro h
      subst h
      exact A.c.not_fund_of_isolated hLmem A.hJ₂iso hS' hLS
    have hLK : Commutes L K := (A.c.commutes_iff_fund hLmem A.hKt hS' hLS A.hKR).mpr hcK
    have hLT : Commutes L T := (A.c.commutes_iff_fund hLmem A.hTt hS' hLS A.hTR).mpr hcT
    have hLz : L ∈ centralizingMembers (conjClass3 K) {z} :=
      ⟨hLmem.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
        (hLK y hy z hR.cls.mem)⟩
    have hLK' : L ≠ K := fun h => hncs K hKΩ (by rw [h] at hLK; exact hLK)
    have hLT' : L ≠ T := fun h => hncs T hT.mem.1 (by rw [h] at hLT; exact hLT)
    exact (A.c.commutes_iff_fund hMt hLmem hRM hMR hLS).mp (hno L hLz hLK' hLT')
  have hMKu : K ∉ centralizingMembers (conjClass3 K) {e.u} := fun h =>
    twinElt_not_le_centralizer_left3 e hR.cls (hex K hKΩ) hKT' h.2
  have hMTu : T ∉ centralizingMembers (conjClass3 K) {e.u} := fun h =>
    twinElt_not_le_centralizer_right3 e clsT (hex T hT.mem.1) hKT' h.2
  rcases hMF tY nY hrow hP A.RK A.RT A.x A.x' A.hdat RM hRM hcomm with h | h
  · have hMK : M = K := locImg_injOn3 A.c.hΩ A.c.hex A.c.hP1 A.c.hO3 hMt A.hKt
      (by rw [hMR, A.hKR, h])
    exact hMKu (hMK ▸ hM)
  · have hMT : M = T := locImg_injOn3 A.c.hΩ A.c.hex A.c.hP1 A.c.hO3 hMt A.hTt
      (by rw [hMR, A.hTR, h])
    exact hMTu (hMT ▸ hM)

end CFSG.ClassicalInvolution.Q3.Q3TIV
