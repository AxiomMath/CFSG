module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf11Bender
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf26U3Pure
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf26U3Out
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Hyp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section U3Twin

variable [PrintedQuotOdd] [PrintedQuotCent] [PrintedHull]

theorem e178U3Q8_of_twin : E178U3Q8 := by
  intro G _ _ Ω K S R W H c z hz hSyl hFs hnab hFc hP hSE
  classical
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨K', hK'tw, hK'ne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  obtain ⟨hK'Ω, z', hzK, hzK'⟩ := hK'tw
  have hzz' : z = z' := hz.eq hzK
  have hzK'z : IsUniqueInvolution K' z := hzz' ▸ hzK'
  have hq8 : ∀ P ∈ RSet Ω, Nonempty (↥P ≃* QuaternionGroup 2) := by
    intro P hP
    obtain ⟨J, hJ, hPJ⟩ := exists_isSylow2In_of_mem_RSet hP
    exact TwinDisc.forall_sylow_iso_of_exists (c.stand.q8 J hJ) P hPJ
  obtain ⟨eR⟩ := hq8 R hRR
  obtain ⟨eR'⟩ := hq8 R' hR'
  obtain ⟨a, haR, b, hbR, hQ⟩ := exists_u3QTriple hz hRK eR
  obtain ⟨a', ha'R, b', hb'R, hQ'⟩ := exists_u3QTriple hzK'z hR'K' eR'
  have hRR'2 : IsPGroup 2 ↥(R ⊔ R') := S.isPGroup'.to_le (sup_le hRS hR'S)
  have hcomm : Commutes R R' :=
    Sec6Gen.commutes_of_twin_of_isPGroup hΩ hK hK'Ω (Ne.symm hK'ne) hz hzK'z hRK hR'K' hRR'2
  set L : Subgroup G := Subgroup.normalClosure ({z} : Set G) with hL
  haveI hLn : L.Normal := Subgroup.normalClosure_normal
  have hzL : z ∈ L := Subgroup.subset_normalClosure (Set.mem_singleton z)
  obtain ⟨n, ⟨e⟩⟩ := hP
  haveI := hFs
  have hnabL : ¬ IsMulCommutative ↥L := by
    intro hc
    obtain ⟨x, hx, y, hy, hne⟩ := hnab
    apply hne
    have := hc.is_comm.comm (⟨x, hx⟩ : ↥L) ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hB : BenderSuzuki.IsBenderGroup ↥L :=
    BenderSuzuki.IsBenderGroup.isPSU3 n (psu3_two_le hnabL e) e
  have hc2 := u3_two_group_cases L hFc hB (S : Subgroup G) S.isPGroup'
  obtain ⟨x, hxN, y, hyN, hxS, hyS, hx2, -, hxy⟩ :=
    u3_pair_noncomm (N := L) (S := (S : Subgroup G)) (T := R) (T' := R') hzL hz.sq hc2 hRS hR'S
      hcomm haR hbR ha'R hb'R hQ hQ'
  exact hxy (u3_invols_commute L hnabL e S ⟨hxS, hxN⟩ ⟨hyS, hyN⟩ hx2)

end U3Twin

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
