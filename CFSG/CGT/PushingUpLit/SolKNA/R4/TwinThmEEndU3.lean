module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEEndQuat
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf26U3Out
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Hyp

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW

namespace ThmE

section U3


theorem e178U3_of_twin {r : ℕ} (hr : 3 ≤ r) :
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
      (R W H : Subgroup G), MinCex r Ω K S R W H →
        ∀ z : G, IsUniqueInvolution K z →
          IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G))
            (Subgroup.centralizer ({z} : Set G)) →
          IsSimpleGroup ↥(Subgroup.normalClosure ({z} : Set G)) →
          (∃ x ∈ Subgroup.normalClosure ({z} : Set G), ∃ y ∈ Subgroup.normalClosure ({z} : Set G),
            x * y ≠ y * x) →
          Subgroup.centralizer ((Subgroup.normalClosure ({z} : Set G) : Subgroup G) : Set G) = ⊥ →
          (∃ n : ℕ, Nonempty (↥(Subgroup.normalClosure ({z} : Set G)) ≃* BenderSuzuki.PSU3Model n)) →
          BenderSuzuki.IsStronglyEmbeddedOrder (H.subgroupOf (Subgroup.normalClosure ({z} : Set G))) →
          False := by
  intro G _ _ Ω K S R W H c z hz hSyl hFs hnab hFc hP hSE
  classical
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨K', hK'tw, hK'ne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  obtain ⟨hK'Ω, z', hzK, hzK'⟩ := hK'tw
  have hzz' : z = z' := hz.eq hzK
  have hzK'z : IsUniqueInvolution K' z := hzz' ▸ hzK'
  have hquat : ∀ P ∈ RSet Ω, Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))) := by
    intro P hP
    obtain ⟨J, hJ, hPJ⟩ := exists_isSylow2In_of_mem_RSet hP
    exact TwinDisc.forall_sylow_iso_of_exists (c.stand.quat J hJ) P hPJ
  obtain ⟨eR⟩ := hquat R hRR
  obtain ⟨eR'⟩ := hquat R' hR'
  obtain ⟨a, haR, b, hbR, hQ⟩ := EndGame.exists_u3QTriple_quat hr hz hRK eR
  obtain ⟨a', ha'R, b', hb'R, hQ'⟩ := EndGame.exists_u3QTriple_quat hr hzK'z hR'K' eR'
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

end U3

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
