module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3Mathieu
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3SporCheck
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3SporCheckB
public import CFSG.Sporadic.Schreier.PairJ2Order
public import CFSG.Sporadic.Schreier.PairHSOrder
public import CFSG.Sporadic.Schreier.PairMcLOrder
public import CFSG.Sporadic.HeldB.CertPBridge
public import CFSG.Sporadic.SuzOddCore.SmallModel
public import CFSG.Sporadic.SuzOddCore.SmallChain
public import CFSG.Sporadic.Schreier.Co3Order
public import CFSG.Sporadic.Co2Cert.Order

public section

namespace CFSG.EvenSmallLie.Child3.SelK3

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

section J2

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative


theorem k3_j2P : K3 j2P :=
  k3_of_check (n := 315) (D := j2K3) rfl (by norm_num) (T := j2P)
    (gG := fun l => if l = 0 then j2Gen 0 else j2Gen 1)
    (pair_gens (rep_ofNatArr (by norm_num) (rep_j2StrongPerm (by norm_num)))
      (rep_ofNatArr (by norm_num) (rep_j2StrongPerm (by norm_num)))
      (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))
    j2K3_check (a := 3) (m := 22400) (by rw [card_j2P]; norm_num) (by norm_num) rfl


theorem excluded_J2 : ExcludedSource (CFSG.Blueprint.NativeSporadic.Carrier .J2) :=
  false_of_k3 (K3.of_mulEquiv j2PermEquiv k3_j2P)

end J2

section HS

open CFSG.Sporadic.Schreier


theorem k3_hsP : K3 hsP :=
  k3_of_check (n := 3850) (D := hsK3) rfl (by norm_num) (T := hsP)
    (gG := fun l => if l = 0 then hsGen 0 else hsGen 1)
    (pair_gens (rep_ofNatArr (by norm_num) (rep_hsGen (by norm_num)))
      (rep_ofNatArr (by norm_num) (rep_hsGen (by norm_num)))
      (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))
    hsK3_check (a := 2) (m := 4928000) (by rw [card_hsP]; norm_num) (by norm_num) rfl


theorem excluded_HS : ExcludedSource (CFSG.Blueprint.NativeSporadic.Carrier .HS) :=
  false_of_k3 (K3.of_mulEquiv hsPermEquiv k3_hsP)

end HS

section McL

open CFSG.Sporadic.Schreier


theorem k3_mclP : K3 mclP :=
  k3_of_check (n := 275) (D := mclK3) rfl (by norm_num) (T := mclP)
    (gG := fun l => if l = 0 then mclGen 0 else mclGen 1)
    (pair_gens (rep_ofNatArr (by norm_num) (rep_mclGen (by norm_num)))
      (rep_ofNatArr (by norm_num) (rep_mclGen (by norm_num)))
      (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))
    mclK3_check (a := 6) (m := 1232000) (by rw [card_mclP]; norm_num) (by norm_num) rfl


theorem excluded_McL : ExcludedSource (CFSG.Blueprint.NativeSporadic.Carrier .McL) :=
  false_of_k3 (K3.of_mulEquiv mclPermEquiv k3_mclP)

end McL

section He

open CFSG.Sporadic.HeldB


theorem k3_heP : K3 heP :=
  k3_of_check (n := 8330) (D := heK3) rfl (by norm_num) (T := heP)
    (gG := fun l => if l = 0 then heGenPerm 0 else heGenPerm 1)
    (pair_gens (rep_ofNatArr (by norm_num) (rep_heGen (by norm_num)))
      (rep_ofNatArr (by norm_num) (rep_heGen (by norm_num)))
      (heGenPerm_mem (by norm_num)) (heGenPerm_mem (by norm_num)))
    heK3_check (a := 3) (m := 149273600) (by rw [card_heP]; norm_num) (by norm_num) rfl


theorem excluded_He : ExcludedSource (CFSG.Blueprint.NativeSporadic.Carrier .He) :=
  false_of_k3 (K3.of_mulEquiv heEquivP k3_heP)

end He

section Suz

open CFSG.Sporadic.SuzOddCore


theorem k3_suzM : K3 suzM :=
  k3_of_check (n := 1782) (D := suzK3) rfl (by norm_num) (T := suzM)
    (gG := fun l => if l = 0 then suzB0 else suzB1)
    (pair_gens (rep_ofNatArr (by norm_num) rep_b0) (rep_ofNatArr (by norm_num) rep_b1)
      (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))
    suzK3_check (a := 7) (m := 205004800) (by rw [suzM_card_chain]; norm_num) (by norm_num) rfl


theorem excluded_Suz : ExcludedSource (CFSG.Blueprint.NativeSporadic.Carrier .Suz) :=
  false_of_k3 (K3.of_mulEquiv suzEquivM k3_suzM)

end Suz

section Co3

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3


theorem k3_co3P : K3 co3P :=
  k3_of_check (n := 276) (D := co3K3) rfl (by norm_num) (T := co3P)
    (gG := fun l => if l = 0 then co3GenPerm 0 else co3GenPerm 1)
    (pair_gens (rep_ofNatArr (by norm_num) (rep_co3GenPerm (by norm_num)))
      (rep_ofNatArr (by norm_num) (rep_co3GenPerm (by norm_num)))
      (co3GenPerm_mem 0 (by norm_num)) (co3GenPerm_mem 1 (by norm_num)))
    co3K3_check (a := 7) (m := 226688000) (by rw [card_co3P]; norm_num) (by norm_num) rfl


theorem excluded_Co3 : ExcludedSource (CFSG.Blueprint.NativeSporadic.Carrier .Co3) :=
  false_of_k3 (K3.of_mulEquiv co3PermEquiv k3_co3P)

end Co3

section Co2

open CFSG.Sporadic.Co2Cert


theorem k3_co2P : K3 co2P :=
  k3_of_check (n := 2300) (D := co2K3) rfl (by norm_num) (T := co2P)
    (gG := fun l => if l = 0 then co2Gen 0 else co2Gen 1)
    (pair_gens (rep_ofNatArr (by norm_num) (rep_co2Gen (by norm_num)))
      (rep_ofNatArr (by norm_num) (rep_co2Gen (by norm_num)))
      (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))
    co2K3_check (a := 6) (m := 58032128000) (by rw [card_co2P]; norm_num) (by norm_num) rfl


theorem excluded_Co2 : ExcludedSource (CFSG.Blueprint.NativeSporadic.Carrier .Co2) :=
  false_of_k3 (K3.of_mulEquiv co2PermEquiv k3_co2P)

end Co2

section Bundle


theorem sporadicExclusions : SporadicExclusions where
  M22 := excluded_M22
  M23 := excluded_M23
  M24 := excluded_M24
  J2 := excluded_J2
  HS := excluded_HS
  McL := excluded_McL
  He := excluded_He
  Suz := excluded_Suz
  Co3 := excluded_Co3
  Co2 := excluded_Co2

end Bundle

end CFSG.EvenSmallLie.Child3.SelK3
