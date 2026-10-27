module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10F107Case
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10F107Setup
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactPockets
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Fact107c_of_pockets
    (hP5 : Asc82FactPockets5) : Asc82Fact107c := by
  intro G _ _ t L S z K1 K2 hctx hL hSN hCS hP
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have hK1 := hctx.pocket1
  have hK2 := hctx.pocket2
  have hzL : z ∈ L := (Subgroup.mem_inf.1 (hK1.2.1 hK1.1)).1
  have hzP : z ∈ centerIn (S ⊓ L) :=
    mem_centerIn_iff.2 ⟨Subgroup.mem_inf.2 ⟨hctx.mem_S, hzL⟩, fun y hy =>
      (hctx.central y (Subgroup.mem_inf.1 hy).1).symm⟩
  obtain ⟨F, hFP, hQL, hQ⟩ := exists_frame_Q32 hP5 hL hP hzP hz2 hK1 hK2 hctx.ne
  have ht2 : orderOf t = 2 := hctx.involution
  have htsq : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at h
  have htne : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    omega
  have hSetup : PspFrame.Setup107 L t S :=
    { S_le_N := hSN
      S_two := hctx.sylow.2.1
      t_sq := htsq
      t_ne := htne
      t_comm := fun s hs => Subgroup.mem_centralizer_singleton_iff.1 (hctx.sylow.1 hs)
      cent_S := hCS }
  exact hSetup.case107 hFP hQL hQ hL

theorem asc82Fact107c_of_cert :
    Asc82Fact107c :=
  asc82Fact107c_of_pockets asc82FactPockets5_of_cert

end CFSG.OddStandard.SmallF3.Omega
