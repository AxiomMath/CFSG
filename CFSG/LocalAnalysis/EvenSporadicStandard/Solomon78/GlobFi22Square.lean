module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobFi22Model
public import Certificates.Certificate26560

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Fischer CFSG.EvenSporadicStandard.HypOne
open CFSG.EvenSporadicStandard.HypOne.Fi22

theorem fi22_sylowSquareFacts :
    ∃ (S : Subgroup (Equiv.Perm (Fin 3510))) (d : Equiv.Perm (Fin 3510)),
      SylowSquareFacts (centralizerIn fi22P (fi22ExtRep 2)) S (fi22ExtRep 2) d :=
  Certificates.certificate26560

theorem fi22_squareFacts :
    ∃ (S : Subgroup (Equiv.Perm (Fin 3510))) (d : Equiv.Perm (Fin 3510)),
      SquareFacts (centralizerIn fi22P (fi22ExtRep 2)) S (fi22ExtRep 2) d := by
  obtain ⟨S, d, h⟩ := fi22_sylowSquareFacts
  exact ⟨S, d,
    { toSylowSquareFacts := h
      u_mem := mem_centralizerIn.2 ⟨fi22ExtRep_two_mem, rfl⟩
      u_central := fun k hk => (mem_centralizerIn.1 hk).2
      u_sq := by
        have h := pow_orderOf_eq_one (fi22ExtRep 2)
        rw [orderOf_fi22ExtRep (k := 2) (by norm_num)] at h
        rw [← pow_two]
        exact h
      central_inv := fun z hz hzz hzc =>
        centerInv_fi22 (fi22ExtRep 2) fi22ExtRep_two_mem (orderOf_fi22ExtRep (by norm_num)) z
          (mem_centralizerIn.1 hz).1 hzz (mem_centralizerIn.1 hz).2
          (fun y hy hyt => hzc y (mem_centralizerIn.2 ⟨hy, hyt⟩)) }⟩

theorem fi22_squareFacts_P :
    ∃ (S : Subgroup fi22P) (d : fi22P),
      SquareFacts (centralizer ({(⟨fi22ExtRep 2, fi22ExtRep_two_mem⟩ : fi22P)} : Set fi22P)) S
        ⟨fi22ExtRep 2, fi22ExtRep_two_mem⟩ d := by
  have hK : centralizerIn fi22P (fi22ExtRep 2) ≤ fi22P.subtype.range := by
    rw [Subgroup.range_subtype]
    exact inf_le_left
  obtain ⟨S, d, hF⟩ := fi22_squareFacts
  have hδ : d ∈ fi22P := hF.d_mem.1
  have h := hF.comap fi22P.subtype Subtype.coe_injective hK
    (u' := ⟨fi22ExtRep 2, fi22ExtRep_two_mem⟩) (d' := ⟨d, hδ⟩) rfl rfl
  have hKeq : (centralizerIn fi22P (fi22ExtRep 2)).comap fi22P.subtype =
      centralizer ({(⟨fi22ExtRep 2, fi22ExtRep_two_mem⟩ : fi22P)} : Set fi22P) := by
    ext x
    rw [Subgroup.mem_comap, mem_centralizerIn, mem_centralizer_singleton_iff]
    exact ⟨fun h => Subtype.ext h.2, fun h => ⟨x.2, congrArg Subtype.val h⟩⟩
  rw [hKeq] at h
  exact ⟨_, _, h⟩

end CFSG.EvenSporadicStandard.Solomon78
