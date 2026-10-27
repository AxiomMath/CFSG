module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Odd

public section

namespace CFSG.EvenSporadicStandard.Co2Std

open Subgroup

variable {G : Type} [Group G]

theorem TwoCentralSetting.of_facts {L : Subgroup G} {z : G} (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hC : centralizer ({z} : Set G) = L ⊔ zpowers z) (hd : Disjoint L (zpowers z))
    (hF : Co2Facts L) :
    ∃ (t : G) (SL : Subgroup G), TwoCentralSetting G L z t SL := by
  obtain ⟨S, t0, hSp, hmax, ht0S, ht01, ht02, ht0c, hZ⟩ := hF.sylow
  have hinj := L.subtype_injective
  have hSLp : IsPGroup 2 (S.map L.subtype) :=
    hSp.of_equiv (Subgroup.equivMapOfInjective S L.subtype hinj)
  refine ⟨(t0 : G), S.map L.subtype, ?_⟩
  refine
    { z_ne := hz1
      z_sq := hz2
      centralizer_z := hC
      disjoint := hd
      t_mem := t0.2
      t_ne := fun h1 => ht01 (Subtype.ext h1)
      t_sq := by simpa using congrArg Subtype.val ht02
      sq_of_invol := fun v hv hv2 hv1 => ?_
      le := by rintro _ ⟨s, -, rfl⟩; exact s.2
      pgroup := hSLp
      maximal := fun R hRL hRp hSR => ?_
      t_mem_SL := ⟨t0, ht0S, rfl⟩
      t_comm := ?_
      center_eq := ?_ }
  · obtain ⟨w, hw⟩ := hF.sq_of_invol ⟨v, hv⟩ (Subtype.ext (by simpa using hv2))
      (fun h1 => hv1 (congrArg Subtype.val h1))
    exact ⟨(w : G), w.2, by simpa using congrArg Subtype.val hw⟩
  · have hR' : IsPGroup 2 (R.subgroupOf L) :=
      hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRL).symm
    have hSR' : S ≤ R.subgroupOf L := fun s hs => hSR ⟨s, hs, rfl⟩
    have hRS := hmax _ hR' hSR'
    calc R = (R.subgroupOf L).map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hRL).symm
      _ = S.map L.subtype := by rw [hRS]
  · rintro _ ⟨s, hs, rfl⟩
    exact congrArg Subtype.val (ht0c s hs)
  · rintro _ ⟨c, hc, rfl⟩ hcc
    have : c = 1 ∨ c = t0 := by
      refine hZ c hc fun s hs => ?_
      exact Subtype.ext (hcc _ ⟨s, hs, rfl⟩)
    rcases this with rfl | rfl
    · left; simp
    · right; rfl

end CFSG.EvenSporadicStandard.Co2Std
