module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.GlueProd

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2.Glue

open Subgroup

variable {G : Type} [Group G] {L : Subgroup G} {t : G}

@[expose] def rCen (r : G) : CenG r := ⟨r, mem_centralizer_singleton_iff.2 rfl⟩

theorem orderOf_rCen (r : G) : orderOf (rCen r) = orderOf r := Subgroup.orderOf_mk r _

theorem rCen_mem_center (r : G) : rCen r ∈ center (CenG r) := by
  rw [mem_center_iff]
  intro g
  exact Subtype.ext (mem_centralizer_singleton_iff.1 g.2)

theorem orderOf_tCen (hc : Config G L t) {a : G} (ha : a ∈ L) : orderOf (tCen hc ha) = 2 := by
  rw [tCen, Subgroup.orderOf_mk]
  exact hc.orderOf_z

theorem tCen_mul_self (hc : Config G L t) {a : G} (ha : a ∈ L) :
    tCen hc ha * tCen hc ha = 1 :=
  Subtype.ext hc.z_sq

theorem cen_odd_of [Finite G] (hc : Config G L t) (h3 : RuThreeFacts L) {r : G} (hrL : r ∈ L)
    (hr3 : orderOf r = 3) :
    ∀ x ∈ CFSG.oddCore (CenG r), tCen hc hrL * x * (tCen hc hrL)⁻¹ = x → x ∈ zpowers (rCen r) := by
  intro x hx hcomm
  have hxO : (x : G) ∈ oddCoreCen r := (mem_oddCoreCen_iff x).2 hx
  have hxt : (x : G) * t = t * (x : G) := by
    have h : tCen hc hrL * x = x * tCen hc hrL := by
      calc tCen hc hrL * x = (tCen hc hrL * x * (tCen hc hrL)⁻¹) * tCen hc hrL := by group
        _ = x * tCen hc hrL := by rw [hcomm]
    exact (congrArg Subtype.val h).symm
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (cen_odd_le hc h3 hrL hr3 (oddCoreCen_le r)
    (fun y hy n hn => oddCoreCen_norm r hy hn) (odd_card_oddCoreCen r) hxO hxt)
  exact mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa [rCen] using hk)⟩

theorem rCen_mem_oddCore {r : G} (hr3 : orderOf r = 3) : rCen r ∈ CFSG.oddCore (CenG r) :=
  (mem_oddCoreCen_iff (rCen r)).1 (zpowers_le_oddCoreCen hr3 (mem_zpowers r))

end CFSG.EvenSporadicStandard.RuStd.S2.Glue
