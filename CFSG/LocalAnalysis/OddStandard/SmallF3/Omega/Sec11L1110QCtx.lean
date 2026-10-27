module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109BCard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L1110Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem mem_twoCoreIn_iff' {X : Subgroup G} {x : G} (hx : x ∈ X) :
    x ∈ twoCoreIn X ↔ (⟨x, hx⟩ : ↥X) ∈ CFSG.pCore 2 ↥X := by
  unfold twoCoreIn CFSG.inSubgroup
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rwa [this] at hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

private theorem map_invol_eq_neg_one {X : Subgroup G} (e : ↥X ≃* SL23) {w : G} (hw : w ∈ X)
    (hw2 : w * w = 1) (hw1 : w ≠ 1) : e ⟨w, hw⟩ = -1 := by
  have hsq : (⟨w, hw⟩ : ↥X) * ⟨w, hw⟩ = 1 := Subtype.ext hw2
  have hsq' : e ⟨w, hw⟩ * e ⟨w, hw⟩ = 1 := by rw [← map_mul, hsq, map_one]
  rcases sl23_unique_involution _ hsq' with h | h
  · exfalso
    apply hw1
    have h1 : (⟨w, hw⟩ : ↥X) = 1 := e.injective (by rw [h, map_one])
    simpa using congrArg Subtype.val h1
  · exact h

private theorem invol_mem_twoCoreIn {X : Subgroup G} (e : ↥X ≃* SL23) {z : G} (hz : z ∈ X)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) : z ∈ twoCoreIn X := by
  rw [mem_twoCoreIn_iff' hz]
  have hmem : e ⟨z, hz⟩ ∈ CFSG.pCore 2 SL23 := by
    rw [map_invol_eq_neg_one e hz hz2 hz1]
    exact sl23_neg_one_mem_pCore
  rw [← CFSG.pCore_map_iso 2 e] at hmem
  obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp hmem
  have hy' : y = ⟨z, hz⟩ := e.injective hye
  rwa [hy'] at hy

private theorem sq_one_mem_zpowers {X : Subgroup G} (e : ↥X ≃* SL23) {z : G} (hz : z ∈ X)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) {a : G} (ha : a ∈ X) (haa : a * a = 1) :
    a ∈ zpowers z := by
  have hsq : e ⟨a, ha⟩ * e ⟨a, ha⟩ = 1 := by
    rw [← map_mul, show (⟨a, ha⟩ : ↥X) * ⟨a, ha⟩ = 1 from Subtype.ext haa, map_one]
  rcases sl23_unique_involution _ hsq with h | h
  · have h1 : (⟨a, ha⟩ : ↥X) = 1 := e.injective (by rw [h, map_one])
    have ha1 : a = 1 := by simpa using congrArg Subtype.val h1
    rw [ha1]
    exact one_mem _
  · have h' : e ⟨a, ha⟩ = e ⟨z, hz⟩ := by rw [h, map_invol_eq_neg_one e hz hz2 hz1]
    have haz : a = z := congrArg Subtype.val (e.injective h')
    rw [haz]
    exact Subgroup.mem_zpowers z

theorem sec11L1110_q8pair [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) :
    Sec11Q8Pair z (twoCoreIn K1) (twoCoreIn K2) := by
  have hpsp : IsPSp43 L := (hp.basic G t L S z hctx.toSec10Z).1
  have hP5 := hp.facts.pockets5
  have hC5 := hp.facts.centZ5
  obtain ⟨-, hz2, -, -, hz1⟩ := sec11_invols hctx
  obtain ⟨⟨e1⟩, ⟨e2⟩⟩ := sec10KS_equiv hP5 hC5 hpsp hctx
  have hzK1 : z ∈ K1 := hctx.pocket1.1
  have hzK2 : z ∈ K2 := hctx.pocket2.1
  have hmain : K1 ⊓ K2 = zpowers z := (sec10KS_main hP5 hC5 hpsp hctx).2.2
  exact
    { z_sq := hz2
      z_ne := hz1
      z_mem1 := invol_mem_twoCoreIn e1 hzK1 hz2 hz1
      z_mem2 := invol_mem_twoCoreIn e2 hzK2 hz2 hz1
      comm := fun a ha b hb => sec10Z_comm hP5 hpsp hctx a (twoCoreIn_le_self K1 ha) b
        (twoCoreIn_le_self K2 hb)
      inf := fun x h1 h2 => by
        rw [← hmain]
        exact Subgroup.mem_inf.mpr ⟨twoCoreIn_le_self K1 h1, twoCoreIn_le_self K2 h2⟩
      elem1 := sec10KS_Qi_elem hP5 hC5 hpsp hctx
      elem2 := sec10KS_Qi_elem hP5 hC5 hpsp hctx.swap
      center1 := sec10KS_Qi_center hP5 hC5 hpsp hctx
      center2 := sec10KS_Qi_center hP5 hC5 hpsp hctx.swap
      invol1 := fun a ha haa => sq_one_mem_zpowers e1 hzK1 hz2 hz1 (twoCoreIn_le_self K1 ha) haa
      invol2 := fun a ha haa => sq_one_mem_zpowers e2 hzK2 hz2 hz1 (twoCoreIn_le_self K2 ha) haa
      card1 := sec10B_card_twoCoreIn K1 e1
      card2 := sec10B_card_twoCoreIn K2 e2 }

end CFSG.OddStandard.SmallF3.Omega
