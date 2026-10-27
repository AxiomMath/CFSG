module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.ConfigFus
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.StdKGroup

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Certified


theorem centConfig_of_inner {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : StdHyp G L) (hL : IsSporadic ↥L .Co3) {z t : G} {T₀ : Subgroup G}
    (hcfg : Fin76b.InnerConfig G L z t T₀) (hT₀ : Nat.card T₀ = 2 ^ 10)
    (hdvd : 2 ^ 12 ∣ Nat.card ↥(centralizer ({t} : Set G)))
    (a b : ↥(centralizer ({t} : Set G))) (ha : (a : G) = z) (hb : (b : G) = t) :
    CentConfig ↥(centralizer ({t} : Set G)) a b (L.subgroupOf (centralizer ({t} : Set G)))
      (fun w => IsConj z (w : G)) := by
  let H : Subgroup G := centralizer ({t} : Set G)
  change CentConfig ↥H a b (L.subgroupOf H) (fun w => IsConj z (w : G))
  have hzH : z ∈ H :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (hcfg.z_comm_of_mem_A hcfg.t_mem_A).symm
  have hzpow_le_H : zpowers z ≤ H := Subgroup.zpowers_le.mpr hzH
  have hzpow_le_centL : zpowers z ≤ centralizer (L : Set G) :=
    Subgroup.zpowers_le.mpr hcfg.z_cent
  have hzt : ¬ IsConj z t := not_isConj_z_t hcfg hT₀ hdvd
  have hT₀_sub : T₀ ≤ L ⊓ H := by
    refine le_inf hcfg.T₀_le ?_
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcfg.t_central y hy)
  have h210 : 2 ^ 10 ∣ Nat.card ↥(L ⊓ H) := by
    have hd := Subgroup.card_dvd_of_le hT₀_sub
    rwa [hT₀] at hd
  have htwo_inf : IsTwoSp62 ↥(L ⊓ H) :=
    isTwoSp62_inf_centralizer hL hcfg.t_mem_A hcfg.t_order h210
  refine
    { a_sq := ?_
      a_ne := ?_
      b_sq := ?_
      b_ne := ?_
      b_mem := ?_
      b_central := ?_
      cent_a := ?_
      disj := ?_
      E_two := ?_
      kgroupCat := h.isKGroupCat_centralizer hcfg.t_ne
      oddCore := h.oddCore t hcfg.t_order
      two_pow := hdvd
      fus_a := by simpa [ha] using IsConj.refl z
      fus_b := fun hb' => hzt (by simpa [hb] using hb')
      fus := ?_ }
  · apply Subtype.ext
    simp [ha, hcfg.z_sq]
  · intro h1
    exact hcfg.z_ne (by simpa [ha] using congrArg (fun y : ↥H => (y : G)) h1)
  · apply Subtype.ext
    simp [hb, hcfg.t_sq]
  · intro h1
    exact hcfg.t_ne (by simpa [hb] using congrArg (fun y : ↥H => (y : G)) h1)
  · rw [Subgroup.mem_subgroupOf, hb]
    exact hcfg.t_mem_A
  · rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hb]
    exact Subgroup.mem_centralizer_singleton_iff.mp g.2
  · apply le_antisymm
    · intro x hx
      have hxaa : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.mp hx
      have hxz : (x : G) * z = z * (x : G) := by
        have hh := congrArg (fun y : ↥H => (y : G)) hxaa
        simpa [ha] using hh
      have hxcent : (x : G) ∈ L ⊔ zpowers z := by
        rw [← hcfg.cent_eq]
        exact Subgroup.mem_centralizer_singleton_iff.mpr hxz
      obtain ⟨l, hlL, c, hcZ, hlc⟩ :=
        exists_mul_of_mem_sup_of_le_centralizer hzpow_le_centL hxcent
      have hcH : c ∈ H := hzpow_le_H hcZ
      have hlH : l ∈ H := by
        have hl : l = (x : G) * c⁻¹ := by rw [hlc]; group
        rw [hl]
        exact H.mul_mem x.2 (H.inv_mem hcH)
      have hlH_L : (⟨l, hlH⟩ : ↥H) ∈ L.subgroupOf H :=
        Subgroup.mem_subgroupOf.mpr hlL
      have hcH_zpow : (⟨c, hcH⟩ : ↥H) ∈ zpowers a := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcZ
        exact Subgroup.mem_zpowers_iff.mpr
          ⟨k, Subtype.ext (by simpa [ha] using hk)⟩
      have hx_eq : x = (⟨l, hlH⟩ : ↥H) * ⟨c, hcH⟩ :=
        Subtype.ext (by simpa using hlc)
      rw [hx_eq]
      exact mul_mem (Subgroup.mem_sup_right hlH_L) (Subgroup.mem_sup_left hcH_zpow)
    · refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
      · intro y hy
        exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext (by
          have hh : (y : G) * z = z * (y : G) :=
            Subgroup.mem_centralizer_iff.mp hcfg.z_cent (y : G) hy
          simpa [ha] using hh))
  · rw [disjoint_iff]
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    have hxG_L : (x : G) ∈ L := hx2
    have hxG_z : (x : G) ∈ zpowers z := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx1
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by
        have hh := congrArg (fun y : ↥H => (y : G)) hk
        simpa [ha] using hh⟩
    have hmem : (x : G) ∈ zpowers z ⊓ L := ⟨hxG_z, hxG_L⟩
    have hbot : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← hcfg.disjoint.symm.eq_bot]
      exact hmem
    rw [Subgroup.mem_bot] at hbot
    exact Subtype.ext (by simpa using hbot)
  · let e : ↥(L ⊓ H) ≃* ↥(L.subgroupOf H) :=
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : L ⊓ H ≤ H)).symm.trans
        (MulEquiv.subgroupCongr (Subgroup.inf_subgroupOf_right L H))
    exact IsTwoSp62.of_mulEquiv e htwo_inf
  · intro w hw
    have hwt : (w : G) * t = t * (w : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp w.2
    obtain ⟨hw2, hw1, hcf⟩ := centFacts_of_isConj hL hcfg hzt hw hwt
    exact ⟨Subtype.ext (by simpa using hw2),
      fun h1 => hw1 (by simpa using congrArg (fun y : ↥H => (y : G)) h1),
      CentFacts.of_centralizer_inf H w hcf⟩

end Certified

end CFSG.EvenSporadicStandard.Co3Std.CentT
