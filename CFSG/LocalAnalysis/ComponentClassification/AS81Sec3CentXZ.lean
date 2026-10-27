module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3CentZOdd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools Sec3 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace Sec38Hyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  (H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀)
include H

theorem z_not_mem_centralizer_sec3B : z ∉ centralizer (sec3B A₁ x : Set G) := by
  have hS := H.q0.dData.suz
  intro hz
  have hzB : z ∈ sec3B A₁ x := hS.T_le (hS.Q_le H.z_mem_Q)
  have hzZ : z ∈ centerIn (sec3B A₁ x) := ⟨hzB, hz⟩
  rw [hS.B_center] at hzZ
  have h3 : orderOf z ∣ 3 := hS.setting.order_x ▸ orderOf_dvd_of_mem_zpowers hzZ
  rw [show orderOf z = 2 from H.xsub.orderOf_z] at h3
  norm_num at h3

theorem odd_card_centralizer_sec3B :
    Odd (Nat.card (centralizer (sec3B A₁ x : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := H.q0.dData.suz
  set W := centralizer (sec3B A₁ x : Set G) with hW
  by_contra hodd
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥W) 2 hodd
  have hzB : z ∈ sec3B A₁ x := hS.T_le (hS.Q_le H.z_mem_Q)
  have hQB : Q ≤ sec3B A₁ x := hS.Q_le.trans hS.T_le
  have hxB : x ∈ centerIn (sec3B A₁ x) := by rw [hS.B_center]; exact mem_zpowers x
  have htz : (t : G) * z = z * t := (mem_centralizer_iff.mp t.2 z hzB).symm
  have ht2 : IsPGroup 2 (zpowers (t : G)) := by
    refine AS76b.isPGroup_zpowers_of_pow_eq_one (n := 1) ?_
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    simpa using congrArg Subtype.val h
  have hz2 : IsPGroup 2 (zpowers z) := by
    refine AS76b.isPGroup_zpowers_of_pow_eq_one (n := 1) ?_
    rw [pow_one, pow_two]
    exact H.xsub.z_mul_z
  have htN : zpowers (t : G) ≤ normalizer ((zpowers z : Subgroup G) : Set G) := by
    rw [zpowers_le]
    refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun c hc => ?_)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    exact (Commute.zpow_left htz.symm k).eq
  have hS2 : IsPGroup 2 ↥(zpowers (t : G) ⊔ zpowers z) := ht2.to_sup_of_normal_right' hz2 htN
  have hSQ : zpowers (t : G) ⊔ zpowers z ≤ centralizer (Q : Set G) := by
    refine sup_le (zpowers_le.mpr (Subgroup.centralizer_le hQB t.2)) (zpowers_le.mpr ?_)
    exact mem_centralizer_iff.mpr fun q hq => mem_centralizer_iff.mp H.z_mem_centerIn_Q.2 q hq
  have hSx : zpowers (t : G) ⊔ zpowers z ≤ centralizer ({x} : Set G) := by
    refine sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr ?_))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr ?_))
    · exact (mem_centralizer_iff.mp t.2 x hxB.1).symm
    · exact mem_centralizer_iff.mp hxB.2 z hzB
  have hcard := card_le_two_of_le_centralizer_Q hS hS2 hSQ hSx
  have htc : Nat.card (zpowers (t : G)) = 2 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ht]
  have hSeq : zpowers (t : G) ⊔ zpowers z = zpowers (t : G) :=
    (Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [htc]; exact hcard)).symm
  have hzS : z ∈ zpowers (t : G) := hSeq ▸ mem_sup_right (mem_zpowers z)
  exact H.z_not_mem_centralizer_sec3B (zpowers_le.mpr t.2 hzS)

theorem centralizer_sec3B_le_normalizer
    (h17 : Step17G24Odd) :
    centralizer (sec3B A₁ x : Set G) ≤ normalizer ((Q₀ ⊔ Q : Subgroup G) : Set G) := by
  have hQ := H.q0
  have hD := hQ.dData
  have hS := hD.suz
  set W := centralizer (sec3B A₁ x : Set G) with hWdef
  have hxB : x ∈ centerIn (sec3B A₁ x) := by rw [hS.B_center]; exact mem_zpowers x
  have hEB : E ≤ sec3B A₁ x :=
    hS.setting.frame.E_le.trans (sup_le (le_sec3B (A₁_le_centralizer hS.setting.toSec3Pre))
      hS.R_le)
  have hBW : sec3B A₁ x ≤ normalizer (W : Set G) := fun b hb =>
    AS81.mem_normalizer_centralizer (le_normalizer hb)
  have hWX := H.le_zpowers_sup_of_odd h17 H.odd_card_centralizer_sec3B (hEB.trans hBW)
    (hBW hxB.1)
  obtain ⟨Kf, _, _, _, -, f, -, l, -, hDf, hQ₀⟩ := exists_sec3Model_Q₀ hQ
  have hQ₀D : Q₀ ≤ D := by
    rw [hQ₀, hDf]
    exact tr_mono
      ((G2.g2Q0_le_g2V l).trans (G2.g2V_le_g2V0.trans G2.g2V0_le_g2ShortParabolicRadical))
  have hDA : D ≤ A := by
    rw [hD.D_eq]
    exact (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
  have hOK : AS76b.oddCoreIn (centralizer (A : Set G)) ≤ centralizer (A : Set G) :=
    AS76b.oddCoreIn_le _
  have hWQ₀ : W ≤ normalizer (Q₀ : Set G) := hWX.trans (sup_le (zpowers_le.mpr hQ.x_Q₀)
    (hOK.trans ((centralizer_le (SetLike.coe_subset_coe.mpr (hQ₀D.trans hDA))).trans
      (centralizer_le_normalizer _))))
  have hWQ : W ≤ normalizer (Q : Set G) :=
    (centralizer_le (SetLike.coe_subset_coe.mpr (hS.Q_le.trans hS.T_le))).trans
      (centralizer_le_normalizer _)
  exact fun w hw => H.mem_normalizer_sup (hWQ₀ hw) (hWQ hw)

theorem mem_normalizer_of_comm
    (h17 : Step17G24Odd)
    (hinner : ∀ w : G, w * x = x * w →
      ∃ b ∈ sec3B A₁ x, b⁻¹ * w ∈ centralizer (sec3B A₁ x : Set G))
    (hCBz : ∀ k ∈ sec3B A₁ x ⊓ centralizer ({z} : Set G), ∃ b₀ ∈ B₀, ∃ i : ℤ, k = b₀ * x ^ i)
    {w : G} (hwx : w * x = x * w) (hwz : w * z = z * w) :
    w ∈ normalizer ((Q₀ ⊔ Q : Subgroup G) : Set G) := by
  have hS := H.q0.dData.suz
  obtain ⟨b, hbB, hbc⟩ := hinner w hwx
  have hzB : z ∈ sec3B A₁ x := hS.T_le (hS.Q_le H.z_mem_Q)
  have hcz : (b⁻¹ * w) * z = z * (b⁻¹ * w) := (mem_centralizer_iff.mp hbc z hzB).symm
  have hbz : b ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc b * z = w * (b⁻¹ * w)⁻¹ * z := by group
      _ = w * ((b⁻¹ * w)⁻¹ * z * (b⁻¹ * w)) * (b⁻¹ * w)⁻¹ := by group
      _ = w * z * (b⁻¹ * w)⁻¹ := by rw [show (b⁻¹ * w)⁻¹ * z * (b⁻¹ * w) = z by
            rw [mul_assoc, ← hcz, ← mul_assoc, inv_mul_cancel, one_mul]]
      _ = z * w * (b⁻¹ * w)⁻¹ := by rw [hwz]
      _ = z * b := by group
  obtain ⟨b₀, hb₀, i, hbi⟩ := hCBz b (mem_inf.mpr ⟨hbB, hbz⟩)
  have hbN : b ∈ normalizer ((Q₀ ⊔ Q : Subgroup G) : Set G) := by
    rw [hbi]
    exact mul_mem (H.B₀_le_N hb₀) (zpow_mem H.x_mem_N i)
  rw [show w = b * (b⁻¹ * w) by group]
  exact mul_mem hbN (H.centralizer_sec3B_le_normalizer h17 hbc)

end Sec38Hyp

end CFSG.ComponentClassification.AS81
