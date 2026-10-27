module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63Syl
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63Burn
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63E1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.ExtremalTransfer

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y63_ext (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) (hY : Y63Hyps c)
    (hRT : c.s.R = c.s.T) (h61 : c.Fact61) (hC : Y63Concl c) (hS : IsSylowIn 2 ⊤ (y63Q c)) :
    ∀ x : G, IsExtremalConj (y63Q c) c.s.t x → x ∉ S3 c.s := by
  intro x hx hxS
  obtain ⟨hxQ, hxt, hmax⟩ := hx
  have cfg := c.y6cfg hH
  have hxord : orderOf x = 2 := by
    obtain ⟨d, hd⟩ := isConj_iff.mp hxt
    rw [← hd, ← c.s.t_order]
    simpa [MulAut.conj_apply] using (MulAut.conj d).orderOf_eq c.s.t
  have hTQ : c.s.T ≤ y63Q c := le_sup_left
  have hTcent : c.s.T ≤ centEl (y63Q c) c.s.t := le_inf hTQ c.s.sylow_T.1
  have hTcount : Nat.card ↥c.s.T ≤ Nat.card ↥(centEl (y63Q c) c.s.t) :=
    Subgroup.card_le_of_le hTcent
  have hmaxT : Nat.card ↥(centEl (y63Q c) c.s.t) ≤ Nat.card ↥(centEl (y63Q c) x) :=
    hmax c.s.t hY.t_mem (IsConj.refl c.s.t)
  have hle : 2 ^ 7 ≤ Nat.card ↥(centEl (y63Q c) x) := by
    have h128 : Nat.card ↥c.s.T = 128 := (y6_card_T hH).1 hRT
    rw [show (2 : ℕ) ^ 7 = 128 by norm_num]
    omega
  obtain ⟨y, hy, hCy⟩ :=
    y63_extr_cent (Q := y63Q c) (T := c.s.T) (t := c.s.t) (x := x)
      (y63_Q_pgroup hY) c.s.sylow_T hxt (le_trans hTcount hmaxT)
  have hnot := y63_not_mem_comm c hH hRT hy hCy
  obtain ⟨hxC1, hzC'⟩ := hC.good x hxS hxord hle hnot
  have hyz : y * c.s.fr.z * y⁻¹ = c.s.fr.z := y63_y_cent_z c hH hF hRT hCy hzC'
  let K : Subgroup G := Subgroup.centralizer ({c.s.fr.z} : Set G)
  let Z : Subgroup G := zpowers c.s.fr.z
  have hzc : c.s.fr.z ∈ cen (y63Q c) := y63_z_mem_cen_Q c hH hF hRT
  have hz_comm : ∀ q ∈ y63Q c, q * c.s.fr.z = c.s.fr.z * q :=
    fun q hq => (Subgroup.mem_centralizer_iff.mp hzc.2) q hq
  have hQK : y63Q c ≤ K :=
    fun q hq => Subgroup.mem_centralizer_singleton_iff.mpr (hz_comm q hq)
  have hQsyl : IsSylowIn 2 K (y63Q c) := y63_sylow_of_le hS hQK
  have hZE : Y63ZE64 Z (C1 c.e) := y63_C1_ZE64 c hH
  have hZK : ∀ k ∈ K, ∀ w ∈ Z, k * w * k⁻¹ = w := by
    intro k hk w hw
    have hkz : c.s.fr.z * k = k * c.s.fr.z :=
      (Subgroup.mem_centralizer_singleton_iff.mp hk).symm
    have hle_cen : Z ≤ Subgroup.centralizer ({k} : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hkz)
    have hwcomm : w * k = k * w := Subgroup.mem_centralizer_singleton_iff.mp (hle_cen hw)
    rw [← hwcomm]; group
  have hweak : ∀ k ∈ K, conjSub k (C1 c.e) ≤ y63Q c → conjSub k (C1 c.e) = C1 c.e := by
    intro k hk hkle
    exact hC.uniq (conjSub k (C1 c.e)) hkle (y63_ZE64_conj hZE (hZK k hk))
  have hyK : y ∈ K := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc y * c.s.fr.z = (y * c.s.fr.z * y⁻¹) * y := by group
      _ = c.s.fr.z * y := by rw [hyz]
  have htC1 : c.s.t ∈ C1 c.e := y63_t_mem_C1 c hH
  have hga : y * c.s.t * y⁻¹ ∈ C1 c.e := by rw [hy]; exact hxC1
  obtain ⟨n, _hnK, hnN, w, hwZ, hnt⟩ :=
    y63_burn_modZ (K := K) (Q := y63Q c) (U := C1 c.e) (Z := Z)
      hQsyl (y63_C1_le_Q c hH) hZE.1 hZK hZE.2.2.2 hweak htC1 hyK hga
  have hxAV : x ∈ AV1 c.e := y63_C1_inf_S3_le c hH hY ⟨hxC1, hxS⟩
  have hwA : w ∈ c.s.fr.A := (Subgroup.zpowers_le.mpr (y6_z_mem_A cfg)) hwZ
  have hxwAV : x * w ∈ AV1 c.e := mul_mem hxAV (Subgroup.mem_sup_left hwA)
  have hAV_le_C1 : AV1 c.e ≤ C1 c.e := by
    show c.s.fr.A ⊔ V1 c.e ≤ c.s.fr.A ⊔ C0 c.e
    exact sup_le le_sup_left (le_trans inf_le_left le_sup_right)
  have hxwC1 : x * w ∈ C1 c.e := hAV_le_C1 hxwAV
  have hcommV : ∀ v ∈ V1 c.e, (x * w) * v = v * (x * w) :=
    (y6_cent_C1_V cfg (x * w) hxwC1).mpr hxwAV
  have hnV : n ∈ normalizer (V1 c.e : Set G) := h61.2.2.1 (h61.2.1 hnN)
  have huV1 : c.d * c.s.t ∈ V1 c.e := by
    rw [cfg.hV]; exact Subgroup.mem_zpowers (c.d * c.s.t)
  have hvV : n * (c.d * c.s.t) * n⁻¹ ∈ V1 c.e :=
    (Subgroup.mem_normalizer_iff.mp hnV (c.d * c.s.t)).mp huV1
  have hcommUV : (x * w) * (n * (c.d * c.s.t) * n⁻¹)
      = (n * (c.d * c.s.t) * n⁻¹) * (x * w) := hcommV _ hvV
  have hnt' : n * c.s.t * n⁻¹ = x * w := by rw [hnt, hy]
  have htueq : c.s.t * (c.d * c.s.t) = (c.d * c.s.t) * c.s.t := by
    have hh := hcommUV
    rw [← hnt'] at hh
    have h1 : n * (c.s.t * (c.d * c.s.t)) * n⁻¹
        = n * ((c.d * c.s.t) * c.s.t) * n⁻¹ := by
      calc n * (c.s.t * (c.d * c.s.t)) * n⁻¹
          = (n * c.s.t * n⁻¹) * (n * (c.d * c.s.t) * n⁻¹) := by group
        _ = (n * (c.d * c.s.t) * n⁻¹) * (n * c.s.t * n⁻¹) := hh
        _ = n * ((c.d * c.s.t) * c.s.t) * n⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h1)
  have htu : c.s.t * (c.d * c.s.t) * c.s.t⁻¹ = c.d * c.s.t := by
    rw [htueq]; group
  have huu : c.d * c.s.t = (c.d * c.s.t)⁻¹ := by
    rw [← cfg.t_inv, htueq]; group
  have hz1 : c.s.fr.z = 1 := by
    rw [← cfg.u_sq]
    have h2 : (c.d * c.s.t) * (c.d * c.s.t) = 1 := eq_inv_iff_mul_eq_one.mp huu
    simpa [pow_two] using h2
  exact cfg.z_ne hz1

end CFSG.OddStandard.HigherRank.YamadaG23
