module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81E6b
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81E6a

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁}

section Fusion

variable {v : H} (hv : d.IsV v) (I : In81) (F : d.Facts)
include hv I F

theorem not_conj_mul_sigma {e : H} (he : e ∈ h.D ⊔ h.P) (heZ : e * d.sigma ∈ h.ZF32) (c : H) :
    c⁻¹ * h.a * c ≠ e * d.sigma := by
  have hσ := d.sigma_not_mem_DP I.cf1 I.cf2 F
  intro hc
  have hZ : c⁻¹ * h.a * c ∈ h.ZF32 := by rw [hc]; exact heZ
  apply hσ
  rcases conj_a_of_mem_ZF hv I F hZ with h1 | h1
  · rw [eq_inv_mul_of_mul_eq (hc.symm.trans h1)]
    exact mul_mem (inv_mem he) (mem_sup_right h.toHyp52.a_mem_P)
  · rw [eq_inv_mul_of_mul_eq (hc.symm.trans h1)]
    exact mul_mem (inv_mem he) (mem_sup_left d.z_D)

theorem e6_not_conj_mul_b {w : H}
    (hw : w = h.a ∨ w = d.z ∨ w = h.a * d.z * d.tau ∨ w = d.z * d.tau) (c : H) :
    c⁻¹ * h.a * c ≠ w * d.b := by
  have hazZ : h.a * d.z * d.sigma ∈ h.ZF32 :=
    mul_mem (mul_mem (a_mem_ZF I F) (z_mem_ZF I F)) (sigma_mem_ZF I F)
  have hzZ : d.z * d.sigma ∈ h.ZF32 := mul_mem (z_mem_ZF I F) (sigma_mem_ZF I F)
  have hzDP : d.z ∈ h.D ⊔ h.P := mem_sup_left d.z_D
  have hazDP : h.a * d.z ∈ h.D ⊔ h.P := mul_mem (mem_sup_right h.toHyp52.a_mem_P) hzDP
  have haz : h.a * d.z = d.z * h.a := (d.z_comm_a).symm
  have hzb : (h.x * d.g)⁻¹ * (d.z * d.b) * (h.x * d.g) = h.a * d.z * d.sigma := by
    rw [show (h.x * d.g)⁻¹ * (d.z * d.b) * (h.x * d.g) =
        d.g⁻¹ * (h.x⁻¹ * d.z * h.x) * d.g * (d.g⁻¹ * (h.x⁻¹ * d.b * h.x) * d.g) by group,
      x_inv_z_x, x_inv_b_x,
      show d.g⁻¹ * (h.a * d.b) * d.g = (d.g⁻¹ * h.a * d.g) * (d.g⁻¹ * d.b * d.g) by group,
      F.z_g, d.a_g, g_inv_b_g,
      show d.z * (h.a * d.tau * d.b) = d.z * h.a * (d.tau * d.b) by group, ← haz]
  intro hc
  rcases hw with rfl | rfl | rfl | rfl
  ·
    apply not_conj_a_b hv I F (c * h.x⁻¹)
    calc (c * h.x⁻¹)⁻¹ * h.a * (c * h.x⁻¹) = h.x * (c⁻¹ * h.a * c) * h.x⁻¹ := by group
      _ = h.x * (h.x⁻¹ * d.b * h.x) * h.x⁻¹ := by rw [hc, x_inv_b_x]
      _ = d.b := by group
  ·
    apply not_conj_mul_sigma hv I F hazDP hazZ (c * (h.x * d.g))
    rw [show (c * (h.x * d.g))⁻¹ * h.a * (c * (h.x * d.g)) =
      (h.x * d.g)⁻¹ * (c⁻¹ * h.a * c) * (h.x * d.g) by group, hc, hzb]
  ·
    exact not_conj_mul_sigma hv I F hazDP hazZ c (hc.trans (mul_assoc _ _ _))
  ·
    exact not_conj_mul_sigma hv I F hzDP hzZ c (hc.trans (mul_assoc _ _ _))

end Fusion

section Normal

variable {v : H} (hv : d.IsV v) (I : In81) (F : d.Facts) (hJo : CFSec8JOrder) (hL0 : CF81L0)
  (hCls : CF81E6Cls) (hOut : CF81E6Out)
include hv I F hJo hL0 hCls hOut

theorem conj_a_mem_M3 (T : Sylow 2 H) (hTW : (T : Subgroup H) ≤ h.W) (hBT : h.B ≤ T)
    (haT : h.a ∈ (T : Subgroup H)) (R : Sylow 2 ↥h.M3)
    (hR : (R : Subgroup ↥h.M3) = (T : Subgroup H).subgroupOf h.M3) {t : H} (ht : t ∈ T) :
    t * h.a * t⁻¹ ∈ h.M3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, p, f, hp, hp2, hf, hK, hJ⟩ := Hyp52.Sec8Case.exists_params h.toHyp52 H₁.kloc.case8
  have hNn := (hOut _ p f hp hp2 hf hK H₁.kloc.rhoA
    (H₁.kloc.rhoA_admQ I.cf1 I.cf2 hJo hp hp2 hf hJ)).1
  have htaT : t * h.a * t⁻¹ ∈ (T : Subgroup H) := mul_mem (mul_mem ht haT) (inv_mem ht)
  have hψ : H₁.psiW ⟨t * h.a * t⁻¹, hTW htaT⟩ ∈
      Cat8.innA (h.K ⧸ pPrimeCore 2 h.K) H₁.kloc.rhoA := by
    have h1 : (⟨t * h.a * t⁻¹, hTW htaT⟩ : ↥h.W) = ⟨t, hTW ht⟩ *
        ⟨h.a, h.toHyp52.M3_le_normalizer h.toHyp52.a_mem_M3⟩ * ⟨t, hTW ht⟩⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv]
    exact hNn.conj_mem _ (psiW_mem_innA h.toHyp52.a_mem_M3) _
  obtain ⟨r, hr, hrb⟩ := exists_mem_T_M3 T hTW hBT R hR htaT hψ
  obtain ⟨-, hrM⟩ := mem_inf.mp hr
  rcases mem_zpowers_two d.b_ord (d.B_eq ▸ hrb) with h1 | h1
  · rw [← inv_mul_eq_one.mp h1]
    exact hrM
  · exfalso
    have hy : t * h.a * t⁻¹ = r * d.b := by rw [← h1, mul_inv_cancel_left]
    have ha2 : h.a * h.a = 1 := Six.a_mul_a_self h.toHyp52
    have hbc : t * h.a * t⁻¹ * d.b = d.b * (t * h.a * t⁻¹) := d.comm_b_of_mem_W (hTW htaT)
    have hr_eq : r = t * h.a * t⁻¹ * d.b := by rw [hy, mul_assoc, d.b_mul_self, mul_one]
    have hr2 : r * r = 1 := by
      rw [hr_eq]
      calc t * h.a * t⁻¹ * d.b * (t * h.a * t⁻¹ * d.b) =
          t * h.a * t⁻¹ * (d.b * (t * h.a * t⁻¹)) * d.b := by group
        _ = t * h.a * t⁻¹ * (t * h.a * t⁻¹ * d.b) * d.b := by rw [hbc]
        _ = t * (h.a * h.a) * t⁻¹ * (d.b * d.b) := by group
        _ = 1 := by rw [ha2, d.b_mul_self]; group
    have hr1 : r ≠ 1 := by
      intro hr1
      apply not_conj_a_b hv I F t⁻¹
      rw [inv_inv, hy, hr1, one_mul]
    obtain ⟨m, hmM, hm⟩ := d.e6_inv_cases I.cf1 I.cf2 hJo hL0 hCls F hrM hr2 hr1
    have hmb : m⁻¹ * d.b * m = d.b := by
      rw [mul_assoc, ← d.comm_b_of_mem_M3 hmM, inv_mul_cancel_left]
    apply d.e6_not_conj_mul_b hv I F hm (m⁻¹ * t)⁻¹
    calc (m⁻¹ * t)⁻¹⁻¹ * h.a * (m⁻¹ * t)⁻¹ = m⁻¹ * (t * h.a * t⁻¹) * m := by group
      _ = m⁻¹ * (r * d.b) * m := by rw [hy]
      _ = m⁻¹ * r * m * (m⁻¹ * d.b * m) := by group
      _ = m⁻¹ * r * m * d.b := by rw [hmb]

theorem Q0_normal (T : Sylow 2 H) (hTW : (T : Subgroup H) ≤ h.W) (hBT : h.B ≤ T)
    (haT : h.a ∈ (T : Subgroup H)) (R : Sylow 2 ↥h.M3)
    (hR : (R : Subgroup ↥h.M3) = (T : Subgroup H).subgroupOf h.M3) {t : H} (ht : t ∈ T) {q : H}
    (hq : q ∈ (T : Subgroup H) ⊓ h.M3) : t * q * t⁻¹ ∈ (T : Subgroup H) ⊓ h.M3 := by
  obtain ⟨hqT, hqM⟩ := mem_inf.mp hq
  refine mem_inf.mpr ⟨mul_mem (mul_mem ht hqT) (inv_mem ht), ?_⟩
  have htK : t ∈ normalizer (h.K : Set H) := H₁.kloc.normalizer_le_normalizer_K (hTW ht)
  have hta := conj_a_mem_M3 hv I F hJo hL0 hCls hOut T hTW hBT haT R hR ht
  obtain ⟨k, hk, hqk⟩ := Eight.mem_sup_zpowers_cases H₁.kloc.a_mem_normalizer_K
    (Six.a_mul_a_self h.toHyp52) hqM
  have htk : t * k * t⁻¹ ∈ h.M3 := mem_sup_left ((mem_normalizer_iff.mp htK k).mp hk)
  rcases hqk with rfl | rfl
  · exact htk
  · rw [show t * (k * h.a) * t⁻¹ = (t * k * t⁻¹) * (t * h.a * t⁻¹) by group]
    exact mul_mem htk hta

end Normal

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
