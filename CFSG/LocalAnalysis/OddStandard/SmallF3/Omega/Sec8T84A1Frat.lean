module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A1Syl
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SNFr

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B K : Subgroup G}

theorem sec8t84a1_dec (h8A : Asc82Lemma8A) (h8B : Asc82Lemma8B) (h6 : Asc82Tab6M)
    (hK : Sec8T84A1Pre G t L S z g B K) :
    ∀ n ∈ Nsub8 t B, ∃ k ∈ K, ∃ h ∈ Hsub8 t B K, ∃ o ∈ oddCoreIn (Nsub8 t B),
      n = k * h * o := by
  intro n hn
  have hCN := sec8t84a1_C_normal h8B hK.ctx
  have hm : ∀ x : G, x ∈ Nsub8 t B ⊓ centralizer (B : Set G) ↔
      n * x * n⁻¹ ∈ Nsub8 t B ⊓ centralizer (B : Set G) := by
    intro x
    constructor
    · intro hx
      exact hCN n hn x hx
    · intro hx
      have h := hCN n⁻¹ ((Nsub8 t B).inv_mem hn) (n * x * n⁻¹) hx
      simp only [inv_inv] at h
      have h' : n⁻¹ * (n * x * n⁻¹) * n = x := by group
      rw [h'] at h
      exact h
  obtain ⟨c, hcC, hc⟩ := sec9n_frattini
    (K := Nsub8 t B ⊓ centralizer (B : Set G)) (A := K) hK.syl hm
  have hcN : c ∈ Nsub8 t B := hcC.1
  have hmN : c * n ∈ Nsub8 t B := (Nsub8 t B).mul_mem hcN hn
  have hKO : K ≤ normalizer (oddCoreIn (Nsub8 t B) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro o
    constructor
    · intro ho
      exact sec8t84a1_O_norm k (hK.le_C hk).1 o ho
    · intro ho
      have h := sec8t84a1_O_norm k⁻¹ ((Nsub8 t B).inv_mem (hK.le_C hk).1) (k * o * k⁻¹) ho
      have h' : k⁻¹ * (k * o * k⁻¹) * k⁻¹⁻¹ = o := by group
      rwa [h'] at h
  have hc_inv_sup : c⁻¹ ∈ K ⊔ oddCoreIn (Nsub8 t B) := by
    rw [sec8t84a1_pre_sup h8A h8B h6 hK]
    exact (Nsub8 t B ⊓ centralizer (B : Set G)).inv_mem hcC
  have hmem : c⁻¹ ∈ (K : Set G) * (oddCoreIn (Nsub8 t B) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right K (oddCoreIn (Nsub8 t B)) hKO]
    exact hc_inv_sup
  rw [Set.mem_mul] at hmem
  obtain ⟨k₁, hk₁, o₁, ho₁, hc_inv_eq⟩ := hmem
  set b : G := (c * n) * t * (c * n)⁻¹ * t⁻¹ with hbdef
  have hb : b ∈ B := by
    rw [hbdef]
    exact sec8t84a1_comm_mem h8B hK.ctx hmN
  obtain ⟨k₂, hk₂, hk₂_eq⟩ := hK.tau b⁻¹ (B.inv_mem hb)
  have hk₂_comm : k₂ * b = b * k₂ :=
    (Subgroup.mem_centralizer_iff.mp (hK.le_C hk₂).2 b hb).symm
  have hmt : (c * n) * t * (c * n)⁻¹ = b * t := by
    rw [hbdef]; group
  have hkt : k₂ * t * k₂⁻¹ = b⁻¹ * t := by
    rw [← hk₂_eq]; group
  have hconj : (k₂ * (c * n)) * t * (k₂ * (c * n))⁻¹ = t := by
    calc (k₂ * (c * n)) * t * (k₂ * (c * n))⁻¹
        = k₂ * ((c * n) * t * (c * n)⁻¹) * k₂⁻¹ := by group
      _ = k₂ * (b * t) * k₂⁻¹ := by rw [hmt]
      _ = b * (k₂ * t * k₂⁻¹) := by
            calc k₂ * (b * t) * k₂⁻¹ = (k₂ * b) * t * k₂⁻¹ := by group
              _ = (b * k₂) * t * k₂⁻¹ := by rw [hk₂_comm]
              _ = b * (k₂ * t * k₂⁻¹) := by group
      _ = b * (b⁻¹ * t) := by rw [hkt]
      _ = t := by group
  have hht : (k₂ * (c * n)) * t = t * (k₂ * (c * n)) := by
    calc (k₂ * (c * n)) * t
        = ((k₂ * (c * n)) * t * (k₂ * (c * n))⁻¹) * (k₂ * (c * n)) := by group
      _ = t * (k₂ * (c * n)) := by rw [hconj]
  have hhN : k₂ * (c * n) ∈ Nsub8 t B := (Nsub8 t B).mul_mem (hK.le_C hk₂).1 hmN
  have hh_norm : ∀ x : G, x ∈ K ↔ (k₂ * (c * n)) * x * (k₂ * (c * n))⁻¹ ∈ K := by
    intro x
    constructor
    · intro hx
      have heq : (k₂ * (c * n)) * x * (k₂ * (c * n))⁻¹ =
          k₂ * ((c * n) * x * (c * n)⁻¹) * k₂⁻¹ := by group
      rw [heq]
      exact K.mul_mem (K.mul_mem hk₂ ((hc x).1 hx)) (K.inv_mem hk₂)
    · intro hx
      have heq : (c * n) * x * (c * n)⁻¹ =
          k₂⁻¹ * ((k₂ * (c * n)) * x * (k₂ * (c * n))⁻¹) * k₂ := by group
      have hmemK : (c * n) * x * (c * n)⁻¹ ∈ K := by
        rw [heq]
        exact K.mul_mem (K.mul_mem (K.inv_mem hk₂) hx) hk₂
      exact (hc x).2 hmemK
  have hhH : k₂ * (c * n) ∈ Hsub8 t B K :=
    (sec8t84a1_mem_H (h := k₂ * (c * n))).mpr ⟨hhN, hh_norm, hht⟩
  have ho₂ : (c * n)⁻¹ * o₁ * (c * n) ∈ oddCoreIn (Nsub8 t B) := by
    have h := sec8t84a1_O_norm (c * n)⁻¹ ((Nsub8 t B).inv_mem hmN) o₁ ho₁
    simp only [inv_inv] at h
    exact h
  refine ⟨k₁ * k₂⁻¹, K.mul_mem hk₁ (K.inv_mem hk₂), k₂ * (c * n), hhH,
    (c * n)⁻¹ * o₁ * (c * n), ho₂, ?_⟩
  calc n = c⁻¹ * (c * n) := by group
    _ = (k₁ * o₁) * (c * n) := by rw [← hc_inv_eq]
    _ = (k₁ * k₂⁻¹) * (k₂ * (c * n)) * ((c * n)⁻¹ * o₁ * (c * n)) := by group

theorem sec8t84a1_H_trans (h8A : Asc82Lemma8A) (h8B : Asc82Lemma8B) (h6 : Asc82Tab6M)
    (hK : Sec8T84A1Pre G t L S z g B K) :
    ∀ b ∈ B, b ≠ 1 → ∀ b' ∈ B, b' ≠ 1 → ∃ h ∈ Hsub8 t B K, h * b * h⁻¹ = b' := by
  intro b hb hb1 b' hb' hb1'
  obtain ⟨n, hn, hnb⟩ := (sec8t84a1_autL h6 hK.ctx).2 b hb hb1 b' hb' hb1'
  have hnN : n ∈ Nsub8 t B := (sec8t84a1_L_norm_le hK.ctx hn).1
  obtain ⟨k, hkK, h, hhH, o, hoO, hn_eq⟩ := sec8t84a1_dec h8A h8B h6 hK n hnN
  have hbB : h * b * h⁻¹ ∈ B := by
    have hNnorm : Nsub8 t B ≤ normalizer (B : Set G) := sec8t84a1_N_le_normalizer h8B hK.ctx
    have hhN : h ∈ Nsub8 t B := (sec8t84a1_mem_H.mp hhH).1
    exact (Subgroup.mem_normalizer_iff.mp (hNnorm hhN) b).mp hb
  have hk_comm : k * (h * b * h⁻¹) = (h * b * h⁻¹) * k :=
    (Subgroup.mem_centralizer_iff.mp (hK.le_C hkK).2 (h * b * h⁻¹) hbB).symm
  have ho_comm : o * b = b * o :=
    (Subgroup.mem_centralizer_iff.mp ((sec8t84a1_O_le_C h8A hK.ctx) hoO).2 b hb).symm
  have hmain : n * b * n⁻¹ = h * b * h⁻¹ := by
    have hob : o * b * o⁻¹ = b := by rw [ho_comm]; group
    have key : (k * h * o) * b * (k * h * o)⁻¹ = k * (h * b * h⁻¹) * k⁻¹ := by
      rw [show (k * h * o) * b * (k * h * o)⁻¹ =
        k * (h * (o * b * o⁻¹) * h⁻¹) * k⁻¹ by group, hob]
    calc n * b * n⁻¹ = (k * h * o) * b * (k * h * o)⁻¹ := by rw [hn_eq]
      _ = k * (h * b * h⁻¹) * k⁻¹ := key
      _ = h * b * h⁻¹ := by rw [hk_comm]; group
  refine ⟨h, hhH, ?_⟩
  rw [← hmain]
  exact hnb

end CFSG.OddStandard.SmallF3.Omega
