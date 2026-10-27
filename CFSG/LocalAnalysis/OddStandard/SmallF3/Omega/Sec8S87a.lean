module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Early
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L68b

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem mem_zpowers_two {t x : G} (ht2 : t * t = 1) (hx : x ∈ zpowers t) :
    x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : t ^ (2 : ℕ) = 1 := by simpa [pow_two] using ht2
  have hmod : t ^ k = t ^ (k % (2 : ℤ)) := zpow_eq_zpow_emod' k h2
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left; rw [hmod, hk]; simp
  · right; rw [hmod, hk]; simp

private theorem mem_normalizer_centralizer {H : Subgroup G} {s : G}
    (hs : s ∈ normalizer (H : Set G)) : s ∈ normalizer (centralizer (H : Set G)) := by
  rw [Subgroup.mem_normalizer_iff] at hs ⊢
  intro c
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc x hx
    have hx' : s⁻¹ * x * s ∈ H := (hs (s⁻¹ * x * s)).mpr (by
      rw [show s * (s⁻¹ * x * s) * s⁻¹ = x by group]; exact hx)
    calc x * (s * c * s⁻¹) = s * ((s⁻¹ * x * s) * c) * s⁻¹ := by group
      _ = s * (c * (s⁻¹ * x * s)) * s⁻¹ := by rw [hc (s⁻¹ * x * s) hx']
      _ = (s * c * s⁻¹) * x := by group
  · intro hc x hx
    have hx' : s * x * s⁻¹ ∈ H := (hs x).mp hx
    have h := hc (s * x * s⁻¹) hx'
    calc x * c = s⁻¹ * ((s * x * s⁻¹) * (s * c * s⁻¹)) * s := by group
      _ = s⁻¹ * ((s * c * s⁻¹) * (s * x * s⁻¹)) * s := by rw [h]
      _ = c * x := by group

private theorem sec8s_conj_comm {t z s g : G} {S : Subgroup G}
    (hSt : S ≤ centralizer ({t} : Set G)) (hcentral : ∀ s ∈ S, s * z = z * s)
    (htz : g⁻¹ * t * g = t * z) (hs : s ∈ S) :
    (g * s * g⁻¹) * t = t * (g * s * g⁻¹) := by
  have hst : s * t = t * s := Subgroup.mem_centralizer_singleton_iff.mp (hSt hs)
  have hsz : s * z = z * s := hcentral s hs
  have ht' : g * (t * z) * g⁻¹ = t := by rw [← htz]; group
  calc (g * s * g⁻¹) * t
      = (g * s * g⁻¹) * (g * (t * z) * g⁻¹) := by rw [ht']
    _ = g * (s * (t * z)) * g⁻¹ := by group
    _ = g * ((s * t) * z) * g⁻¹ := by group
    _ = g * ((t * s) * z) * g⁻¹ := by rw [hst]
    _ = g * (t * (s * z)) * g⁻¹ := by group
    _ = g * (t * (z * s)) * g⁻¹ := by rw [hsz]
    _ = g * ((t * z) * s) * g⁻¹ := by group
    _ = (g * (t * z) * g⁻¹) * (g * s * g⁻¹) := by group
    _ = t * (g * s * g⁻¹) := by rw [ht']

theorem sec8s_sylow_t [Finite G] (h68 : Asc82Lemma68) (h85 : Asc82Lemma85) (hB : Asc82Sec8B)
    {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G} (hctx : Sec8Ctx G t L S z g B) :
    IsSylow2Of (zpowers t) (centralizer (L : Set G)) := by
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hzB : z ∈ B := (hB G t L S z g B hctx.toSec8Base).1
  have hz2 : orderOf z = 2 := hctx.pocket.1
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hne : g⁻¹ * t * g ≠ t := by
    intro h
    have htz : t * z = t := by rw [← hctx.tz, h]
    exact hz1 (mul_left_cancel (a := t) (by rw [htz, mul_one]))
  have hmem : g⁻¹ * t * g ∈ cosetSet t B := by
    rw [hctx.tz]
    exact ⟨z, hzB, rfl⟩
  have h85c : S ⊓ L = S ⊓ CFSG.conjugate L g := h85 G t L S z g B hctx
  have hBg : B ≤ CFSG.conjugate L g := fun x hx => by
    have hx' : x ∈ S ⊓ L := ⟨(hctx.B_le hx).2, (hctx.B_le hx).1⟩
    rw [h85c] at hx'
    exact hx'.2
  exact (h68 G t L hS hctx.omega6m B hctx.B_e16 (fun x hx => (hctx.B_le hx).1)
    g hne hmem hBg).1

theorem sec8s_sylow_normalizer [Finite G] (h36 : Asc82Lemma36) (h68 : Asc82Lemma68)
    (h85 : Asc82Lemma85) (h86 : Asc82Lemma86) (hB : Asc82Sec8B) {t : G} {L S : Subgroup G}
    {z g : G} {B : Subgroup G} (hctx : Sec8Ctx G t L S z g B) :
    IsSylow2Of S (normalizer (L : Set G)) := by
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hnorm := conjugate_eq_self_of_lemma36 h36 hS
  have hSN : S ≤ normalizer (L : Set G) := by
    intro s hsS
    have hconj : CFSG.conjugate L s = L := hnorm s (hctx.sylow.1 hsS)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact (show x ∈ L ↔ x ∈ CFSG.conjugate L s from by rw [hconj]).trans
      (mem_conjugate_iff' (H := L) (g := s) (x := x))
  have ht2 : t * t = 1 := by rw [← pow_two, ← hS.involution, pow_orderOf_eq_one]
  have htS : t ∈ S := by
    have ht : t ∈ S ⊓ centralizer (L : Set G) := by
      rw [h86 G t L S z g B hctx]
      exact Subgroup.mem_zpowers t
    exact ht.1
  have htC : t ∈ centralizer (L : Set G) := sec68_t_mem_centralizer hS
  obtain ⟨S', hS'syl, hSS'⟩ :=
    sec68_exists_sylow_ge (H := normalizer (L : Set G)) hctx.sylow.2.1 hSN
  have hT₀2 : IsPGroup 2 ↥(S' ⊓ centralizer (L : Set G)) := hS'syl.2.1.to_le inf_le_left
  have hztle : zpowers t ≤ S' ⊓ centralizer (L : Set G) := by
    rw [zpowers_le]
    exact ⟨hSS' htS, htC⟩
  have hT := sec8s_sylow_t h68 h85 hB hctx
  have hT₀eq : S' ⊓ centralizer (L : Set G) = zpowers t :=
    hT.eq_of_le inf_le_right hT₀2 hztle
  have hS'C : S' ≤ centralizer ({t} : Set G) := by
    intro s hsS'
    have hsN : s ∈ normalizer (L : Set G) := hS'syl.1 hsS'
    have hsNC : s ∈ normalizer (centralizer (L : Set G)) := mem_normalizer_centralizer hsN
    have hstC : s * t * s⁻¹ ∈ centralizer (L : Set G) :=
      (Subgroup.mem_normalizer_iff.mp hsNC t).mp htC
    have hstS' : s * t * s⁻¹ ∈ S' := S'.mul_mem (S'.mul_mem hsS' (hSS' htS)) (S'.inv_mem hsS')
    have hstT : s * t * s⁻¹ ∈ S' ⊓ centralizer (L : Set G) := ⟨hstS', hstC⟩
    have hstz : s * t * s⁻¹ ∈ zpowers t := by rwa [hT₀eq] at hstT
    have ht1 : t ≠ 1 := by
      intro ht1
      have hinv : orderOf t = 2 := hS.involution
      rw [ht1, orderOf_one] at hinv
      exact absurd hinv (by norm_num)
    rcases mem_zpowers_two ht2 hstz with h1 | h1
    · exfalso
      have h3 := congrArg (fun y => s⁻¹ * y * s) h1
      rw [show s⁻¹ * (s * t * s⁻¹) * s = t by group,
        show s⁻¹ * (1 : G) * s = 1 by group] at h3
      exact ht1 h3
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc s * t = (s * t * s⁻¹) * s := by group
        _ = t * s := by rw [h1]
  have hS'eq : S' = S := hctx.sylow.eq_of_le hS'C hS'syl.2.1 hSS'
  rw [hS'eq] at hS'syl
  exact hS'syl

theorem sec8s_mem_normalizer_conj [Finite G] (h36 : Asc82Lemma36) {t : G} {L S : Subgroup G}
    {z g : G} {B : Subgroup G} (hctx : Sec8Ctx G t L S z g B) {s : G} (hs : s ∈ S) :
    s ∈ normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) := by
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hnorm := conjugate_eq_self_of_lemma36 h36 hS
  have hs'C : g * s * g⁻¹ ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (sec8s_conj_comm hctx.sylow.1 hctx.central hctx.tz hs)
  have hs'N : g * s * g⁻¹ ∈ normalizer (L : Set G) := by
    have hconj : CFSG.conjugate L (g * s * g⁻¹) = L := hnorm (g * s * g⁻¹) hs'C
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact (show x ∈ L ↔ x ∈ CFSG.conjugate L (g * s * g⁻¹) from by rw [hconj]).trans
      (mem_conjugate_iff' (H := L) (g := g * s * g⁻¹) (x := x))
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [mem_conjugate_iff' (H := L) (g := g) (x := h),
    mem_conjugate_iff' (H := L) (g := g) (x := s * h * s⁻¹)]
  have heq : g * (s * h * s⁻¹) * g⁻¹ =
      (g * s * g⁻¹) * (g * h * g⁻¹) * (g * s * g⁻¹)⁻¹ := by group
  rw [heq]
  exact Subgroup.mem_normalizer_iff.mp hs'N (g * h * g⁻¹)

end CFSG.OddStandard.SmallF3.Omega
