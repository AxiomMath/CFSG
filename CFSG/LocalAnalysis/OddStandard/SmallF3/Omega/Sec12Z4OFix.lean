module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12EDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123aVec
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z4OFin
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z4ORho

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def Z4OFix (Y : Subgroup G) (φ : (Fin 5 → ZMod 2) → G) (c : Fin 5) (v : G) : Prop :=
  ∀ y ∈ Y, ∀ σ : Equiv.Perm (Fin 5), SecActs φ y σ → σ c = c → σ * σ = 1 →
    Equiv.Perm.sign σ = 1 → y * v * y⁻¹ = v

theorem z4o_secActs_one (φ : (Fin 5 → ZMod 2) → G) : SecActs φ 1 1 := by
  intro v _
  rw [permVec_one]
  group

theorem z4o_act_eq [Finite G] {t : G} {L S V : Subgroup G} (F : Sec12Frame t L S)
    (hBV : secB S L ≤ V) (hVc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) {φ : (Fin 5 → ZMod 2) → G}
    (hφ : SecNatCoord φ (secB S L)) {y y' : G} (hy : y ∈ L) (hy' : y' ∈ L)
    {σ : Equiv.Perm (Fin 5)} (h1 : SecActs φ y σ) (h2 : SecActs φ y' σ) {v : G}
    (hv : v ∈ V) : y * v * y⁻¹ = y' * v * y'⁻¹ := by
  have h3 := (z4o_secActs_inv h2).mul h1
  rw [show σ⁻¹ * σ = 1 from inv_mul_cancel σ] at h3
  have hc : y'⁻¹ * y ∈ centralizer (secB S L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨u, hu, rfl⟩ := hφ.onto b hb
    have h4 := h3 u hu
    rw [permVec_one] at h4
    calc φ u * (y'⁻¹ * y) = (y'⁻¹ * y * φ u * (y'⁻¹ * y)⁻¹) * (y'⁻¹ * y) := by rw [h4]
      _ = y'⁻¹ * y * φ u := by group
  have hB : y'⁻¹ * y ∈ secB S L := by
    have h5 : y'⁻¹ * y ∈ centralizer (secB S L : Set G) ⊓ L :=
      Subgroup.mem_inf.mpr ⟨hc, L.mul_mem (L.inv_mem hy') hy⟩
    rwa [F.bdata.2.2.1] at h5
  have h6 : (y'⁻¹ * y) * v * (y'⁻¹ * y)⁻¹ = v := by
    rw [hVc _ (hBV hB) v hv]
    group
  calc y * v * y⁻¹ = y' * ((y'⁻¹ * y) * v * (y'⁻¹ * y)⁻¹) * y'⁻¹ := by group
    _ = y' * v * y'⁻¹ := by rw [h6]

theorem z4o_fix_conj {Y : Subgroup G} {φ : (Fin 5 → ZMod 2) → G} {c : Fin 5} {v g : G}
    (hgY : ∀ y ∈ Y, g⁻¹ * y * g ∈ Y) {τ : Equiv.Perm (Fin 5)} (hgτ : SecActs φ g τ)
    (hτc : τ c = c) (hv : Z4OFix Y φ c v) : Z4OFix Y φ c (g * v * g⁻¹) := by
  intro y hy σ hσ h1 h2 h3
  have hact : SecActs φ (g⁻¹ * y * g) (τ⁻¹ * σ * τ) := ((z4o_secActs_inv hgτ).mul hσ).mul hgτ
  have hτc' : τ⁻¹ c = c := by rw [Equiv.Perm.inv_eq_iff_eq]; exact hτc.symm
  have e1 : (τ⁻¹ * σ * τ) c = c := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hτc, h1, hτc']
  have e2 : (τ⁻¹ * σ * τ) * (τ⁻¹ * σ * τ) = 1 := by
    calc (τ⁻¹ * σ * τ) * (τ⁻¹ * σ * τ) = τ⁻¹ * (σ * σ) * τ := by group
      _ = 1 := by rw [h2]; group
  have e3 : Equiv.Perm.sign (τ⁻¹ * σ * τ) = 1 := by
    rw [map_mul, map_mul, map_inv, h3, mul_one, inv_mul_cancel]
  have hfix := hv _ (hgY y hy) _ hact e1 e2 e3
  calc y * (g * v * g⁻¹) * y⁻¹ = g * ((g⁻¹ * y * g) * v * (g⁻¹ * y * g)⁻¹) * g⁻¹ := by group
    _ = g * v * g⁻¹ := by rw [hfix]

theorem z4o_fix_of_gen [Finite G] {t : G} {L S V : Subgroup G} (F : Sec12Frame t L S)
    (hBV : secB S L ≤ V) (hVc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) {φ : (Fin 5 → ZMod 2) → G}
    (hφ : SecNatCoord φ (secB S L)) {c : Fin 5} {q1 q2 v : G} (hq1 : q1 ∈ L) (hq2 : q2 ∈ L)
    (h1 : SecActs φ q1 (z4oS1 c)) (h2 : SecActs φ q2 (z4oS2 c)) (hv : v ∈ V)
    (hv1 : q1 * v * q1⁻¹ = v) (hv2 : q2 * v * q2⁻¹ = v) :
    Z4OFix (secM t S L ⊓ L) φ c v := by
  intro y hy σ hσ hc hσ2 hs
  rcases z4o_klein_cases c hc hσ2 hs with rfl | rfl | rfl | rfl
  · rw [z4o_act_eq F hBV hVc hφ hy.2 (one_mem L) hσ (z4o_secActs_one φ) hv]
    group
  · rw [z4o_act_eq F hBV hVc hφ hy.2 hq1 hσ h1 hv, hv1]
  · rw [z4o_act_eq F hBV hVc hφ hy.2 hq2 hσ h2 hv, hv2]
  · rw [z4o_act_eq F hBV hVc hφ hy.2 (mul_mem hq1 hq2) hσ (h1.mul h2) hv]
    calc q1 * q2 * v * (q1 * q2)⁻¹ = q1 * (q2 * v * q2⁻¹) * q1⁻¹ := by group
      _ = v := by rw [hv2, hv1]

end CFSG.OddStandard.SmallF3.Omega
