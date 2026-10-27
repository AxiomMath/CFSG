module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FSwap
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem conjugate_one_eq (H : Subgroup G) : CFSG.conjugate H 1 = H := by
  ext x
  rw [mem_conjugate_iff]
  simp

private theorem inf_centralizer_singleton_mul_of_mem_centralizer {H : Subgroup G} {a b : G}
    (ha : a ∈ centralizer (H : Set G)) :
    H ⊓ centralizer ({b} : Set G) = H ⊓ centralizer ({b * a} : Set G) := by
  ext x
  constructor
  · rintro ⟨hxH, hx⟩
    have hxa : x * a = a * x := Subgroup.mem_centralizer_iff.mp ha x hxH
    have hxb : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    refine ⟨hxH, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc x * (b * a) = (x * b) * a := by group
      _ = (b * x) * a := by rw [hxb]
      _ = b * (x * a) := by group
      _ = b * (a * x) := by rw [hxa]
      _ = (b * a) * x := by group
  · rintro ⟨hxH, hx⟩
    have hxa : x * a = a * x := Subgroup.mem_centralizer_iff.mp ha x hxH
    have hxba : x * (b * a) = (b * a) * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    refine ⟨hxH, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc x * b = x * (b * a) * a⁻¹ := by group
      _ = (b * a) * x * a⁻¹ := by rw [hxba]
      _ = b * (a * x) * a⁻¹ := by group
      _ = b * (x * a) * a⁻¹ := by rw [← hxa]
      _ = b * x := by group

theorem sec4_lemmaP (h36 : Asc82Lemma36) (h39 : Asc82Lemma39) (hk6 : Asc82FactK6)
    (hf6 : Asc82Fact6Class) (hD : Asc82FactD) (hABC : Asc82ClaimsABC) [Finite G] {t : G}
    {L S : Subgroup G} {z : G} (hctx : Sec4Ctx G t L S z) {s : G}
    (hs : ∃ h : G, s = h⁻¹ * t * h) (hsc : s ∈ centralizer ({t} : Set G))
    (hs6 : InducesTypeSome L s 7 1 6 1) {u : G} (huL : u ∈ L) (hu2 : orderOf u = 2)
    (hu6 : InducesTypeSome L u 7 1 6 (-1)) : ∃ h : G, t * u = h⁻¹ * t * h := by
  classical
  obtain ⟨g, rfl⟩ := hs
  have hL : IsOmega7Group L := sec4_isOmega7Group hctx.toSec4Setting
  let L₂ : Subgroup G := CFSG.conjugate L g
  let D : Subgroup G := L ⊓ L₂
  obtain ⟨-, -, -, hFx, hFy⟩ := sec4F_pair_data hD hABC hctx hsc hs6
  obtain ⟨w, hwU, hw6'⟩ := hFy.2.2.2.1
  have hw2 : InducesTypeSome L w 7 1 2 (-1) :=
    (sec4_frame_swap h39 hk6 hD hABC hctx hsc hs6 hwU).mpr hw6'
  have hsw : (g⁻¹ * t * g) * w ∈ conjClassIn L (g⁻¹ * t * g) := hFx.2.2.2.2 w hwU hw2
  obtain ⟨l, hlL, hlw⟩ := hsw
  let u₀ : G := g * w * g⁻¹
  have hu₀L : u₀ ∈ L := by
    show g * w * g⁻¹ ∈ L
    exact (mem_conjugate_iff L g w).mp (Subgroup.mem_inf.mp hwU.1).2
  have hu₀2 : orderOf u₀ = 2 := by
    show orderOf (g * w * g⁻¹) = 2
    have h := orderOf_conjugate_eq w g⁻¹
    simp only [inv_inv] at h
    exact h.trans hwU.2.1
  have hu₀6 : InducesTypeSome L u₀ 7 1 6 (-1) := by
    have h := inducesTypeSome_conjugate hw6' g⁻¹
    have hL₂inv : CFSG.conjugate L₂ g⁻¹ = L := by
      dsimp only [L₂]
      rw [sec4F_conjugate_conjugate L g g⁻¹, mul_inv_cancel, conjugate_one_eq]
    rw [hL₂inv] at h
    show InducesTypeSome L (g * w * g⁻¹) 7 1 6 (-1)
    simpa only [inv_inv] using h
  have htu₀ : ∃ h : G, t * u₀ = h⁻¹ * t * h := by
    have hx : (g⁻¹ * t * g) * w = (g * l⁻¹)⁻¹ * t * (g * l⁻¹) := by
      rw [hlw]; group
    refine ⟨(g * l⁻¹) * g⁻¹, ?_⟩
    calc t * u₀ = g * ((g⁻¹ * t * g) * w) * g⁻¹ := by
          show t * (g * w * g⁻¹) = g * ((g⁻¹ * t * g) * w) * g⁻¹
          group
      _ = g * ((g * l⁻¹)⁻¹ * t * (g * l⁻¹)) * g⁻¹ := by rw [hx]
      _ = ((g * l⁻¹) * g⁻¹)⁻¹ * t * ((g * l⁻¹) * g⁻¹) := by group
  obtain ⟨x, hx⟩ := htu₀
  obtain ⟨l', hl'L, hl'u⟩ := hf6 G L hL u₀ u hu₀L huL hu₀2 hu2 hu₀6 hu6
  have ht_comm : t * l' = l' * t :=
    (Subgroup.mem_centralizer_iff.mp (sec4_t_mem_centralizer hctx.toSec3Setting) l' hl'L).symm
  refine ⟨x * l'⁻¹, ?_⟩
  calc t * u = t * (l' * u₀ * l'⁻¹) := by rw [hl'u]
    _ = (t * l') * u₀ * l'⁻¹ := by group
    _ = (l' * t) * u₀ * l'⁻¹ := by rw [ht_comm]
    _ = l' * (t * u₀) * l'⁻¹ := by group
    _ = l' * (x⁻¹ * t * x) * l'⁻¹ := by rw [hx]
    _ = (x * l'⁻¹)⁻¹ * t * (x * l'⁻¹) := by group

theorem sec4_no_triangle (h36 : Asc82Lemma36) (h39 : Asc82Lemma39) (hk6 : Asc82FactK6)
    (hD : Asc82FactD) (hABC : Asc82ClaimsABC) [Finite G] {t : G} {L S : Subgroup G} {z : G}
    (hctx : Sec4Ctx G t L S z) {m : G} (hm : ∃ h : G, m = h⁻¹ * t * h)
    (hmt : ∃ h : G, m * t = h⁻¹ * t * h) (hmc : m ∈ centralizer ({t} : Set G))
    (hm6 : InducesTypeSome L m 7 1 6 1) : False := by
  classical
  obtain ⟨g, rfl⟩ := hm
  obtain ⟨k, hk⟩ := hmt
  let m : G := g⁻¹ * t * g
  let L₂ : Subgroup G := CFSG.conjugate L g
  let L₃ : Subgroup G := CFSG.conjugate L k
  have hL : IsOmega7Group L := sec4_isOmega7Group hctx.toSec4Setting
  have hL₂ : IsOmega7Group L₂ := sec4_isOmega7Group (hctx.conjugate g).toSec4Setting
  have htC : t ∈ centralizer (L : Set G) := sec4_t_mem_centralizer hctx.toSec3Setting
  have hmC : m ∈ centralizer (L₂ : Set G) :=
    sec4_t_mem_centralizer (hctx.conjugate g).toSec3Setting
  have hmc' : m ∈ centralizer ({t} : Set G) := hmc
  have hm6' : InducesTypeSome L m 7 1 6 1 := hm6
  have hmct : m * t = t * m := Subgroup.mem_centralizer_singleton_iff.mp hmc'
  have hk'm : m * t = k⁻¹ * t * k := hk
  obtain ⟨P12T, P12C1, P12C2, P12Fx, P12Fy⟩ := sec4F_pair_data hD hABC hctx hmc' hm6'
  have ht_self : t ∈ centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hkc : k⁻¹ * t * k ∈ centralizer ({t} : Set G) := by
    rw [← hk'm]
    exact mul_mem hmc' ht_self
  have hk6ty : InducesTypeSome L (k⁻¹ * t * k) 7 1 6 1 := by
    rw [← hk'm]
    exact (sec4F_type_mul_cent_iff hL htC (Or.inr (Or.inr rfl))).mpr hm6'
  obtain ⟨P13T, P13C1, P13C2, P13Fx, P13Fy⟩ := sec4F_pair_data hD hABC hctx hkc hk6ty
  let g' : G := g⁻¹ * k
  have hge : g'⁻¹ * m * g' = m * t := by
    have h1 : g'⁻¹ * m * g' = k⁻¹ * t * k := by
      dsimp only [g', m]; group
    rw [h1, ← hk'm]
  have hconjL₂ : CFSG.conjugate L₂ g' = L₃ := by
    dsimp only [L₂, L₃, g']
    rw [sec4F_conjugate_conjugate L g (g⁻¹ * k), show g * (g⁻¹ * k) = k by group]
  have hm_self : m ∈ centralizer ({m} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have ht_in_cent_m : t ∈ centralizer ({m} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hmct.symm
  have hgc23 : g'⁻¹ * m * g' ∈ centralizer ({m} : Set G) := by
    rw [hge]
    exact mul_mem hm_self ht_in_cent_m
  have hg623 : InducesTypeSome L₂ (g'⁻¹ * m * g') 7 1 6 1 := by
    rw [hge, hmct]
    exact (sec4F_type_mul_cent_iff hL₂ hmC (Or.inr (Or.inr rfl))).mpr P12T
  obtain ⟨P23T, P23C1, P23C2, P23Fx, P23Fy⟩ :=
    sec4F_pair_data hD hABC (hctx.conjugate g) hgc23 hg623
  have hE1c := inf_centralizer_singleton_mul_of_mem_centralizer (H := L) (a := t) (b := m) htC
  have hE1ge : L ⊓ L₃ ≤ L ⊓ centralizer ({m} : Set G) := by
    have h := sec4FC_inf_conjugate_le_left htC k
    rw [← hk'm, ← hE1c] at h
    exact h
  have hE1le : L ⊓ centralizer ({m} : Set G) ≤ (L ⊓ L₃) ⊔ Sec4FOdd L := by
    have h := P13C1
    rw [← hk'm, ← hE1c] at h
    exact h
  have hE2b0 :=
    inf_centralizer_singleton_mul_of_mem_centralizer (H := L₂) (a := m) (b := t) hmC
  have hE2b : L₂ ⊓ centralizer ({m * t} : Set G) = L₂ ⊓ centralizer ({t} : Set G) := by
    rw [← hmct] at hE2b0
    exact hE2b0.symm
  have hE2ge : L₂ ⊓ L₃ ≤ L₂ ⊓ centralizer ({t} : Set G) := by
    have h := sec4FC_inf_conjugate_le_left hmC g'
    rw [hge, hconjL₂, hE2b] at h
    exact h
  have hE2le : L₂ ⊓ centralizer ({t} : Set G) ≤ (L₂ ⊓ L₃) ⊔ Sec4FOdd L₂ := by
    have h := P23C1
    rw [hge, hconjL₂, hE2b] at h
    exact h
  have hU13 : ∀ v, Asc82SetU (L ⊓ L₂) v → Asc82SetU (L ⊓ L₃) v := fun v hv =>
    (Asc82SetU.congr_oddCent (sec4FC_inf_conjugate_le_left htC g) hE1ge P12C1 hE1le
      (sec4FC_oddCent_odd hL inf_le_left)).mp hv
  have hU23 : ∀ v, Asc82SetU (L ⊓ L₂) v → Asc82SetU (L₂ ⊓ L₃) v := fun v hv =>
    (Asc82SetU.congr_oddCent (sec4FC_inf_conjugate_le_right htC g) hE2ge P12C2 hE2le
      (sec4FC_oddCent_odd hL₂ inf_le_left)).mp hv
  obtain ⟨v, hvU, hv2⟩ := P12Fx.2.2.1
  have h6L₂ : InducesTypeSome L₂ v 7 1 6 (-1) :=
    (sec4_frame_swap h39 hk6 hD hABC hctx hmc' hm6' hvU).mp hv2
  have hvL₃ : Asc82SetU (L ⊓ CFSG.conjugate L k) v := hU13 v hvU
  have h6L₃ : InducesTypeSome L₃ v 7 1 6 (-1) :=
    (sec4_frame_swap h39 hk6 hD hABC hctx hkc hk6ty hvL₃).mp hv2
  have h2L₂ : InducesTypeSome L₂ v 7 1 2 (-1) := by
    have hvL₂L₃ : Asc82SetU (L₂ ⊓ L₃) v := hU23 v hvU
    have hvL₂g' : Asc82SetU (CFSG.conjugate L g ⊓
        CFSG.conjugate (CFSG.conjugate L g) g') v := by
      rw [hconjL₂]
      exact hvL₂L₃
    have S23 := sec4_frame_swap h39 hk6 hD hABC (hctx.conjugate g) hgc23 hg623 hvL₂g'
    rw [hconjL₂] at S23
    exact S23.mpr h6L₃
  exact (by decide : (2 : ℕ) ≠ 6)
    (sec4F_type_excl hL₂ (Or.inl rfl) (Or.inr (Or.inr rfl)) h2L₂ h6L₂).1

end CFSG.OddStandard.SmallF3.Omega
