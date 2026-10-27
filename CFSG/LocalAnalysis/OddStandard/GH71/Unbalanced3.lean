module

public import CFSG.LocalAnalysis.OddStandard.GH71.Frame
public import CFSG.LocalAnalysis.OddStandard.Solomon75GH71Pairing

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.OddStandard.Solomon75

variable {G : Type} [Group G] [Finite G] {z : G} {S U : Subgroup G} {u : G}

namespace Ctx71

theorem exists_sylow_bar (h : Ctx71 G z S U u) :
    ∃ Q : Sylow 2 (HBar (Cen z)), (Q : Subgroup (HBar (Cen z))) = barIn (Cen z) S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := h.ctx.sylow
  refine ⟨P.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(Cen z))), ?_⟩
  rw [Sylow.coe_mapSurjective]
  unfold barIn
  congr 1
  rw [← hP]
  exact (Subgroup.comap_map_eq_self_of_injective (Cen z).subtype_injective _).symm

theorem conj_u (h : Ctx71 G z S U u) {s : G} (hs : s ∈ S) :
    s * u * s⁻¹ = u ∨ s * u * s⁻¹ = u * z := by
  have hmem : s * u * s⁻¹ ∈ U := (mem_normalizer_iff.mp (h.U_norm hs) u).mp h.u_mem
  rcases h.mem_U hmem with h1 | h1 | h1 | h1
  · exfalso; apply h.u_ne_one
    have : u = s⁻¹ * (s * u * s⁻¹) * s := by group
    rw [this, h1]; group
  · exfalso; apply h.u_ne_z
    have hsz : s * z = z * s := mem_centralizer_singleton_iff.mp (h.S_le hs)
    have : u = s⁻¹ * (s * u * s⁻¹) * s := by group
    rw [this, h1]
    calc s⁻¹ * z * s = s⁻¹ * (z * s) := by group
      _ = s⁻¹ * (s * z) := by rw [hsz]
      _ = z := by group
  · exact Or.inl h1
  · exact Or.inr h1

theorem not_S_le_cen_u (h : Ctx71 G z S U u) : ¬ S ≤ centralizer ({u} : Set G) := by
  intro hS
  obtain ⟨Q, hQ⟩ := h.exists_sylow_bar
  refine h.not_mem_center h.u_mem h.u_ne_one h.u_ne_z ?_
  refine mem_center_of_mem_center_sylow (n := 11) (by norm_num) h.cover Q ?_ ?_
  · intro s hs
    rw [hQ] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_singleton_iff.mp (hS (Subgroup.mem_subgroupOf.mp hs')))
  · rw [← map_mul]
    have : (⟨u, h.U_le.trans h.S_le h.u_mem⟩ * ⟨u, h.U_le.trans h.S_le h.u_mem⟩ : ↥(Cen z)) = 1 :=
      Subtype.ext (h.sq_eq_one_of_mem_U h.u_mem)
    rw [this, map_one]

theorem relIndex_T₂ (h : Ctx71 G z S U u) : (S ⊓ centralizer ({u} : Set G)).relIndex S = 2 := by
  rw [inf_comm, inf_relIndex_right]
  obtain ⟨s₀, hs₀S, hs₀⟩ := Set.not_subset.mp h.not_S_le_cen_u
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨s₀, hs₀S⟩, fun b => ?_⟩
  have hb := h.conj_u b.2
  have hs₀' := h.conj_u hs₀S
  have hs₀u : s₀ * u * s₀⁻¹ = u * z := hs₀'.resolve_left (fun e => hs₀
    (mem_centralizer_singleton_iff.mpr (by
      calc s₀ * u = s₀ * u * s₀⁻¹ * s₀ := by group
        _ = u * s₀ := by rw [e])))
  have hbz : (b : G) * z * (b : G)⁻¹ = z := by
    have hbz' : (b : G) * z = z * b := mem_centralizer_singleton_iff.mp (h.S_le b.2)
    rw [hbz']; group
  have hz2 : z * z = 1 := h.sq_eq_one_of_mem_U h.z_mem
  have key : ∀ x : G, x * u * x⁻¹ = u ↔ x ∈ centralizer ({u} : Set G) := by
    intro x
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro e
      calc x * u = x * u * x⁻¹ * x := by group
        _ = u * x := by rw [e]
    · intro e
      rw [e]; group
  have huz_ne : u * z ≠ u := h.uz_ne_u
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  rcases hb with hb | hb
  ·
    have h1 : (b : G) * s₀ * u * ((b : G) * s₀)⁻¹ = u * z := by
      calc (b : G) * s₀ * u * ((b : G) * s₀)⁻¹ = (b : G) * (s₀ * u * s₀⁻¹) * (b : G)⁻¹ := by group
        _ = ((b : G) * u * (b : G)⁻¹) * ((b : G) * z * (b : G)⁻¹) := by rw [hs₀u]; group
        _ = u * z := by rw [hb, hbz]
    refine Or.inr ⟨(key b).mp hb, fun hc => huz_ne ?_⟩
    rw [← h1]; exact (key _).mpr hc
  ·
    have h1 : (b : G) * s₀ * u * ((b : G) * s₀)⁻¹ = u := by
      calc (b : G) * s₀ * u * ((b : G) * s₀)⁻¹ = (b : G) * (s₀ * u * s₀⁻¹) * (b : G)⁻¹ := by group
        _ = ((b : G) * u * (b : G)⁻¹) * ((b : G) * z * (b : G)⁻¹) := by rw [hs₀u]; group
        _ = u * z * z := by rw [hb, hbz]
        _ = u := by rw [mul_assoc, hz2, mul_one]
    refine Or.inl ⟨(key _).mp h1, fun hc => huz_ne ?_⟩
    rw [← hb]; exact (key _).mpr hc

theorem card_T₂ (h : Ctx71 G z S U u) :
    Nat.card (S ⊓ centralizer ({u} : Set G) : Subgroup G) = 2 ^ 7 := by
  have h1 := relIndex_mul_card (S ⊓ centralizer ({u} : Set G)) S
  rw [h.relIndex_T₂, inf_of_le_left inf_le_left, h.card_S] at h1
  omega

end Ctx71

end CFSG.OddStandard.GH71
