module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBParts

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

namespace CaseBData

theorem sec52_gen_δ_conj (hB : d.CaseBHyp) (c : d.CaseBData) {g : G}
    (hg : g ∈ centralizer ({d.t} : Set G)) (y : c.Kc)
    (hgy : g * (y : G) * g⁻¹ ∈ c.Kc) :
    c.δ hB ⟨g * (y : G) * g⁻¹, hgy⟩ = g * c.δ hB y * g⁻¹ := by
  have hc : g * d.t = d.t * g :=
    (Subgroup.mem_centralizer_iff.1 hg d.t (Set.mem_singleton _)).symm
  have e1 : d.t⁻¹ * g = g * d.t⁻¹ := by
    calc d.t⁻¹ * g = d.t⁻¹ * (g * d.t) * d.t⁻¹ := by group
      _ = d.t⁻¹ * (d.t * g) * d.t⁻¹ := by rw [hc]
      _ = g * d.t⁻¹ := by group
  have e2 : g⁻¹ * d.t = d.t * g⁻¹ := by
    calc g⁻¹ * d.t = g⁻¹ * (d.t * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * d.t) * g⁻¹ := by rw [← hc]
      _ = d.t * g⁻¹ := by group
  have key : d.t⁻¹ * (g * (y : G) * g⁻¹) * d.t = g * (d.t⁻¹ * (y : G) * d.t) * g⁻¹ := by
    rw [show d.t⁻¹ * (g * (y : G) * g⁻¹) * d.t = (d.t⁻¹ * g) * (y : G) * (g⁻¹ * d.t) by group,
      e1, e2]
    group
  change (g * (y : G) * g⁻¹) * (d.t⁻¹ * (g * (y : G) * g⁻¹) * d.t) =
    g * ((y : G) * (d.t⁻¹ * (y : G) * d.t)) * g⁻¹
  rw [key]
  group

theorem sec52_gen (hB : d.CaseBHyp) (c : d.CaseBData) (h11 : CaseBData.Sec52Sylow hB c)
    (h12 : CaseBData.Sec52Factors hB c) (h13 : c.W₂.map (MulAut.conj d.s).toMonoidHom = c.W₂) :
    c.Kc = c.W₂ ⊔ (c.W₂ ⊓ c.W₂.map (MulAut.conj d.r).toMonoidHom).map
      (MulAut.conj (d.r * d.s)).toMonoidHom := by
  have hsC : d.s ∈ centralizer ({d.t} : Set G) := hB.hyp.s_mem_centralizer_t
  have hrC : d.r ∈ centralizer ({d.t} : Set G) := by
    have hr0 : d.r ∈ d.L₁ ⊓ centralizer ({d.t} : Set G) := by
      rw [hB.L₁_inf_centralizer_t]
      exact (le_sup_right : d.N₁ ≤ d.A₃ ⊔ d.N₁) d.r_mem_N₁
    exact (Subgroup.mem_inf.1 hr0).2
  have hrsC : d.r * d.s ∈ centralizer ({d.t} : Set G) := mul_mem hrC hsC
  have hr : d.r ∈ normalizer (c.Kc : Set G) := c.L₁_le_normalizer_Kc (d.N₁_le_L₁ d.r_mem_N₁)
  have hrN : ∀ y ∈ c.Kc, d.r * y * d.r⁻¹ ∈ c.Kc := fun y hy =>
    (Subgroup.mem_normalizer_iff.1 hr y).1 hy
  have hWK : c.W₂ ≤ c.Kc := inf_le_right
  obtain ⟨M, hM⟩ : ∃ M : Subgroup G, M = c.W₂ ⊔
      (c.W₂ ⊓ c.W₂.map (MulAut.conj d.r).toMonoidHom).map (MulAut.conj (d.r * d.s)).toMonoidHom :=
    ⟨_, rfl⟩
  rw [← hM]
  have hWM : c.W₂ ≤ M := by
    rw [hM]
    exact le_sup_left
  have hXM : (c.W₂ ⊓ c.W₂.map (MulAut.conj d.r).toMonoidHom).map
      (MulAut.conj (d.r * d.s)).toMonoidHom ≤ M := by
    rw [hM]
    exact le_sup_right
  have hMK : M ≤ c.Kc := by
    rw [hM]
    refine sup_le hWK ?_
    rintro _ ⟨x, hx, rfl⟩
    have hsx : d.s * x * d.s⁻¹ ∈ c.W₂ := by
      rw [← h13]
      exact Subgroup.mem_map_of_mem (MulAut.conj d.s).toMonoidHom (Subgroup.mem_inf.1 hx).1
    have e : (MulAut.conj (d.r * d.s)).toMonoidHom x = d.r * (d.s * x * d.s⁻¹) * d.r⁻¹ := by
      show (d.r * d.s) * x * (d.r * d.s)⁻¹ = _
      group
    rw [e]
    exact hrN _ (hWK hsx)
  have hpre : ∀ {a : G}, a ∈ d.A₂ → ∃ w : c.Kc, (w : G) ∈ c.W₂ ∧ c.δ hB w = a := by
    intro a ha
    rw [← h12.map_δ] at ha
    obtain ⟨w, hw, hwa⟩ := Subgroup.mem_map.1 ha
    exact ⟨w, Subgroup.mem_subgroupOf.1 hw, hwa⟩
  have hA2 : d.A₂ ≤ (M.subgroupOf c.Kc).map (c.δ hB) := by
    rw [← h12.map_δ]
    refine Subgroup.map_mono ?_
    intro w hw
    exact Subgroup.mem_subgroupOf.2 (hWM (Subgroup.mem_subgroupOf.1 hw))
  have hX : (d.A₂ ⊓ d.A₂.map (MulAut.conj d.r).toMonoidHom).map
      (MulAut.conj (d.r * d.s)).toMonoidHom ≤ (M.subgroupOf c.Kc).map (c.δ hB) := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨w0, hw0W, hw0a⟩ := hpre (Subgroup.mem_inf.1 ha).1
    obtain ⟨a', ha', har⟩ := Subgroup.mem_map.1 (Subgroup.mem_inf.1 ha).2
    obtain ⟨w1, hw1W, hw1a⟩ := hpre ha'
    have hrw1 : d.r * (w1 : G) * d.r⁻¹ ∈ c.Kc := hrN _ w1.2
    have hinj : (⟨d.r * (w1 : G) * d.r⁻¹, hrw1⟩ : c.Kc) = w0 := by
      apply c.injective_δ hB
      rw [sec52_gen_δ_conj hB c hrC w1 hrw1, hw1a, hw0a]
      exact har
    have hw0r : (w0 : G) ∈ c.W₂.map (MulAut.conj d.r).toMonoidHom :=
      Subgroup.mem_map.2 ⟨(w1 : G), hw1W, congrArg Subtype.val hinj⟩
    have hmem' : (MulAut.conj (d.r * d.s)).toMonoidHom (w0 : G) ∈
        (c.W₂ ⊓ c.W₂.map (MulAut.conj d.r).toMonoidHom).map
          (MulAut.conj (d.r * d.s)).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj (d.r * d.s)).toMonoidHom
        (Subgroup.mem_inf.2 ⟨hw0W, hw0r⟩)
    have hmem := hXM hmem'
    rw [← hw0a]
    exact Subgroup.mem_map.2 ⟨⟨(MulAut.conj (d.r * d.s)).toMonoidHom (w0 : G), hMK hmem⟩,
      Subgroup.mem_subgroupOf.2 hmem, sec52_gen_δ_conj hB c hrsC w0 (hMK hmem)⟩
  have hrange : (c.δ hB).range ≤ (M.subgroupOf c.Kc).map (c.δ hB) := by
    rw [c.range_δ hB, hB.L₁_inf_centralizer_t, Data.A₃_sup_N₁_eq d]
    exact sup_le hA2 hX
  have hKM : c.Kc ≤ M := by
    intro k hk
    have hkr : c.δ hB ⟨k, hk⟩ ∈ (c.δ hB).range := MonoidHom.mem_range.2 ⟨⟨k, hk⟩, rfl⟩
    obtain ⟨m, hm, hmk⟩ := Subgroup.mem_map.1 (hrange hkr)
    have hmk' : m = ⟨k, hk⟩ := c.injective_δ hB hmk
    have hval : (m : G) = k := congrArg Subtype.val hmk'
    rw [← hval]
    exact Subgroup.mem_subgroupOf.1 hm
  exact le_antisymm hKM hMK

end CaseBData

end Data

namespace CaseBParts

theorem sec52Gen : Sec52GenStatement :=
  fun _ _ _ _ _ _ _ _ hB c h11 h12 h13 => Data.CaseBData.sec52_gen hB c h11 h12 h13

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
