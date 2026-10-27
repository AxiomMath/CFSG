module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6bDict

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6b

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits CFSG.Open

section E25glue

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


variable [Fact (∀ a b : ↥d.s56V, a * b = b * a)] [Fact (∀ a : ↥d.s56V, a * a = 1)]

theorem p6b_exists_starB (σ : ↥(Hs d)) : ∃ (g : G) (hg : g ∈ Hg d), starB d g hg = σ := by
  obtain ⟨g, hg, -, hgσ⟩ := (mem_imgIn_iff d.s56V (Hg d)).1 σ.2
  exact ⟨g, hg, Subtype.ext hgσ⟩

theorem p6b_mem_pre (J : Subgroup ↥(Hs d)) {y : G} :
    y ∈ pre d (J.map (Hs d).subtype) ↔ ∃ hy : y ∈ Hg d, starB d y hy ∈ J := by
  rw [show pre d (J.map (Hs d).subtype) = preIn d.s56V (J.map (Hs d).subtype) from rfl,
    mem_preIn_iff]
  constructor
  · rintro ⟨hy, σ, hσ, hσy⟩
    refine ⟨hy, ?_⟩
    have : starB d y hy = σ := Subtype.ext hσy.symm
    rwa [this]
  · rintro ⟨hy, h⟩
    exact ⟨hy, starB d y hy, h, rfl⟩

theorem p6b_comm_inv (hcG : ∀ a ∈ d.s56V, ∀ b ∈ d.s56V, a * b = b * a) {y : G} (hy : y ∈ Hg d)
    (u : ↥d.s56V) :
    ((u⁻¹ * (starB d y hy : MulAut ↥d.s56V) u : ↥d.s56V) : G) =
      ((u : G) * y * (u : G)⁻¹ * y⁻¹)⁻¹ := by
  have h1 : ((star d y u : ↥d.s56V) : G) = y * u * y⁻¹ := star_apply_val hy u
  have hmem : y * (u : G) * y⁻¹ ∈ d.s56V := h1 ▸ (star d y u).2
  have hc : (u : G)⁻¹ * (y * u * y⁻¹) = (y * u * y⁻¹) * (u : G)⁻¹ := hcG _ (inv_mem u.2) _ hmem
  show (u : G)⁻¹ * ((star d y u : ↥d.s56V) : G) = _
  rw [h1, hc]
  group

theorem p6b_centMod_pre (hZH : ∀ g ∈ Hg d, ∀ y ∈ Zz d z₀, g * y * g⁻¹ ∈ Zz d z₀)
    (hcG : ∀ a ∈ d.s56V, ∀ b ∈ d.s56V, a * b = b * a) (J : Subgroup ↥(Hs d)) :
    centralizerMod d.s56V (Zz d z₀) (pre d (J.map (Hs d).subtype)) =
      (centModSub (Zv d z₀) J).map d.s56V.subtype := by
  ext v
  constructor
  · rintro ⟨hvV, -, hv⟩
    refine ⟨⟨v, hvV⟩, fun σ hσ => ?_, rfl⟩
    obtain ⟨y, hy, rfl⟩ := p6b_exists_starB σ
    have h1 : v * y * v⁻¹ * y⁻¹ ∈ Zz d z₀ := hv y ((p6b_mem_pre J).2 ⟨hy, hσ⟩)
    refine Subgroup.mem_subgroupOf.2 ?_
    rw [p6b_comm_inv hcG hy ⟨v, hvV⟩]
    exact inv_mem h1
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u.2, mem_normalizer_Z hZH (Subgroup.le_normalizer u.2), fun y hy => ?_⟩
    obtain ⟨hyH, hyJ⟩ := (p6b_mem_pre J).1 hy
    have h1 := Subgroup.mem_subgroupOf.1 (hu _ hyJ)
    rw [p6b_comm_inv hcG hyH u] at h1
    exact inv_mem_iff.1 h1

theorem node23b_E25 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (hinv : d.S56Z0Inv)
    (hcard : Nat.card d.s56V = 2 ^ 10)
    (hZH : ∀ g ∈ Hg d, ∀ y ∈ Zz d z₀, g * y * g⁻¹ ∈ Zz d z₀)
    {h₀ : G} (hh₀ : h₀ ∈ Hg d) (hh : star d (h₀ * d.t * h₀⁻¹) = star d (d.t * d.pv 2))
    (hWimg : img d (Wg d z₀) = Ws d)
    (hWnorm : ∀ h ∈ Hs d, ∀ w ∈ Ws d, h * w * h⁻¹ ∈ Ws d)
    (hWel : IsElemAbelian 2 (Ws d)) (hWJ : Ws d ≤ img d (Jg d))
    [hN : ((Ws d).subgroupOf (img d (Jg d))).Normal]
    (e : ↥(img d (Jg d)) ⧸ (Ws d).subgroupOf (img d (Jg d)) ≃*
      Multiplicative (ZMod 5) × Multiplicative (ZMod 5))
    (core : E25CoreStmt) : N23bE25 d z₀ := by
  have hc : ∀ a b : ↥d.s56V, a * b = b * a := Fact.out
  have hs : ∀ a : ↥d.s56V, a * a = 1 := Fact.out
  have hcG : ∀ a ∈ d.s56V, ∀ b ∈ d.s56V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hc ⟨a, ha⟩ ⟨b, hb⟩)
  have hsG : ∀ a ∈ d.s56V, a * a = 1 := fun a ha => congrArg Subtype.val (hs ⟨a, ha⟩)
  have M := mdata_d h49 hd hz hinv hcard hh₀ hh
  haveI hWbN : ((Ws d).subgroupOf (Hs d)).Normal := Wb_normal hWnorm
  have hW2 : ∀ w ∈ (Ws d).subgroupOf (Hs d), w * w = 1 := by
    intro w hw
    have := hWel.2 (w : MulAut ↥d.s56V) (Subgroup.mem_subgroupOf.1 hw)
    exact Subtype.ext (by simpa [pow_two] using this)
  have hWJb := Wb_le_Jb h49 hd hWJ
  obtain ⟨eb⟩ := jb_quot_equiv h49 hd hWJ _ e
  obtain ⟨J₁, J₂, hWJ₁, hJ₁, hWJ₂, hJ₂, hdec, hinfW, hr₁, hr₂, hsupV, hinfV, hZr₁, hZr₂, hcM⟩ :=
    E25_branch (hB := map_Zv_eq hZH) M ((Ws d).subgroupOf (Hs d)) hW2 hWJb ⟨eb⟩
      (fun H hab => core _ H hab)
  have hZv := Zv_map h49 hd hz
  have hWH : Ws d ≤ Hs d := hWJ.trans (imgIn_mono d.s56V (Jg_le_Hg d))
  have hWmap : ((Ws d).subgroupOf (Hs d)).map (Hs d).subtype = Ws d :=
    Subgroup.map_subgroupOf_eq_of_le hWH
  have hJle : ∀ K : Subgroup ↥(Hs d), K ≤ normalClosure ({xB h49 hd} : Set ↥(Hs d)) →
      K.map (Hs d).subtype ≤ img d (Jg d) := fun K hK =>
    (Subgroup.map_mono hK).trans (Jb_map_eq h49 hd).le
  have hWle : ∀ K : Subgroup ↥(Hs d), (Ws d).subgroupOf (Hs d) ≤ K →
      Wg d z₀ ≤ pre d (K.map (Hs d).subtype) := by
    intro K hK
    rw [Wg_eq_pre hz hWimg]
    refine preIn_mono d.s56V ?_
    rw [← hWmap]
    exact Subgroup.map_mono hK
  have hrel : ∀ K : Subgroup ↥(Hs d), ((Ws d).subgroupOf (Hs d)).relIndex K = 5 →
      (Wg d z₀).relIndex (pre d (K.map (Hs d).subtype)) = 5 := by
    intro K hK
    rw [Wg_eq_pre hz hWimg]
    have h1 := relIndex_preIn (S := d.s56V) (K₁ := Ws d) (K₂ := K.map (Hs d).subtype)
      (Subgroup.map_subtype_le _)
    have h2 : (Ws d).relIndex (K.map (Hs d).subtype) = 5 := by
      rw [← hK, ← Subgroup.relIndex_map_map_of_injective _ _ (Hs d).subtype_injective, hWmap]
    exact h1.trans h2
  refine ⟨jp_quot_equiv hz hWimg _ e, pre d (J₁.map (Hs d).subtype), pre d (J₂.map (Hs d).subtype),
    centralizerMod d.s56V (Zz d z₀) (pre d (J₁.map (Hs d).subtype)),
    centralizerMod d.s56V (Zz d z₀) (pre d (J₂.map (Hs d).subtype)),
    hWle J₁ hWJ₁, preIn_mono d.s56V (hJle J₁ hJ₁), hWle J₂ hWJ₂, preIn_mono d.s56V (hJle J₂ hJ₂),
    ?_, ?_, hrel J₁ hr₁, hrel J₂ hr₂, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine le_antisymm (sup_le (preIn_mono d.s56V (hJle J₁ hJ₁))
      (preIn_mono d.s56V (hJle J₂ hJ₂))) ?_
    intro g hg
    have hgH : g ∈ Hg d := ((mem_preIn_iff d.s56V _).1 hg).1
    obtain ⟨σ₁, hσ₁, σ₂, hσ₂, hσ⟩ := hdec _ (starB_mem_Jb h49 hd hg)
    obtain ⟨g₁, hg₁, hgσ₁⟩ := p6b_exists_starB σ₁
    have hg₂ : g₁⁻¹ * g ∈ Hg d := mul_mem (inv_mem hg₁) hgH
    have h1 : g₁ ∈ pre d (J₁.map (Hs d).subtype) :=
      (p6b_mem_pre J₁).2 ⟨hg₁, by rw [hgσ₁]; exact hσ₁⟩
    have h2 : g₁⁻¹ * g ∈ pre d (J₂.map (Hs d).subtype) := by
      refine (p6b_mem_pre J₂).2 ⟨hg₂, ?_⟩
      have e1 : (σ₁ : MulAut ↥d.s56V) = actFun d.s56V g₁ := congrArg Subtype.val hgσ₁.symm
      have e2 : (σ₁ : MulAut ↥d.s56V) * σ₂ = actFun d.s56V g := congrArg Subtype.val hσ
      have : starB d (g₁⁻¹ * g) hg₂ = σ₂ := by
        refine Subtype.ext ?_
        show actFun d.s56V (g₁⁻¹ * g) = (σ₂ : MulAut ↥d.s56V)
        rw [actFun_mul d.s56V (inv_mem hg₁) hgH, actFun_inv d.s56V hg₁, ← e1, ← e2]
        group
      rwa [this]
    have hg' : g = g₁ * (g₁⁻¹ * g) := by group
    rw [hg']
    exact mul_mem_sup h1 h2
  ·
    refine (preIn_inf d.s56V _ _).symm.trans ?_
    rw [← Subgroup.map_inf _ _ _ (Subgroup.subtype_injective _), hinfW, hWmap]
    exact (Wg_eq_pre hz hWimg).symm
  ·
    rw [p6b_centMod_pre hZH hcG J₁, p6b_centMod_pre hZH hcG J₂, ← Subgroup.map_sup, hsupV,
      Subgroup.map_top, Subgroup.range_subtype]
  ·
    rw [p6b_centMod_pre hZH hcG J₁, p6b_centMod_pre hZH hcG J₂,
      ← Subgroup.map_inf _ _ _ (Subgroup.subtype_injective _), hinfV, hZv]
  ·
    have := isElemAbQuot_map d.s56V hcG hsG (le_centModSub (map_Zv_eq hZH) J₁) hZr₁
    rw [hZv] at this
    rwa [p6b_centMod_pre hZH hcG J₁]
  ·
    have := isElemAbQuot_map d.s56V hcG hsG (le_centModSub (map_Zv_eq hZH) J₂) hZr₂
    rw [hZv] at this
    rwa [p6b_centMod_pre hZH hcG J₂]
  ·
    rw [p6b_centMod_pre hZH hcG J₁, p6b_centMod_pre hZH hcG J₂, hcM]
    exact conj_transfer (t_mem_H h49 hd) (centModSub (Zv d z₀) J₁)

end E25glue

end CFSG.LocalAnalysis.EvenBN.Tits.N.P6b
