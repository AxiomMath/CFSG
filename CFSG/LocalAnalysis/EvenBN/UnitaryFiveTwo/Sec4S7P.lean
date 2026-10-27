module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7L
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7M

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {d : Data G} {K₀ : Subgroup G}

theorem commutator_mul_of_conj_eq {G : Type*} [Group G] {b e c : G}
    (hcb : c * b⁻¹ * c⁻¹ = b⁻¹) : ⁅b, e * c⁆ = ⁅b, e⁆ := by
  simp only [commutatorElement_def]
  calc b * (e * c) * b⁻¹ * (e * c)⁻¹ = b * e * (c * b⁻¹ * c⁻¹) * e⁻¹ := by group
    _ = b * e * b⁻¹ * e⁻¹ := by rw [hcb]

omit [Finite G] in
theorem Data.e₁e₂_mem_K₂ : d.e₁ * d.e₂ ∈ d.K₂ :=
  ⟨e₁SU * e₂SU, e₁e₂_mem_K₂sub, map_mul d.ι e₁SU e₂SU⟩

omit [Finite G] in
theorem Data.e₁e₂_mem_L : d.e₁ * d.e₂ ∈ d.L := mul_mem (d.ι_mem e₁SU) (d.ι_mem e₂SU)

omit [Finite G] in
theorem Data.e₁e₂_comm_z : d.e₁ * d.e₂ * d.z = d.z * (d.e₁ * d.e₂) := by
  have := congrArg d.ι e₁e₂_comm_zSU
  simp only [map_mul] at this
  exact this

omit [Finite G] in
theorem Data.A₁_conj_e₁e₂ {a : G} (ha : a ∈ d.A₁) :
    d.e₁ * d.e₂ * a * (d.e₁ * d.e₂)⁻¹ ∈ d.A₁ := by
  obtain ⟨α, hα, rfl⟩ := ha
  refine ⟨_, A₁sub_conj_e₁e₂ hα, ?_⟩
  show d.ι (e₁SU * e₂SU * α * (e₁SU * e₂SU)⁻¹) =
    d.ι e₁SU * d.ι e₂SU * d.ι α * (d.ι e₁SU * d.ι e₂SU)⁻¹
  simp only [map_mul, map_inv]

omit [Finite G] in
theorem Data.A₁_commutator_zpowers_e₁e₂ : ⁅d.A₁, zpowers (d.e₁ * d.e₂)⁆ = d.A₁ := by
  have := congrArg (Subgroup.map d.ι) commutator_A₁sub_zpowers_e₁e₂
  rw [Subgroup.map_commutator, MonoidHom.map_zpowers, map_mul] at this
  exact this


section Gen



variable (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀)


include h hKU in
theorem Data.Hyp.exists_delta_eq_e₁e₂ :
    ∃ ε : ↥(Data.Nn h hKU hf), Data.delta h hKU hf ε = d.e₁ * d.e₂ := by
  have : d.e₁ * d.e₂ ∈ (Data.delta h hKU hf).range := by
    rw [h.range_delta_eq_A₂_sup_K₂ hKU hf]
    exact mem_sup_right Data.e₁e₂_mem_K₂
  exact this

include h hKU in
theorem Data.Hyp.e₁e₂_conj_eq {x : G} (hx : x ∈ Data.Nn h hKU hf) {ε : ↥(Data.Nn h hKU hf)}
    (hε : Data.delta h hKU hf ε = d.e₁ * d.e₂) :
    (d.e₁ * d.e₂) * x * (d.e₁ * d.e₂)⁻¹ = (ε : G) * x * (ε : G)⁻¹ := by
  rw [← hε]
  exact h.delta_conj hKU hf ε hx

include h hKU in
theorem Data.Hyp.e₁e₂_conj_mem_B₁ {x : G} (hx : x ∈ Data.B₁ h hKU hf) :
    (d.e₁ * d.e₂) * x * (d.e₁ * d.e₂)⁻¹ ∈ Data.B₁ h hKU hf := by
  obtain ⟨ε, hε⟩ := h.exists_delta_eq_e₁e₂ hKU hf
  obtain ⟨hxN, hxA⟩ := (h.mem_B₁_iff hKU hf).1 hx
  rw [h.e₁e₂_conj_eq hKU hf hxN hε]
  have hcN : (ε : G) * x * (ε : G)⁻¹ ∈ Data.Nn h hKU hf :=
    mul_mem (mul_mem ε.2 hxN) (inv_mem ε.2)
  refine (h.mem_B₁_iff hKU hf).2 ⟨hcN, ?_⟩
  have key : Data.delta h hKU hf ⟨(ε : G) * x * (ε : G)⁻¹, hcN⟩ =
      (d.e₁ * d.e₂) * (x * (d.t * x * d.t)) * (d.e₁ * d.e₂)⁻¹ := by
    have e : (ε * ⟨x, hxN⟩ * ε⁻¹ : ↥(Data.Nn h hKU hf)) = ⟨(ε : G) * x * (ε : G)⁻¹, hcN⟩ := rfl
    rw [← e, map_mul, map_mul, map_inv, hε]
    rfl
  have hconj := Data.A₁_conj_e₁e₂ hxA
  rw [← key] at hconj
  exact hconj

include h hKU in
theorem Data.Hyp.e₁e₂_mem_normalizer_B₁ :
    d.e₁ * d.e₂ ∈ normalizer (Data.B₁ h hKU hf : Set G) :=
  mem_normalizer_fintype fun _ hx => h.e₁e₂_conj_mem_B₁ hKU hf hx

include h hKU in
theorem Data.Hyp.e₁e₂_comm_ZQ {ζ : G} (hζ : ζ ∈ Data.ZQ h hKU hf) :
    (d.e₁ * d.e₂) * ζ = ζ * (d.e₁ * d.e₂) := by
  obtain ⟨ε, hε⟩ := h.exists_delta_eq_e₁e₂ hKU hf
  obtain ⟨hζN, hζZ⟩ := (h.mem_ZQ_iff hKU hf).1 hζ
  have hε' : (ε : G) * (d.t * (ε : G) * d.t) = d.e₁ * d.e₂ := hε
  have hεζ : (ε : G) * ζ = ζ * (ε : G) := by
    rw [h.comm_iff_delta_comm hKU hf ε.2 hζN, hε']
    rcases Data.Hyp.eq_one_or_eq_z hζZ with h1 | h1
    · rw [h1]
      simp
    · rw [h1]
      exact Data.e₁e₂_comm_z
  have hτ : d.t * (ε : G) * d.t ∈ d.tc (Data.Nn h hKU hf) := h.t_conj_mem_tcNn hKU hf ε.2
  have hτζ : (d.t * (ε : G) * d.t) * ζ = ζ * (d.t * (ε : G) * d.t) :=
    (h.comm_Nn_tcNn hKU hf hζN hτ).symm
  rw [← hε']
  calc (ε : G) * (d.t * (ε : G) * d.t) * ζ = (ε : G) * ((d.t * (ε : G) * d.t) * ζ) := by group
    _ = (ε : G) * (ζ * (d.t * (ε : G) * d.t)) := by rw [hτζ]
    _ = ((ε : G) * ζ) * (d.t * (ε : G) * d.t) := by group
    _ = (ζ * (ε : G)) * (d.t * (ε : G) * d.t) := by rw [hεζ]
    _ = ζ * ((ε : G) * (d.t * (ε : G) * d.t)) := by group

include h hKU hf in
theorem Data.Hyp.e₁e₂_comm_W {w : G} (hw : w ∈ d.W) :
    d.e₁ * d.e₂ * w = w * (d.e₁ * d.e₂) := by
  have hgt : (d.e₁ * d.e₂) * d.t = d.t * (d.e₁ * d.e₂) := h.t_comm_of_mem_L Data.e₁e₂_mem_L
  have htg : d.t * (d.e₁ * d.e₂) * d.t = d.e₁ * d.e₂ := by
    rw [← hgt, mul_assoc, h.t_mul_t, mul_one]
  rw [h.W_eq_ZQ_sup hKU hf] at hw
  obtain ⟨a, ha, b, hb, rfl⟩ := KProd.exists_mul_of_mem_sup_of_comm (fun a ha b hb =>
    h.comm_Nn_tcNn hKU hf (h.ZQ_le_Nn hKU hf ha) (h.tc_mono (h.ZQ_le_Nn hKU hf) hb)) hw
  have hga := h.e₁e₂_comm_ZQ hKU hf ha
  have hgb' := h.e₁e₂_comm_ZQ hKU hf ((h.mem_tc).1 hb)
  have hgb : (d.e₁ * d.e₂) * b = b * (d.e₁ * d.e₂) := by
    have h1 := h.t_conj_comm_of_comm hgb'
    rwa [htg, h.t_conj_conj] at h1
  calc (d.e₁ * d.e₂) * (a * b) = ((d.e₁ * d.e₂) * a) * b := by group
    _ = (a * (d.e₁ * d.e₂)) * b := by rw [hga]
    _ = a * ((d.e₁ * d.e₂) * b) := by group
    _ = a * (b * (d.e₁ * d.e₂)) := by rw [hgb]
    _ = (a * b) * (d.e₁ * d.e₂) := by group

include h hKU in
theorem Data.Hyp.B₁_eq_commutator_g :
    Data.B₁ h hKU hf = ⁅Data.B₁ h hKU hf ⊔ d.W, zpowers (d.e₁ * d.e₂)⁆ := by
  have hgN := h.e₁e₂_mem_normalizer_B₁ hKU hf
  refine le_antisymm ?_ ?_
  ·
    obtain ⟨ε, hε⟩ := h.exists_delta_eq_e₁e₂ hKU hf
    set H₁ : Subgroup ↥(Data.Nn h hKU hf) := d.A₁.comap (Data.delta h hKU hf) with hH₁
    set H₂ : Subgroup ↥(Data.Nn h hKU hf) := zpowers ε with hH₂
    have hH₁map : H₁.map (Data.delta h hKU hf) = d.A₁ := by
      rw [hH₁, Subgroup.map_comap_eq, inf_eq_right.2 (d.A₁_le_S.trans (h.S_le_range_delta hKU hf))]
    have hH₂map : H₂.map (Data.delta h hKU hf) = zpowers (d.e₁ * d.e₂) := by
      rw [hH₂, MonoidHom.map_zpowers, hε]
    have hcomm : ⁅H₁, H₂⁆ = H₁ := by
      apply Subgroup.map_injective (h.delta_injective hKU hf)
      rw [Subgroup.map_commutator, hH₁map, hH₂map, Data.A₁_commutator_zpowers_e₁e₂]
    have hB : Data.B₁ h hKU hf = ⁅Data.B₁ h hKU hf, zpowers (ε : G)⁆ := by
      have e1 : Data.B₁ h hKU hf = H₁.map (Data.Nn h hKU hf).subtype := rfl
      have e2 : zpowers (ε : G) = H₂.map (Data.Nn h hKU hf).subtype :=
        (MonoidHom.map_zpowers (Data.Nn h hKU hf).subtype ε).symm
      rw [e2, e1, ← Subgroup.map_commutator, hcomm]
    refine hB.le.trans ?_
    rw [Subgroup.commutator_le]
    intro b hb y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    have hτ : d.t * (ε : G) * d.t ∈ d.tc (Data.Nn h hKU hf) := h.t_conj_mem_tcNn hKU hf ε.2
    have hcε : Commute (ε : G) (d.t * (ε : G) * d.t) := h.comm_Nn_tcNn hKU hf ε.2 hτ
    have hg : d.e₁ * d.e₂ = (ε : G) * (d.t * (ε : G) * d.t) := hε.symm
    have hgk : (d.e₁ * d.e₂) ^ k = (ε : G) ^ k * (d.t * (ε : G) * d.t) ^ k := by
      rw [hg]
      exact hcε.mul_zpow k
    have hck : (d.t * (ε : G) * d.t) ^ k ∈ d.tc (Data.Nn h hKU hf) := zpow_mem hτ k
    have hcb : (d.t * (ε : G) * d.t) ^ k * b⁻¹ * ((d.t * (ε : G) * d.t) ^ k)⁻¹ = b⁻¹ := by
      have := h.comm_Nn_tcNn hKU hf (inv_mem (h.B₁_le_Nn hKU hf hb)) hck
      rw [← this, mul_inv_cancel_right]
    have e : ⁅b, (ε : G) ^ k⁆ = ⁅b, (d.e₁ * d.e₂) ^ k⁆ := by
      rw [hgk]
      exact (commutator_mul_of_conj_eq hcb).symm
    rw [e]
    exact Subgroup.commutator_mem_commutator (mem_sup_left hb) (zpow_mem_zpowers _ _)
  ·
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨b, hb, w, hw, rfl⟩ := KProd.exists_mul_of_mem_sup_of_comm
      (fun a ha w hw => (h.W_comm_P hKU hw (h.B₁_le_Q hKU hf ha).1).symm) hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    have hwg : w * (d.e₁ * d.e₂) ^ k = (d.e₁ * d.e₂) ^ k * w :=
      ((Commute.zpow_left (show Commute (d.e₁ * d.e₂) w from h.e₁e₂_comm_W hKU hf hw) k).eq).symm
    have hwg' : w * (d.e₁ * d.e₂) ^ k * w⁻¹ = (d.e₁ * d.e₂) ^ k := by
      rw [hwg, mul_inv_cancel_right]
    have e : ⁅b * w, (d.e₁ * d.e₂) ^ k⁆ =
        b * ((d.e₁ * d.e₂) ^ k * b⁻¹ * ((d.e₁ * d.e₂) ^ k)⁻¹) := by
      rw [commutatorElement_def]
      calc b * w * (d.e₁ * d.e₂) ^ k * (b * w)⁻¹ * ((d.e₁ * d.e₂) ^ k)⁻¹
          = b * (w * (d.e₁ * d.e₂) ^ k * w⁻¹) * b⁻¹ * ((d.e₁ * d.e₂) ^ k)⁻¹ := by group
        _ = b * (d.e₁ * d.e₂) ^ k * b⁻¹ * ((d.e₁ * d.e₂) ^ k)⁻¹ := by rw [hwg']
        _ = b * ((d.e₁ * d.e₂) ^ k * b⁻¹ * ((d.e₁ * d.e₂) ^ k)⁻¹) := by group
    rw [e]
    exact mul_mem hb ((mem_normalizer_iff.1 (zpow_mem hgN k) b⁻¹).1 (inv_mem hb))

end Gen

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
