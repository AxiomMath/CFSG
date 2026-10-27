module

public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Basic

public section

namespace GL83.CompFam

open CFSG.Open

variable {G : Type*} [Group G]

structure IsFam (p : ℕ) (B : Subgroup G) (𝒦 : Set (Subgroup G)) : Prop where
  elem : IsElemAbelian p B
  nonempty : 𝒦.Nonempty
  quasi : ∀ K ∈ 𝒦, IsQuasisimple K
  comm : ∀ K ∈ 𝒦, ∀ K' ∈ 𝒦, K ≠ K' → ∀ x ∈ K, ∀ y ∈ K', x * y = y * x
  smul_mem : ∀ K ∈ 𝒦, ∀ b ∈ B, cj b K ∈ 𝒦
  trans : ∀ K ∈ 𝒦, ∀ K' ∈ 𝒦, ∃ b ∈ B, cj b K = K'

@[expose] def layer (𝒦 : Set (Subgroup G)) : Subgroup G := ⨆ K ∈ 𝒦, K

@[expose] def stab (B K : Subgroup G) : Subgroup G := B ⊓ Subgroup.normalizer (K : Set G)

@[expose] def cen (B K : Subgroup G) : Subgroup G := B ⊓ Subgroup.centralizer (K : Set G)

theorem le_layer {𝒦 : Set (Subgroup G)} {K : Subgroup G} (hK : K ∈ 𝒦) : K ≤ layer 𝒦 :=
  le_iSup₂ (f := fun K (_ : K ∈ 𝒦) => K) K hK

theorem mem_stab {B K : Subgroup G} {b : G} : b ∈ stab B K ↔ b ∈ B ∧ cj b K = K := by
  rw [stab, Subgroup.mem_inf, cj_eq_iff_mem_normalizer]

theorem mem_cen {B K : Subgroup G} {b : G} :
    b ∈ cen B K ↔ b ∈ B ∧ ∀ x ∈ K, b * x = x * b := by
  rw [cen, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact and_congr_right fun _ => ⟨fun h x hx => (h x hx).symm, fun h x hx => (h x hx).symm⟩

theorem cj_eq_of_mem_cen {B K : Subgroup G} {b : G} (hb : b ∈ cen B K) : cj b K = K := by
  rw [mem_cen] at hb
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show b * y * b⁻¹ ∈ K
    rw [hb.2 y hy]
    simpa using hy
  · intro hx
    refine ⟨x, hx, ?_⟩
    show b * x * b⁻¹ = x
    rw [hb.2 x hx]
    group

theorem cen_le_stab (B K : Subgroup G) : cen B K ≤ stab B K := fun _ hb =>
  mem_stab.2 ⟨(mem_cen.1 hb).1, cj_eq_of_mem_cen hb⟩

section Fam

variable {p : ℕ} {B : Subgroup G} {𝒦 : Set (Subgroup G)}

theorem IsFam.mul_comm_of_mem (hF : IsFam p B 𝒦) {b c : G} (hb : b ∈ B) (hc : c ∈ B) :
    b * c = c * b :=
  elem_comm hF.elem hb hc

theorem IsFam.cj_cj_swap (hF : IsFam p B 𝒦) {b c : G} (hb : b ∈ B) (hc : c ∈ B)
    (K : Subgroup G) : cj b (cj c K) = cj c (cj b K) := by
  rw [← cj_mul, ← cj_mul, hF.mul_comm_of_mem hb hc]

theorem IsFam.stab_eq (hF : IsFam p B 𝒦) {K K₀ : Subgroup G} (hK : K ∈ 𝒦) (hK₀ : K₀ ∈ 𝒦) :
    stab B K = stab B K₀ := by
  obtain ⟨c, hc, rfl⟩ := hF.trans K₀ hK₀ K hK
  ext b
  rw [mem_stab, mem_stab]
  constructor
  · rintro ⟨hb, h⟩
    refine ⟨hb, ?_⟩
    rw [hF.cj_cj_swap hb hc] at h
    have := congrArg (cj c⁻¹) h
    rwa [cj_inv_cj, cj_inv_cj] at this
  · rintro ⟨hb, h⟩
    refine ⟨hb, ?_⟩
    rw [hF.cj_cj_swap hb hc, h]

theorem commute_conj_iff {b c x : G} (hbc : Commute b c) :
    Commute b (c * x * c⁻¹) ↔ Commute b x := by
  constructor
  · intro h
    have h2 : Commute b (c⁻¹ * (c * x * c⁻¹) * c) :=
      (hbc.inv_right.mul_right h).mul_right hbc
    have h3 : c⁻¹ * (c * x * c⁻¹) * c = x := by group
    rwa [h3] at h2
  · intro h
    exact (hbc.mul_right h).mul_right hbc.inv_right

theorem IsFam.cen_cj (hF : IsFam p B 𝒦) {c : G} (hc : c ∈ B) (K : Subgroup G) :
    cen B (cj c K) = cen B K := by
  ext b
  rw [mem_cen, mem_cen]
  refine and_congr_right fun hb => ?_
  have hbc := hF.mul_comm_of_mem hb hc
  constructor
  · intro h y hy
    exact (commute_conj_iff hbc).1 (h (c * y * c⁻¹) (mul_mem_cj hy))
  · intro h x hx
    have hy : c⁻¹ * x * c ∈ K := mem_cj.1 hx
    have hxy : x = c * (c⁻¹ * x * c) * c⁻¹ := by group
    rw [hxy]
    exact (commute_conj_iff hbc).2 (h _ hy)

theorem IsFam.cen_eq (hF : IsFam p B 𝒦) {K K₀ : Subgroup G} (hK : K ∈ 𝒦) (hK₀ : K₀ ∈ 𝒦) :
    cen B K = cen B K₀ := by
  obtain ⟨c, hc, rfl⟩ := hF.trans K₀ hK₀ K hK
  exact hF.cen_cj hc K₀

theorem IsFam.cen_comm (hF : IsFam p B 𝒦) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝒦) {b : G}
    (hb : b ∈ cen B K₀) {K : Subgroup G} (hK : K ∈ 𝒦) : ∀ x ∈ K, b * x = x * b := by
  have h' : b ∈ cen B K := by rw [hF.cen_eq hK hK₀]; exact hb
  exact (mem_cen.1 h').2

theorem IsFam.cj_layer_le (hF : IsFam p B 𝒦) {b : G} (hb : b ∈ B) :
    cj b (layer 𝒦) ≤ layer 𝒦 := by
  rw [layer, cj_iSup]
  refine iSup_le fun K => ?_
  rw [cj_iSup]
  exact iSup_le fun hK => le_layer (hF.smul_mem K hK b hb)

theorem IsFam.cj_layer (hF : IsFam p B 𝒦) {b : G} (hb : b ∈ B) :
    cj b (layer 𝒦) = layer 𝒦 := by
  refine le_antisymm (hF.cj_layer_le hb) ?_
  have hb' : b⁻¹ ∈ B := B.inv_mem hb
  have := cj_mono b (hF.cj_layer_le hb')
  rwa [cj_cj_inv] at this

end Fam

end GL83.CompFam
