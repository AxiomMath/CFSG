module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6L

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

variable {G : Type} [Group G] [Finite G] {d : Data G} {K₀ : Subgroup G}

section Normalizing



variable (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀)

include hKU in
theorem Data.Hyp.theta_mem_F_iff (k : ↥K₀) :
    (k : G) ∈ d.Y ↔ Data.theta h hf k ∈ d.F := by
  constructor
  · intro hk
    have hY' : d.t * (k : G) * d.t ∈ d.Y := h.t_conj_mem_Y hk
    have hθY : Data.theta h hf k ∈ d.Y := by
      rw [Data.theta_apply]
      exact mul_mem hk hY'
    have hθH : Data.theta h hf k ∈ centralizer ({d.t} : Set G) :=
      Common.range_diagonalHom_le (hf.comm_inv0 h) h.t_mul_t ⟨k, rfl⟩
    rw [← h.sec4_6.2.2.2.1]
    exact ⟨hθY, hθH⟩
  · intro hθF
    have hθY : Data.theta h hf k ∈ d.Y := h.F_le_Y hθF
    obtain ⟨a, ha, b, hb, hab⟩ := h.exists_mul_of_mem_Y hKU hf hθY
    have hab' : (k : G) * (d.t * (k : G) * d.t) = a * b := by
      rw [← Data.theta_apply]
      exact hab
    have htk : d.t * (k : G) * d.t ∈ d.tc K₀ :=
      (h.mem_tc).2 (by rw [h.t_conj_conj]; exact k.2)
    obtain ⟨e1, -⟩ := hf.unique k.2 ha.2 htk hb.2 hab'
    rw [e1]
    exact ha.1

include hKU in
theorem Data.Hyp.Lam₁_conj_mem_I {l a : G} (hl : l ∈ Data.Lam₁ h hKU hf) (ha : a ∈ d.Y ⊓ K₀) :
    l * a * l⁻¹ ∈ d.Y ⊓ K₀ := by
  have hl0 : l ∈ K₀ := Data.Lam₁_le_K₀ h hKU hf hl
  set L' : ↥K₀ := ⟨l, hl0⟩
  set A' : ↥K₀ := ⟨a, ha.2⟩
  have hθL : Data.theta h hf L' ∈ d.K₂ := Data.theta_mem_K₂_of_mem_Lam₁ h hKU hf L' hl
  have hθA : Data.theta h hf A' ∈ d.F := (h.theta_mem_F_iff hKU hf A').1 ha.1
  have hconj : Data.theta h hf (L' * A' * L'⁻¹) ∈ d.F := by
    rw [map_mul, map_mul, map_inv]
    exact Data.K₂_conj_mem_F hθL hθA
  refine ⟨(h.theta_mem_F_iff hKU hf (L' * A' * L'⁻¹)).2 hconj, ?_⟩
  exact K₀.mul_mem (K₀.mul_mem hl0 ha.2) (K₀.inv_mem hl0)

include hKU in
theorem Data.Hyp.Lam₁_conj_mem_Y {l y : G} (hl : l ∈ Data.Lam₁ h hKU hf) (hy : y ∈ d.Y) :
    l * y * l⁻¹ ∈ d.Y := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul_of_mem_Y hKU hf hy
  have hl0 : l ∈ K₀ := Data.Lam₁_le_K₀ h hKU hf hl
  have hbl : l * b = b * l := hf.comm_elem l hl0 b hb.2
  have e : l * (a * b) * l⁻¹ = (l * a * l⁻¹) * b := by
    calc l * (a * b) * l⁻¹ = (l * a) * (b * l⁻¹) := by group
      _ = (l * a) * (l⁻¹ * b) := by
          congr 1
          rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hbl]; group
      _ = (l * a * l⁻¹) * b := by group
  rw [e]
  exact mul_mem (h.Lam₁_conj_mem_I hKU hf hl ha).1 hb.1

include hKU in
theorem Data.Hyp.Lam₁_le_normalizer_Y : Data.Lam₁ h hKU hf ≤ normalizer (d.Y : Set G) :=
  fun _ hl => mem_normalizer_fintype fun _ hy => h.Lam₁_conj_mem_Y hKU hf hl hy

include hKU in
theorem Data.Hyp.tcLam₁_le_normalizer_Y :
    d.tc (Data.Lam₁ h hKU hf) ≤ normalizer (d.Y : Set G) := by
  intro m hm
  refine mem_normalizer_fintype fun y hy => ?_
  have hm' : d.t * m * d.t ∈ Data.Lam₁ h hKU hf := (h.mem_tc).1 hm
  have hy' : d.t * y * d.t ∈ d.Y := h.t_conj_mem_Y hy
  have h1 := h.Lam₁_conj_mem_Y hKU hf hm' hy'
  have h2 := h.t_conj_mem_Y h1
  have htt := h.t_mul_t
  have hinv : (d.t * m * d.t)⁻¹ = d.t * m⁻¹ * d.t := by
    rw [mul_inv_rev, mul_inv_rev, h.t_inv]
    group
  have e : m * y * m⁻¹ =
      d.t * ((d.t * m * d.t) * (d.t * y * d.t) * (d.t * m * d.t)⁻¹) * d.t := by
    rw [hinv]
    calc m * y * m⁻¹ = (d.t * d.t) * m * (d.t * d.t) * y * (d.t * d.t) * m⁻¹ * (d.t * d.t) := by
          rw [htt]; group
      _ = d.t * ((d.t * m * d.t) * (d.t * y * d.t) * (d.t * m⁻¹ * d.t)) * d.t := by group
  rw [e]
  exact h2

end Normalizing

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
