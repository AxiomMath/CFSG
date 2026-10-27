module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaQFData
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaQFSetting
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaQ416

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaQ
open scoped commutatorElement

variable {G : Type*} [Group G]

namespace Hyp

variable [Finite G] {d : Data G} (h : Hyp d) {φ : G} (hF : HypF d φ)
include h hF

omit [Finite G] in
theorem φ_xs (k : Fin 4) : φ * d.xs k * φ⁻¹ = d.xs (frobIdx k) := by
  fin_cases k
  · simp [Data.xs, frobIdx]
  · simpa [Data.xs, frobIdx] using hF.φ_u₁
  · simpa [Data.xs, frobIdx] using hF.φ_u₂
  · show φ * (d.u₁ * d.u₂) * φ⁻¹ = d.u₂
    calc φ * (d.u₁ * d.u₂) * φ⁻¹ = (φ * d.u₁ * φ⁻¹) * (φ * d.u₂ * φ⁻¹) := by group
      _ = d.u₂ := by rw [hF.φ_u₁, hF.φ_u₂, ← mul_assoc, h.u₁_sq, one_mul]

omit h in
theorem φ_mem_X₄ : φ ∈ d.X₄ :=
  mem_normalizer_sup hF.φ_norm_A₄ (mem_normalizer_zpowers hF.φ_comm_t)

theorem φ_mem_normalizer_D₄ : φ ∈ normalizer (d.D₄ : Set G) :=
  h.X₄_le_normalizer_D₄ (φ_mem_X₄ hF)

omit [Finite G] in
theorem φ_basG_lo (d₀ : G) (k : Fin 4) :
    φ * d.basG d₀ ⟨k, by omega⟩ * φ⁻¹ = d.basG d₀ ⟨frobIdx k, by omega⟩ := by
  rw [Data.basG_lo d₀ _ (by simp), Data.basG_lo d₀ _ (by simp), conj_mul_conj,
    show φ * d.xs ⟨(k : ℕ) % 4, Nat.mod_lt _ (by norm_num)⟩ =
      d.xs (frobIdx k) * φ by
        rw [show (⟨(k : ℕ) % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) = k from
          Fin.ext (Nat.mod_eq_of_lt k.2), ← h.φ_xs hF k]; group]
  rw [show (⟨((⟨frobIdx k, by omega⟩ : Fin 8) : ℕ) % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) =
    frobIdx k from Fin.ext (by simp)]
  calc d.xs (frobIdx k) * φ * d.a₀ * (d.xs (frobIdx k) * φ)⁻¹
      = d.xs (frobIdx k) * (φ * d.a₀ * φ⁻¹) * (d.xs (frobIdx k))⁻¹ := by group
    _ = d.xs (frobIdx k) * d.a₀ * (d.xs (frobIdx k))⁻¹ := by rw [hF.φ_a₀]

variable (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1) {d₀ : G} (hd₀ : d₀ ∈ d.D₄)
  (hθ : d₀⁻¹ * d.t * d₀ * d.t = d.a₀)
include hB hV hd₀ hθ

theorem exists_twist : ∃ l : Fin 4 → ZMod 2, φ * d₀ * φ⁻¹ = d₀ * h.kap hd₀ (lo l) := by
  have hφd : φ * d₀ * φ⁻¹ ∈ d.D₄ := (mem_normalizer_iff.mp (h.φ_mem_normalizer_D₄ hF) d₀).mp hd₀
  have hθφ : (φ * d₀ * φ⁻¹)⁻¹ * d.t * (φ * d₀ * φ⁻¹) * d.t = d.a₀ := by
    have := theta_conj_of_comm (d := d) (y := d₀) hF.φ_comm_t
    simp only [Data.theta] at this
    rw [this, hθ, hF.φ_a₀]
  have hA := h.eq_mul_of_crossed_eq hd₀ hφd (by rw [hθ, hθφ])
  obtain ⟨l, hl⟩ := h.exists_lo hd₀ hB hV hA
  exact ⟨l, by rw [hl]; group⟩

omit hθ in
theorem φ_basG_hi {l : Fin 4 → ZMod 2} (hl : φ * d₀ * φ⁻¹ = d₀ * h.kap hd₀ (lo l)) (k : Fin 4) :
    φ * d.basG d₀ ⟨k + 4, by omega⟩ * φ⁻¹ =
      h.kap hd₀ (Pi.single ⟨frobIdx k + 4, by omega⟩ 1 + (mX (frobIdx k)).mulVec (lo l)) := by
  rw [h.kap_add hd₀ hB hV, h.kap_single, ← h.conj_xs_kap hd₀ hB hV,
    Data.basG_hi d₀ _ (by simp), Data.basG_hi d₀ _ (by simp)]
  rw [show (⟨((⟨(k : ℕ) + 4, by omega⟩ : Fin 8) : ℕ) % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) =
    k from Fin.ext (by simp),
    show (⟨((⟨(frobIdx k : ℕ) + 4, by omega⟩ : Fin 8) : ℕ) % 4, Nat.mod_lt _ (by norm_num)⟩ :
      Fin 4) = frobIdx k from Fin.ext (by simp)]
  calc φ * (d.xs k * d₀ * (d.xs k)⁻¹) * φ⁻¹
      = (φ * d.xs k * φ⁻¹) * (φ * d₀ * φ⁻¹) * (φ * d.xs k * φ⁻¹)⁻¹ := by group
    _ = d.xs (frobIdx k) * d₀ * (d.xs (frobIdx k))⁻¹ *
        (d.xs (frobIdx k) * h.kap hd₀ (lo l) * (d.xs (frobIdx k))⁻¹) := by
        rw [h.φ_xs hF k, hl]; group

omit hθ in
theorem conj_φ_kap {l : Fin 4 → ZMod 2} (hl : φ * d₀ * φ⁻¹ = d₀ * h.kap hd₀ (lo l))
    (v : Fin 8 → ZMod 2) : φ * h.kap hd₀ v * φ⁻¹ = h.kap hd₀ ((mPhi l).mulVec v) := by
  refine kprod_conj (h.bas_sq hd₀ hB hV) (h.φ_mem_normalizer_D₄ hF) (mPhi l) (fun j => ?_) v
  have hlo : ∀ k : Fin 4, φ * d.basG d₀ ⟨k, by omega⟩ * φ⁻¹ =
      h.kap hd₀ (fun i => mPhi l i ⟨k, by omega⟩) := fun k => by
    rw [col_mPhi_lo, h.kap_single]; exact h.φ_basG_lo hF d₀ k
  have hhi : ∀ k : Fin 4, φ * d.basG d₀ ⟨k + 4, by omega⟩ * φ⁻¹ =
      h.kap hd₀ (fun i => mPhi l i ⟨k + 4, by omega⟩) := fun k => by
    rw [col_mPhi_hi]; exact h.φ_basG_hi hF hB hV hd₀ hl k
  fin_cases j
  · exact hlo 0
  · exact hlo 1
  · exact hlo 2
  · exact hlo 3
  · exact hhi 0
  · exact hhi 1
  · exact hhi 2
  · exact hhi 3

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaD
