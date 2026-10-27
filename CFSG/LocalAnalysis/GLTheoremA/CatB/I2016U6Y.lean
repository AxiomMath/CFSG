module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnU6b

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2016U6

open CFSG.Fischer CFSG.LocalAnalysis.GLTheoremA.LevelLieU6 CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnU6
open scoped commutatorElement

variable {D : GL (Fin 6) F4} {d : Fin 6 → F4}
  (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d) (c : F4)

theorem Rc_normal_CenD {x : M6} (hx : x ∈ CenD D) {r : M6} (hr : r ∈ Rc hD c) :
    x * r * x⁻¹ ∈ Rc hD c := by
  obtain ⟨hr1, hrC, hrb⟩ := (mem_Rc hD c).1 hr
  have hxC : x * r * x⁻¹ ∈ CenD D := mul_mem (mul_mem hx hrC) (inv_mem hx)
  rw [mem_Rc]
  refine ⟨?_, hxC, ?_⟩
  · rw [mem_K1]
    refine ⟨hxC, fun c' => ?_⟩
    have hr' : (blkM d c' (mM6 r)).det = 1 := ((mem_K1 hD).1 hr1).2 c'
    have hbr : blkDet hD c' ⟨r, hrC⟩ = 1 := Units.ext (by rw [blkDet_val]; exact hr')
    have h1 := blkDet_val hD c' ⟨x * r * x⁻¹, hxC⟩
    have h2 : (⟨x * r * x⁻¹, hxC⟩ : ↥(CenD D)) = ⟨x, hx⟩ * ⟨r, hrC⟩ * ⟨x, hx⟩⁻¹ := rfl
    rw [← h1, h2, map_mul, map_mul, map_inv, hbr, mul_one, mul_inv_cancel]
    rfl
  · have hrb' : blkHom hD c ⟨r, hrC⟩ = 1 := Units.ext (by rw [blkHom_val]; simpa using hrb)
    have h1 : blkHom hD c ⟨x * r * x⁻¹, hxC⟩ = 1 := by
      have : (⟨x * r * x⁻¹, hxC⟩ : ↥(CenD D)) = ⟨x, hx⟩ * ⟨r, hrC⟩ * ⟨x, hx⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hrb', mul_one, mul_inv_cancel]
    have h2 := congrArg Units.val h1
    rw [blkHom_val] at h2
    simpa using h2

theorem card_Rc (c₂ : F4) (hne : c ≠ c₂) (hcover : ∀ i : Fin 6, d i = c ∨ d i = c₂)
    (h2 : Fintype.card (Blk d c₂) = 2) : Nat.card (Rc hD c) = 6 := by
  rw [Rc_eq_range hD c c₂ hne hcover]
  rw [← Nat.card_congr (MonoidHom.ofInjective (embSU_injective d c₂)).toEquiv]
  exact card_statedSU_six _ h2

theorem comm_Rc_of_perfect (hsmall : ∀ c' : F4, c' ≠ c → Fintype.card (Blk d c') ≤ 3)
    {L : Subgroup M6} (hLC : L ≤ CenD D) (hperf : ⁅L, L⁆ = L) :
    ∀ l ∈ L, ∀ y ∈ Rc hD c, l * y = y * l := by
  intro l hl y hy
  obtain ⟨A, hA⟩ := le_range_embSU d c hD hsmall hLC hperf hl
  obtain ⟨_, hyC, hyb⟩ := (mem_Rc hD c).1 hy
  rw [← hA]
  exact embSU_comm_of_blk_one d c hD A hyC hyb

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2016U6

end
