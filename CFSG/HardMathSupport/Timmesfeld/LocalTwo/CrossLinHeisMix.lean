module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisCalc
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisBeta

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis

open Module CFSG.RankThree.PartOne.KCLinPlane

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable {p : ℕ} [NeZero p] {f : ZMod p → Module.End K V} {t ti : Module.End K V} {c₀ : K}

namespace HeisData

variable (H : HeisData p f t ti c₀)

include H

theorem f_betaOp {y : V} (hy : f 0 y = y) (ξ : Module.Dual K V) (m : ZMod p)
    (v : V) : f m (betaOp p t ti y ξ v) = ξ ((ti ^ m.val) v) • (t ^ m.val) y := by
  rw [betaOp_apply, map_sum]
  simp only [map_smul]
  have hb : ∀ k : ℕ, f ((0 : ZMod p) + k) ((t ^ k) y) = (t ^ k) y :=
    fun k => tpow_apply_block H k hy
  rw [sum_range_single (fun k => ξ ((ti ^ k) v) • f m ((t ^ k) y)) m]
  · have := hb m.val
    rw [zero_add, ZMod.natCast_zmod_val] at this
    rw [this]
  · intro k hk hkm
    have := hb k
    rw [zero_add] at this
    rw [f_apply_self_of_mem H this m (Ne.symm hkm), smul_zero]

theorem betaOp_f {y : V} {ξ : Module.Dual K V} {c : ZMod p} (hξ : ∀ v, ξ (f c v) = ξ v)
    (m : ZMod p) (v : V) :
    betaOp p t ti y ξ (f m v) = ξ ((ti ^ (m - c).val) v) • (t ^ (m - c).val) y := by
  rw [betaOp_apply]
  have hk' : ∀ k : ℕ, ξ ((ti ^ k) (f m v)) = ξ (f (m - k) ((ti ^ k) v)) := fun k => by
    have := congrArg (fun g : Module.End K V => g v) (H.tipow_f k m)
    simp only [Module.End.mul_apply] at this
    rw [this]
  rw [sum_range_single (fun k => ξ ((ti ^ k) (f m v)) • (t ^ k) y) (m - c)]
  · simp only [hk']
    have hmc : m - ((m - c).val : ZMod p) = c := by rw [ZMod.natCast_zmod_val]; ring
    rw [hmc, hξ]
  · intro k hk hkm
    beta_reduce
    rw [hk', dual_apply_of_ne H hξ ?_, zero_smul]
    intro h
    apply hkm
    rw [← h]
    ring

theorem betaOp_sq [Nontrivial V] {y : V} (hy : f 0 y = y) {ξ : Module.Dual K V} {c : ZMod p}
    (hξ : ∀ v, ξ (f c v) = ξ v) (hξz : ξ ((t ^ c.val) y) = 0) (v : V) :
    betaOp p t ti y ξ (betaOp p t ti y ξ v) = 0 := by
  rw [betaOp_apply (v := betaOp p t ti y ξ v)]
  refine Finset.sum_eq_zero fun k hk => ?_
  have : ξ ((ti ^ k) (betaOp p t ti y ξ v)) = 0 := by
    rw [betaOp_apply, map_sum, map_sum]
    refine Finset.sum_eq_zero fun l hl => ?_
    rw [map_smul, map_smul,
      dual_ti_t_eq_zero H hy hξ hξz (Finset.mem_range.1 hk) (Finset.mem_range.1 hl), smul_zero]
  rw [this, zero_smul]

end HeisData

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis
