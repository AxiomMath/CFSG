module

public import CFSG.LocalAnalysis.EvenSmallLie.OddTranspAlt.Setup
public import CFSG.LocalAnalysis.EvenSmallLie.OddTranspAlt.PermSwap
public import CFSG.LocalAnalysis.ZStar

public section

namespace CFSG.EvenSmallLie.OddTranspAlt

open Equiv Equiv.Perm CFSG.Open

namespace Cfg

variable {G : Type} [Group G] [Finite G] {n : ℕ} (c : Cfg G n)

theorem Dt_nonempty : c.Dt.Nonempty := by
  by_contra hne
  have hiso : ∀ g : G, g * c.t * g⁻¹ * c.t = c.t * (g * c.t * g⁻¹) → g * c.t * g⁻¹ = c.t :=
    fun g hg => by_contra fun h => hne ⟨_, ⟨g, rfl⟩, h, hg.symm⟩
  have ht2 : c.t * c.t = 1 := c.mul_self_of_mem_cls c.t_mem_cls
  have ht1 : c.t ≠ 1 := fun h => by simpa [h] using c.ht
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨M, hMn, hModd, hM⟩ := ZStar.glauberman_zStar G c.t ht1 ht2 hiso
  have hq : ∀ x ∈ cls c.t, (x : G ⧸ M) = (c.t : G ⧸ M) := by
    rintro x ⟨e, rfl⟩
    exact QuotientGroup.eq_iff_div_mem.2 (by rw [div_eq_mul_inv]; exact hM e)
  have hq2 : (c.t : G ⧸ M) * (c.t : G ⧸ M) = 1 := by
    rw [← QuotientGroup.mk_mul, ht2, QuotientGroup.mk_one]
  have key : ∀ y ∈ Subgroup.closure (cls c.t), (y : G ⧸ M) = 1 ∨ (y : G ⧸ M) = (c.t : G ⧸ M) := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx => exact Or.inr (hq x hx)
    | one => exact Or.inl (QuotientGroup.mk_one M)
    | mul a b _ _ ha hb =>
      rw [QuotientGroup.mk_mul]
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb, hq2]
    | inv a _ ha =>
      rw [QuotientGroup.mk_inv]
      rcases ha with ha | ha <;> simp [ha, inv_eq_of_mul_eq_one_right hq2]
  obtain ⟨u, hu, hu4⟩ := exists_alt_orderOf_four (n := n) (by have := c.hn; omega)
  obtain ⟨y, hy, rfl⟩ := c.exists_ι_eq hu
  rw [c.orderOf_ι hy] at hu4
  have hyM : y * y ∈ M := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
    rcases key y (c.hYle hy) with h | h <;> simp [h, hq2]
  have hy2 : orderOf (y * y) = 2 := by
    refine orderOf_eq_prime ?_ fun h => ?_
    · rw [← pow_two, ← pow_mul]
      exact (hu4 ▸ pow_orderOf_eq_one y : y ^ 4 = 1)
    · have := orderOf_dvd_of_pow_eq_one (pow_two y ▸ h)
      rw [hu4] at this
      omega
  exact hModd.not_two_dvd_nat (hy2 ▸ M.orderOf_dvd_natCard hyM)

end Cfg

end CFSG.EvenSmallLie.OddTranspAlt
