module

public import CFSG.LocalAnalysis.EvenSmallLie.OddTranspAlt.Setup
public import CFSG.LocalAnalysis.EvenSmallLie.OddTranspAlt.PermSwap
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock

public section

namespace CFSG.EvenSmallLie.OddTranspAlt

open Equiv Equiv.Perm CFSG.Open

namespace Cfg

variable {G : Type} [Group G] [Finite G] {n : ℕ} (c : Cfg G n)

theorem comp_eq_or_commute {d : G} (hd : d ∈ Subgroup.centralizer ({c.t} : Set G)) :
    c.Y.map (MulAut.conj d).toMonoidHom = c.Y ∨
      ⁅c.Y.map (MulAut.conj d).toMonoidHom, c.Y⁆ = ⊥ := by
  have hY := (ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 c.hY
  have hdt : d * c.t * d⁻¹ = c.t := by
    rw [← Subgroup.mem_centralizer_iff.1 hd c.t rfl, mul_inv_cancel_right]
  have hC := LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton d c.t
  rw [hdt] at hC
  have hYd := LocalAnalysis.ComponentInitial.isComponentOf_map_conj hY d
  rw [hC] at hYd
  exact LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hYd hY

theorem Dt_subset_N {x : G} (hx : x ∈ c.Dt) : x ∈ c.N := by
  obtain ⟨hxD, -, hxt⟩ := hx
  have hxC : x ∈ Subgroup.centralizer ({c.t} : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff.1 hh]; exact hxt
  rcases c.comp_eq_or_commute hxC with h | h
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.2 h
  exfalso
  have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
  have hmem : ∀ w ∈ c.Y, x * w * x⁻¹ ∈ c.Y.map (MulAut.conj x).toMonoidHom :=
    fun w hw => ⟨w, hw, rfl⟩
  obtain ⟨u, hu, hu4⟩ := exists_alt_orderOf_four (n := n) (by have := c.hn; omega)
  obtain ⟨y, hy, rfl⟩ := c.exists_ι_eq hu
  rw [c.orderOf_ι hy] at hu4
  have hcomm : Commute (x * y * x⁻¹) y⁻¹ :=
    Commute.inv_right (Subgroup.mem_centralizer_iff.1 (hcen (hmem y hy)) y hy).symm
  have heq : x * (y * x * y⁻¹) = x * y * x⁻¹ * y⁻¹ := by
    rw [c.inv_of_mem_cls hxD]; simp only [mul_assoc]
  have hy4 : y ^ 4 = 1 := hu4 ▸ pow_orderOf_eq_one y
  have hz4 : (x * y * x⁻¹ * y⁻¹) ^ 4 = 1 := by
    rw [hcomm.mul_pow, conj_pow, inv_pow, hy4]; group
  have hz2 : ¬ (x * y * x⁻¹ * y⁻¹) ^ 2 = 1 := by
    intro h2
    rw [hcomm.mul_pow, conj_pow, inv_pow, mul_inv_eq_one] at h2
    have hy2 : y ^ 2 ∈ c.Y := c.Y.pow_mem hy 2
    have hc2 : y ^ 2 ∈ Subgroup.centralizer (c.Y : Set G) := hcen (by rw [← h2]; exact hmem _ hy2)
    have h1 : y ^ 2 = 1 :=
      c.Y_center _ hy2 fun w hw => (Subgroup.mem_centralizer_iff.1 hc2 w hw).symm
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hu4] at this
    omega
  have hord : orderOf (x * y * x⁻¹ * y⁻¹) = 4 :=
    orderOf_eq_prime_pow (p := 2) (n := 1) (by rwa [pow_one]) hz4
  have hot := c.ot_cls hxD (conj_mem_cls hxD y)
  rw [heq, hord] at hot
  revert hot
  decide

end Cfg

end CFSG.EvenSmallLie.OddTranspAlt
