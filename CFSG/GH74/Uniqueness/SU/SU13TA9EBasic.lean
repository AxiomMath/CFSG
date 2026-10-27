module

public import CFSG.GH74.Uniqueness.SU.SU13TA9M

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L9

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA

variable {H : Type} [Group H] {π : H →* alternatingGroup (Fin 9)}

theorem toP_pow_three : ∀ i j k : Fin 3, toP i j k ^ 3 = 1 := by decide

theorem toP_decomp : ∀ i j k : Fin 3, toP i j k =
    pc ^ (k : ℕ) * (pa * pb) ^ ((2 * (i + j) : Fin 3) : ℕ) *
      (pa * pb⁻¹) ^ ((2 * (i - j) : Fin 3) : ℕ) := by decide

namespace IsE

variable {E : Subgroup H}

theorem pow_three (hπ : TwoCover π) (hE : IsE π E) {a : H} (ha : a ∈ E) : a ^ 3 = 1 := by
  obtain ⟨i, j, k, hk⟩ := mem_Ebar_iff_toE.mp (hE.map_mem ha)
  have h1 : (π a) ^ 3 = 1 := by
    rw [hk]
    exact Subtype.ext (by simpa [toE, Subgroup.coe_pow] using toP_pow_three i j k)
  have hk3 : a ^ 3 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, h1]
  have h2 := hπ.sq_eq_one_of_mem_ker' hk3
  have hodd : Odd (orderOf (a ^ 3)) := hE.odd_orderOf (Subgroup.pow_mem _ ha 3)
  have hdvd : orderOf (a ^ 3) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have : orderOf (a ^ 3) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.mp this

theorem t_conj_mem (hπ : TwoCover π) (c : Cfg π) (hE : IsE π E) {a : H} (ha : a ∈ E) :
    c.t * a * c.t⁻¹ ∈ E := by
  have hodd : Odd (orderOf (c.t * a * c.t⁻¹)) := by
    rw [← SemiconjBy.orderOf_eq c.t (show c.t * a = c.t * a * c.t⁻¹ * c.t by group)]
    exact hE.odd_orderOf ha
  rw [hE.mem_iff hπ hodd, map_mul, map_mul, map_inv, c.π_t]
  obtain ⟨i, j, k, hk⟩ := mem_Ebar_iff_toE.mp (hE.map_mem ha)
  rw [hk]
  have : et * toE i j k * et⁻¹ = toE j i (-k) := Subtype.ext (by
    simpa [toE, coe_et] using pt_mul_toP i j k)
  rw [this]
  exact mem_Ebar_iff_toE.mpr ⟨_, _, _, rfl⟩

theorem x_conj_mem (hπ : TwoCover π) (c : Cfg π) (hE : IsE π E) {a : H} (ha : a ∈ E) :
    c.x * a * c.x⁻¹ ∈ E := by
  have hodd : Odd (orderOf (c.x * a * c.x⁻¹)) := by
    rw [← SemiconjBy.orderOf_eq c.x (show c.x * a = c.x * a * c.x⁻¹ * c.x by group)]
    exact hE.odd_orderOf ha
  rw [hE.mem_iff hπ hodd, map_mul, map_mul, map_inv, c.π_x]
  obtain ⟨i, j, k, hk⟩ := mem_Ebar_iff_toE.mp (hE.map_mem ha)
  rw [hk]
  have : ex * toE i j k * ex⁻¹ = toE (-j) (-i) (-k) := Subtype.ext (by
    simpa [toE, coe_ex] using px_mul_toP i j k)
  rw [this]
  exact mem_Ebar_iff_toE.mpr ⟨_, _, _, rfl⟩

theorem exists_gen (hπ : TwoCover π) (c : Cfg π) (hE : IsE π E) {g : H} (hg : g ∈ E) :
    ∃ i j k : ℤ, g = c.s₁ ^ i * c.s₂ ^ j * c.s₄ ^ k := by
  obtain ⟨i, j, k, hk⟩ := mem_Ebar_iff_toE.mp (hE.map_mem hg)
  refine ⟨(k : ℕ), ((2 * (i + j) : Fin 3) : ℕ), ((2 * (i - j) : Fin 3) : ℕ), ?_⟩
  simp only [zpow_natCast]
  set w : H := c.s₁ ^ (k : ℕ) * c.s₂ ^ ((2 * (i + j) : Fin 3) : ℕ) *
    c.s₄ ^ ((2 * (i - j) : Fin 3) : ℕ) with hw
  have hwE : w ∈ E :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ (hE.s₁_mem hπ c) _)
      (Subgroup.pow_mem _ (hE.s₂_mem hπ c) _)) (Subgroup.pow_mem _ (hE.s₄_mem hπ c) _)
  have hπw : π w = π g := by
    rw [hw, map_mul, map_mul, map_pow, map_pow, map_pow, c.π_s₁, c.π_s₂, c.π_s₄, hk]
    refine Subtype.ext ?_
    have := toP_decomp i j k
    simpa [toE, Subgroup.coe_mul, Subgroup.coe_pow, coe_ea, coe_eb, coe_ec] using this.symm
  exact (hπ.eq_of_odd_orderOf_of_map_eq (hE.odd_orderOf hwE) (hE.odd_orderOf hg) hπw).symm

end IsE

end CFSG.GH74.Uniqueness.SU.SU13.TA.L9
