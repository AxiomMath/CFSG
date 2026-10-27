module

public import CFSG.GH74.Uniqueness.SU.SU13TA9PermD
public import CFSG.GH74.Uniqueness.SU.SU13TA9M

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L9

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA

variable {H : Type} [Group H] {π : H →* alternatingGroup (Fin 9)}

@[expose] def DE (π : H →* alternatingGroup (Fin 9)) (E : Subgroup H) : Subgroup H := E ⊓ Fh π

theorem DE_le_E {E : Subgroup H} : DE π E ≤ E := inf_le_left

theorem DE_le_Fh {E : Subgroup H} : DE π E ≤ Fh π := inf_le_right

namespace IsE

variable {E : Subgroup H}

theorem mem_DE_iff (hπ : TwoCover π) (hE : IsE π E) {y : H} (hy : Odd (orderOf y)) :
    y ∈ DE π E ↔ π y ∈ Dbar := by
  rw [DE, Subgroup.mem_inf, hE.mem_iff hπ hy, mem_Fh]
  rfl

theorem map_DE (hE : IsE π E) : (DE π E).map π = Dbar := by
  refine le_antisymm ?_ (fun x hx => ?_)
  · rintro _ ⟨y, ⟨hyE, hyF⟩, rfl⟩
    exact ⟨hE.map_mem hyE, mem_Fh.mp hyF⟩
  · have hx' : x ∈ E.map π := hE.2 ▸ hx.1
    obtain ⟨y, hyE, rfl⟩ := hx'
    exact ⟨y, ⟨hyE, mem_Fh.mpr hx.2⟩, rfl⟩

theorem card_DE (hπ : TwoCover π) (hE : IsE π E) : Nat.card (DE π E) = 9 := by
  have hD3 : IsPGroup 3 (DE π E) := hE.1.to_le DE_le_E
  rw [← hπ.card_map_of_isPGroup_three hD3, hE.map_DE, card_Dbar]

theorem exists_eq_zpow_mul_DE (hπ : TwoCover π) (c : Cfg π) (hE : IsE π E) {g : H} (hg : g ∈ E) :
    ∃ i : ℤ, ∃ d ∈ DE π E, g = c.s₁ ^ i * d := by
  obtain ⟨i, j, k, hk⟩ := mem_Ebar_iff_toE.mp (hE.map_mem hg)
  refine ⟨(k : ℕ), c.s₁ ^ (-((k : ℕ) : ℤ)) * g, ?_, by group⟩
  have hs₁ : c.s₁ ∈ E := hE.s₁_mem hπ c
  have hdE : c.s₁ ^ (-((k : ℕ) : ℤ)) * g ∈ E :=
    Subgroup.mul_mem _ (Subgroup.zpow_mem _ hs₁ _) hg
  have hπd : π (c.s₁ ^ (-((k : ℕ) : ℤ)) * g) = toE i j 0 := by
    rw [map_mul, map_zpow, c.π_s₁, hk]
    refine Subtype.ext ?_
    have := pc_inv_mul_toP i j k
    simpa [toE, Subgroup.coe_mul, coe_ec, zpow_neg, zpow_natCast] using this
  have hodd : Odd (orderOf (c.s₁ ^ (-((k : ℕ) : ℤ)) * g)) := hE.odd_orderOf hdE
  rw [hE.mem_DE_iff hπ hodd, hπd]
  exact toE_mem_Dbar i j

end IsE

theorem r_sq_sq (hπ : TwoCover π) {r : H} (hr : π r = er) {z : H} (hz : z ∈ π.ker) (hz1 : z ≠ 1) :
    (r ^ 2) ^ 2 = z := by
  obtain ⟨hk, h1⟩ := hπ.sq_mem_ker_ne_one_of_cycleType_two_two (by norm_num) (x := r ^ 2)
    (by rw [map_pow, hr]; exact cycleType_er_sq)
  exact hπ.eq_of_mem_ker_ne_one' hk hz h1 hz1

theorem pow_four_r (hπ : TwoCover π) {r : H} (hr : π r = er) {z : H} (hz : z ∈ π.ker)
    (hz1 : z ≠ 1) : r ^ 4 = z := by
  rw [show 4 = 2 * 2 from rfl, pow_mul]
  exact r_sq_sq hπ hr hz hz1

theorem orderOf_r (hπ : TwoCover π) {r : H} (hr : π r = er) {z : H} (hz : z ∈ π.ker)
    (hz1 : z ≠ 1) : orderOf r = 8 := by
  have hz2 : z ^ 2 = 1 := hπ.sq_eq_one_of_mem_ker' hz
  have h4 := pow_four_r hπ hr hz hz1
  have h8 : r ^ (2 ^ (2 + 1)) = 1 := by
    rw [show 2 ^ (2 + 1) = 4 * 2 by norm_num, pow_mul, h4, hz2]
  have hn4 : ¬ r ^ (2 ^ 2) = 1 := fun h => hz1 (by rw [← h4]; simpa using h)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := orderOf_eq_prime_pow hn4 h8
  simpa using this

theorem r_mem_Fh {r : H} (hr : π r = er) : r ∈ Fh π := by
  rw [mem_Fh, hr]
  exact er_mem_AS

theorem r_conj_mem_DE {E : Subgroup H} (hπ : TwoCover π) (hE : IsE π E) {r : H} (hr : π r = er)
    {d : H} (hd : d ∈ DE π E) : r * d * r⁻¹ ∈ DE π E := by
  have hodd : Odd (orderOf (r * d * r⁻¹)) := by
    rw [← SemiconjBy.orderOf_eq r (show r * d = r * d * r⁻¹ * r by group)]
    exact hE.odd_orderOf hd.1
  rw [hE.mem_DE_iff hπ hodd, map_mul, map_mul, map_inv, hr]
  exact er_conj_mem_Dbar ((hE.mem_DE_iff hπ (hE.odd_orderOf hd.1)).mp hd)

theorem t_conj_mem_DE {E : Subgroup H} (hπ : TwoCover π) (c : Cfg π) (hE : IsE π E) {d : H}
    (hd : d ∈ DE π E) : c.t * d * c.t⁻¹ ∈ DE π E := by
  have hodd : Odd (orderOf (c.t * d * c.t⁻¹)) := by
    rw [← SemiconjBy.orderOf_eq c.t (show c.t * d = c.t * d * c.t⁻¹ * c.t by group)]
    exact hE.odd_orderOf hd.1
  rw [hE.mem_DE_iff hπ hodd, map_mul, map_mul, map_inv, c.π_t]
  exact et_conj_mem_Dbar ((hE.mem_DE_iff hπ (hE.odd_orderOf hd.1)).mp hd)

theorem t_r_mem_zpowers (hπ : TwoCover π) (c : Cfg π) {r : H} (hr : π r = er) {z : H}
    (hz : z ∈ π.ker) (hz1 : z ≠ 1) : c.t * r * c.t⁻¹ ∈ zpowers r := by
  have hk : (c.t * r * c.t⁻¹) * r ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, c.π_t, hr, et_mul_er]
    group
  have h4 := pow_four_r hπ hr hz hz1
  have hcases : (c.t * r * c.t⁻¹) * r = 1 ∨ (c.t * r * c.t⁻¹) * r = z := by
    by_cases h1 : (c.t * r * c.t⁻¹) * r = 1
    · exact Or.inl h1
    · exact Or.inr (hπ.eq_of_mem_ker_ne_one' hk hz h1 hz1)
  rcases hcases with h | h
  · have : c.t * r * c.t⁻¹ = r⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers r)
  · have : c.t * r * c.t⁻¹ = r ^ 3 := by
      calc c.t * r * c.t⁻¹ = ((c.t * r * c.t⁻¹) * r) * r⁻¹ := by group
        _ = r ^ 4 * r⁻¹ := by rw [h, h4]
        _ = r ^ 3 := by group
    rw [this]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers r) 3

theorem t_r_ne (c : Cfg π) {r : H} (hr : π r = er) : c.t * r * c.t⁻¹ ≠ r := fun h => by
  have h1 : et * er * et⁻¹ = er := by
    have := congrArg π h
    rwa [map_mul, map_mul, map_inv, c.π_t, hr] at this
  rw [et_mul_er] at h1
  have h2 : er ^ 2 = 1 := by
    calc er ^ 2 = er * er := pow_two er
      _ = er⁻¹ * er := by rw [h1]
      _ = 1 := inv_mul_cancel er
  exact er_sq_ne_one h2

end CFSG.GH74.Uniqueness.SU.SU13.TA.L9
