module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3M1Five

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem Hyp.exists_V₁_cr_eq (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {u : G}
    (hu : u ∈ d.U₁) : ∃ v ∈ d.V₁, v⁻¹ * d.t * v * d.t = u := by
  rw [hd.U₁_eq_map, mem_map_conj_s] at hu
  obtain ⟨c, hc, hca⟩ := hd.exists_F_I₄_cr_eq hGMS hu
  refine ⟨d.s * c * d.s, ?_, ?_⟩
  · rw [V₁, mem_map_conj_s, d.s_conj_s_conj]
    exact hc
  · have e := d.cr_conj (c := d.s) (x := c) hd.s_mem_centralizer_t
    rw [d.s_inv] at e
    rw [e, hca, d.s_conj_s_conj]

theorem Hyp.cr_V₁_inv (hd : d.Hyp) {z : G} (hz : z ∈ d.V₁) :
    z⁻¹⁻¹ * d.t * z⁻¹ * d.t = (z⁻¹ * d.t * z * d.t)⁻¹ := by
  have e := hd.cr_V₁_mul (inv_mem hz) hz
  rw [inv_mul_cancel, show (1 : G)⁻¹ * d.t * 1 * d.t = 1 by simp [hd.t_mul_t]] at e
  exact eq_inv_of_mul_eq_one_left e.symm

theorem Hyp.V₁_le_of_le (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {X : Subgroup G} (hUX : d.U₁ ≤ X) (hDX : d.D₁ ≤ X)
    (hVX : d.V₁ ≤ normalizer (X : Set G)) : d.V₁ ≤ X := by
  have := h.charP
  intro w hw
  obtain ⟨ω, hω⟩ := exists_unit_generator h
  have hω2 : (ω : K) ^ 2 + 1 ≠ 0 := by
    intro e
    have e1 : (ω : K) ^ 2 = 1 := by
      linear_combination e - (CharTwo.two_eq_zero : (2 : K) = 0)
    have e2 : ω ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, e1, Units.val_one])
    have hd2 := orderOf_dvd_of_pow_eq_one e2
    rw [hω] at hd2
    have h4 := hd.four_le
    have h16 : 16 ≤ (2 ^ f) ^ 2 := by nlinarith
    have := Nat.le_of_dvd (by norm_num) hd2
    omega
  obtain ⟨b, hb⟩ := exists_eq_η_uSU (hd.cr_V₁_mem hw)
  set a : K := b / ((ω : K) ^ 2 + 1) with ha
  obtain ⟨v, hv, hva⟩ := hd.exists_V₁_cr_eq hGMS (d.η_uSU_mem a)
  set x := d.η (dHom h ω) with hx
  have hxD : x ∈ d.D₁ := d.η_dHom_mem ω
  have hxv : x * v * x⁻¹ ∈ d.V₁ :=
    (mem_normalizer_iff.1 (hd.D₁_le_normalizer_V₁ hGMS hxD) v).1 hv
  set c := x * v * x⁻¹ * v⁻¹ with hc
  have hcX : c ∈ X := by
    rw [hc, show x * v * x⁻¹ * v⁻¹ = x * (v * x⁻¹ * v⁻¹) by group]
    exact mul_mem (hDX hxD) ((mem_normalizer_iff.1 (hVX hv) _).1 (inv_mem (hDX hxD)))
  have hcV : c ∈ d.V₁ := mul_mem hxv (inv_mem hv)
  have hcr : c⁻¹ * d.t * c * d.t = w⁻¹ * d.t * w * d.t := by
    rw [hc, hd.cr_V₁_mul hxv (inv_mem hv), d.cr_conj (hd.D₁_le_centralizer_t hxD),
      hd.cr_V₁_inv hv, hva, hx, d.η_dHom_conj, ← map_inv, ← map_mul,
      (show (uSU h a)⁻¹ = uSU h a from inv_eq_of_mul_eq_one_right
        (mul_self_of_mem_patSub_I₁ (uSU_mem_patSub a))), ← uSU_add, hb]
    congr 2
    rw [ha]
    field_simp
  have hU : c⁻¹ * w ∈ d.U₁ := by
    rw [← hd.V₁_inf_centralizer_t hGMS]
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hcV) hw, ?_⟩
    rw [← hd.cr_eq_one_iff', hd.cr_V₁_mul (inv_mem hcV) hw, hd.cr_V₁_inv hcV, hcr,
      inv_mul_cancel]
  rw [show w = c * (c⁻¹ * w) by group]
  exact mul_mem hcX (hUX hU)

theorem Hyp.V₁_le_M₁ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.V₁ ≤ d.M₁ := by
  have hNM : d.N₁ ≤ d.M₁ := by
    intro n hn
    exact ⟨⟨n, d.N₁_le_centralizer_I₁ hn⟩, subset_normalClosure (mem_subgroupOf.2 hn), rfl⟩
  refine hd.V₁_le_of_le hGMS (d.U₁_le_N₁.trans hNM) (d.D₁_le_N₁.trans hNM) fun v hv => ?_
  refine mem_normalizer_fintype fun m hm => ?_
  obtain ⟨y, hy, rfl⟩ := hm
  have hvH : v ∈ centralizer (d.I₁ : Set G) := d.V₁_le_centralizer_I₁ hv
  refine ⟨⟨v, hvH⟩ * y * ⟨v, hvH⟩⁻¹,
    (normalClosure_normal (s := ((d.N₁.subgroupOf (centralizer (d.I₁ : Set G)) :
      Subgroup (centralizer (d.I₁ : Set G))) : Set (centralizer (d.I₁ : Set G))))).conj_mem y hy
      ⟨v, hvH⟩, ?_⟩
  simp

end Data

end CFSG.LocalAnalysis.EvenBN.U5
