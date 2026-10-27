module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterRow
public import CFSG.Sporadic.SmallOddCore.Assembly

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.SmallOddCore

variable {M : Type} [Group M] {P R : Subgroup M}

structure AutRowData (P R : Subgroup M) : Prop where
  model : AutModel P R
  index : ∀ x ∈ R, x ∉ P → ∀ y ∈ R, y ∉ P → x⁻¹ * y ∈ P
  centerInv : ∀ a ∈ P, orderOf a = 2 → ∀ z ∈ P, z * z = 1 → z * a = a * z →
    (∀ y ∈ P, y * a = a * y → z * y = y * z) → z = 1 ∨ z = a
  outerLe : ∀ a ∈ P, orderOf a = 2 → ∀ w ∈ R, w ∉ P → w * w = 1 →
    ¬ ∀ y ∈ P, y * a = a * y → y * w = w * y

namespace AutRowData

variable (d : AutRowData P R)
include d

theorem core {n s : M} {E : Prop} (hn : n ∈ R) (hs : s ∈ R) (hnn : n * n = 1) (hss : s * s = 1)
    (hns : n * s = s * n) (hfix : ∀ y ∈ P, y * n = n * y → y * s = s * y)
    (hE : n ∉ P → ∀ z ∈ P, orderOf z = 2 → z * n = n * z →
      (∀ y ∈ P, y * n = n * y → y * z = z * y) → E) :
    s = 1 ∨ s = n ∨ E := by
  have hn' : n⁻¹ = n := inv_eq_of_mul_eq_one_right hnn
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  by_cases hnP : n ∈ P
  · by_cases hn1 : n = 1
    · left
      refine d.model.inj s hs fun p hp => ?_
      have := hfix p hp (by rw [hn1, mul_one, one_mul])
      exact this.symm
    · have hn2 : orderOf n = 2 := orderOf_eq_prime (by rw [pow_two]; exact hnn) hn1
      by_cases hsP : s ∈ P
      · exact (d.centerInv n hnP hn2 s hsP hss hns.symm fun y hy hyn =>
          (hfix y hy hyn).symm).imp id Or.inl
      · exact absurd (fun y hy hyn => hfix y hy hyn) (d.outerLe n hnP hn2 s hs hsP hss)
  · by_cases hsP : s ∈ P
    · by_cases hs1 : s = 1
      · exact Or.inl hs1
      · have hs2 : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hss) hs1
        exact Or.inr (Or.inr (hE hnP s hsP hs2 hns.symm fun y hy hyn => hfix y hy hyn))
    · have hρP : n⁻¹ * s ∈ P := d.index n hn hnP s hs hsP
      rw [hn'] at hρP
      by_cases hρ1' : n * s = 1
      · right; left
        calc s = n⁻¹ * (n * s) := by group
          _ = n := by rw [hρ1', mul_one, hn']
      have hρ1 : n * s ≠ 1 := hρ1'
      have hρρ : (n * s) * (n * s) = 1 := by
        calc (n * s) * (n * s) = n * (s * n) * s := by group
          _ = n * (n * s) * s := by rw [hns]
          _ = (n * n) * (s * s) := by group
          _ = 1 := by rw [hnn, hss, mul_one]
      have hρ2 : orderOf (n * s) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hρρ) hρ1
      refine Or.inr (Or.inr (hE hnP (n * s) hρP hρ2 ?_ fun y hy hyn => ?_))
      · calc n * s * n = n * (s * n) := by group
          _ = n * (n * s) := by rw [hns]
      · have hys := hfix y hy hyn
        calc y * (n * s) = (y * n) * s := by group
          _ = (n * y) * s := by rw [hyn]
          _ = n * (y * s) := by group
          _ = n * (s * y) := by rw [hys]
          _ = (n * s) * y := by group

theorem autCenterCondExc {Exc : MulAut ↥P → Prop}
    (houter : ∀ (α : MulAut ↥P) (w : M), w ∈ R → w ∉ P →
      (∀ p : P, ((α p : P) : M) = w * p * w⁻¹) → w * w = 1 → ∀ z ∈ P, orderOf z = 2 →
      z * w = w * z → (∀ y ∈ P, y * w = w * y → y * z = z * y) → Exc α) :
    AutCenterCondExc ↥P Exc := by
  intro ν σ hν hσ hνσ hfix
  have h := d.model
  have hn := h.elt_mem ν
  have hs := h.elt_mem σ
  have hsp := h.elt_spec σ
  have hnp := h.elt_spec ν
  have hnn : h.elt ν * h.elt ν = 1 := by
    refine h.eq_of_conj (R.mul_mem hn hn) R.one_mem fun p hp => ?_
    have e := congrArg (fun α : MulAut P => ((α ⟨p, hp⟩ : P) : M)) hν
    simp only [MulAut.mul_apply, MulAut.one_apply] at e
    rw [hnp, hnp] at e
    calc h.elt ν * h.elt ν * p * (h.elt ν * h.elt ν)⁻¹ =
        h.elt ν * (h.elt ν * p * (h.elt ν)⁻¹) * (h.elt ν)⁻¹ := by group
      _ = p := e
      _ = 1 * p * 1⁻¹ := by group
  have hss : h.elt σ * h.elt σ = 1 := by
    refine h.eq_of_conj (R.mul_mem hs hs) R.one_mem fun p hp => ?_
    have e := congrArg (fun α : MulAut P => ((α ⟨p, hp⟩ : P) : M)) hσ
    simp only [MulAut.mul_apply, MulAut.one_apply] at e
    rw [hsp, hsp] at e
    calc h.elt σ * h.elt σ * p * (h.elt σ * h.elt σ)⁻¹ =
        h.elt σ * (h.elt σ * p * (h.elt σ)⁻¹) * (h.elt σ)⁻¹ := by group
      _ = p := e
      _ = 1 * p * 1⁻¹ := by group
  have hns : h.elt ν * h.elt σ = h.elt σ * h.elt ν := by
    refine h.eq_of_conj (R.mul_mem hn hs) (R.mul_mem hs hn) fun p hp => ?_
    have e := congrArg (fun α : MulAut P => ((α ⟨p, hp⟩ : P) : M)) hνσ
    simp only [MulAut.mul_apply] at e
    rw [hnp, hsp, hsp, hnp] at e
    calc h.elt ν * h.elt σ * p * (h.elt ν * h.elt σ)⁻¹ =
        h.elt ν * (h.elt σ * p * (h.elt σ)⁻¹) * (h.elt ν)⁻¹ := by group
      _ = h.elt σ * (h.elt ν * p * (h.elt ν)⁻¹) * (h.elt σ)⁻¹ := e
      _ = h.elt σ * h.elt ν * p * (h.elt σ * h.elt ν)⁻¹ := by group
  have hfix' : ∀ y ∈ P, y * h.elt ν = h.elt ν * y → y * h.elt σ = h.elt σ * y := by
    intro y hy hyn
    have hν1 : ν ⟨y, hy⟩ = ⟨y, hy⟩ := by
      apply Subtype.ext
      rw [hnp]
      calc h.elt ν * y * (h.elt ν)⁻¹ = y * h.elt ν * (h.elt ν)⁻¹ := by rw [← hyn]
        _ = y := by group
    have hσ1 := congrArg Subtype.val (hfix ⟨y, hy⟩ hν1)
    rw [hsp] at hσ1
    calc y * h.elt σ = (h.elt σ * y * (h.elt σ)⁻¹) * h.elt σ := by rw [hσ1]
      _ = h.elt σ * y := by group
  rcases d.core (E := Exc ν) hn hs hnn hss hns hfix' (fun hnP z hz hz2 hzn hzc =>
    houter ν (h.elt ν) hn hnP (fun p => hnp p) hnn z hz hz2 hzn hzc) with h1 | h1 | h1
  · left
    refine MulEquiv.ext fun p => Subtype.ext ?_
    rw [hsp, h1]
    simp
  · right; left
    refine MulEquiv.ext fun p => Subtype.ext ?_
    rw [hsp, hnp, h1]
  · exact Or.inr (Or.inr h1)

end AutRowData

theorem centerInv_conj {a r c : M} (hc : c ∈ P) (har : a = c * r * c⁻¹)
    (h : ∀ z ∈ P, z * z = 1 → z * r = r * z → (∀ y ∈ P, y * r = r * y → z * y = y * z) →
      z = 1 ∨ z = r) :
    ∀ z ∈ P, z * z = 1 → z * a = a * z → (∀ y ∈ P, y * a = a * y → z * y = y * z) →
      z = 1 ∨ z = a := by
  intro z hz hzz hza hzc
  subst har
  have hz' : c⁻¹ * z * c ∈ P := P.mul_mem (P.mul_mem (P.inv_mem hc) hz) hc
  have h1 := h (c⁻¹ * z * c) hz'
    (by calc c⁻¹ * z * c * (c⁻¹ * z * c) = c⁻¹ * (z * z) * c := by group
          _ = 1 := by rw [hzz]; group)
    (by calc c⁻¹ * z * c * r = c⁻¹ * (z * (c * r * c⁻¹)) * c := by group
          _ = c⁻¹ * ((c * r * c⁻¹) * z) * c := by rw [hza]
          _ = r * (c⁻¹ * z * c) := by group)
    (by
      intro y hy hyr
      have hy' : c * y * c⁻¹ ∈ P := P.mul_mem (P.mul_mem hc hy) (P.inv_mem hc)
      have h2 := hzc (c * y * c⁻¹) hy' (by
        calc c * y * c⁻¹ * (c * r * c⁻¹) = c * (y * r) * c⁻¹ := by group
          _ = c * (r * y) * c⁻¹ := by rw [hyr]
          _ = c * r * c⁻¹ * (c * y * c⁻¹) := by group)
      calc c⁻¹ * z * c * y = c⁻¹ * (z * (c * y * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * y * c⁻¹) * z) * c := by rw [h2]
        _ = y * (c⁻¹ * z * c) := by group)
  rcases h1 with h1 | h1
  · left
    calc z = c * (c⁻¹ * z * c) * c⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · right
    calc z = c * (c⁻¹ * z * c) * c⁻¹ := by group
      _ = c * r * c⁻¹ := by rw [h1]

theorem AutModel.umovesCond (h : AutModel P R)
    (hwit : ∀ u ∈ P, orderOf u = 2 → ∀ w ∈ R, w * w = 1 →
      ∃ x ∈ P, (x * u * x⁻¹) * w = w * (x * u * x⁻¹)) : UMovesCond ↥P := by
  intro u hu α hα
  have hw := h.elt_mem α
  have hwp := h.elt_spec α
  have hww : h.elt α * h.elt α = 1 := by
    refine h.eq_of_conj (R.mul_mem hw hw) R.one_mem fun p hp => ?_
    have e := congrArg (fun β : MulAut P => ((β ⟨p, hp⟩ : P) : M)) hα
    simp only [MulAut.mul_apply, MulAut.one_apply] at e
    rw [hwp, hwp] at e
    calc h.elt α * h.elt α * p * (h.elt α * h.elt α)⁻¹ =
        h.elt α * (h.elt α * p * (h.elt α)⁻¹) * (h.elt α)⁻¹ := by group
      _ = p := e
      _ = 1 * p * 1⁻¹ := by group
  have hu' : orderOf (u : M) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
  obtain ⟨x, hx, hxc⟩ := hwit u u.2 hu' _ hw hww
  refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
  rw [hwp]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc h.elt α * (x * (u : M) * x⁻¹) * (h.elt α)⁻¹ =
      (x * (u : M) * x⁻¹) * h.elt α * (h.elt α)⁻¹ := by rw [← hxc]
    _ = x * (u : M) * x⁻¹ := by group

theorem exists_commuting_conj_of_cover (U W : List M)
    (hUcov : ∀ u ∈ P, orderOf u = 2 → ∃ r ∈ U, ∃ c ∈ P, u = c * r * c⁻¹)
    (hWcov : ∀ w ∈ R, orderOf w = 2 → ∃ r ∈ W, ∃ c ∈ R, w = c * r * c⁻¹)
    (hfuse : ∀ r ∈ U, ∀ c ∈ R, ∃ g ∈ P, c * r * c⁻¹ = g * r * g⁻¹)
    (hwit : ∀ r ∈ U, ∀ r' ∈ W, ∃ h ∈ P, (h * r * h⁻¹) * r' = r' * (h * r * h⁻¹))
    (hle : P ≤ R) :
    ∀ u ∈ P, orderOf u = 2 → ∀ w ∈ R, w * w = 1 →
      ∃ x ∈ P, (x * u * x⁻¹) * w = w * (x * u * x⁻¹) := by
  intro u hu hu2 w hw hww
  by_cases hw1 : w = 1
  · exact ⟨1, P.one_mem, by rw [hw1]; simp⟩
  have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hww) hw1
  obtain ⟨r, hr, c, hc, rfl⟩ := hUcov u hu hu2
  obtain ⟨r', hr', d, hd, rfl⟩ := hWcov w hw hw2
  obtain ⟨h₀, hh₀, hcomm⟩ := hwit r hr r' hr'
  obtain ⟨g, hg, hgr⟩ := hfuse r hr (d * h₀) (R.mul_mem hd (hle hh₀))
  refine ⟨g * c⁻¹, P.mul_mem hg (P.inv_mem hc), ?_⟩
  have e : (g * c⁻¹) * (c * r * c⁻¹) * (g * c⁻¹)⁻¹ = d * (h₀ * r * h₀⁻¹) * d⁻¹ := by
    calc (g * c⁻¹) * (c * r * c⁻¹) * (g * c⁻¹)⁻¹ = g * r * g⁻¹ := by group
      _ = d * h₀ * r * (d * h₀)⁻¹ := hgr.symm
      _ = d * (h₀ * r * h₀⁻¹) * d⁻¹ := by group
  rw [e]
  calc d * (h₀ * r * h₀⁻¹) * d⁻¹ * (d * r' * d⁻¹) = d * ((h₀ * r * h₀⁻¹) * r') * d⁻¹ := by group
    _ = d * (r' * (h₀ * r * h₀⁻¹)) * d⁻¹ := by rw [hcomm]
    _ = d * r' * d⁻¹ * (d * (h₀ * r * h₀⁻¹) * d⁻¹) := by group

end CFSG.EvenSporadicStandard.Solomon78
