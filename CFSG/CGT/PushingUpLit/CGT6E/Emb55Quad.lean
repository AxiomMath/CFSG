module

public import CFSG.CGT.PushingUpLit.CGT6E.Emb55Data

public section

namespace CFSG.CGT.PushingUpLit.CGT6E

open CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6
open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V] {G T Y H Q : Subgroup (MulAut V)}

theorem Emb55Data.quad (d : Emb55Data V G T Y H Q) {y a : MulAut V} (hy : y ∈ Y) (hy1 : y ≠ 1)
    (hyQ : y ∉ Q) (ha : a ∈ Q) (hac : a * ⁅a, y⁆ = ⁅a, y⁆ * a) : ⁅a, y⁆ = 1 := by
  by_contra hc
  set c : MulAut V := ⁅a, y⁆ with hcdef
  set y₁ : MulAut V := a * y * a⁻¹ with hy₁def
  set y₂ : MulAut V := a * y₁ * a⁻¹ with hy₂def
  have hcexp : c = y₁ * y⁻¹ := by rw [hcdef, commutatorElement_def]
  have hcQ : c ∈ Q := by
    have h1 : y * a⁻¹ * y⁻¹ ∈ Q := d.Qnorm y (d.yH hy) a⁻¹ (Q.inv_mem ha)
    have e : c = a * (y * a⁻¹ * y⁻¹) := by rw [hcdef, commutatorElement_def]; group
    rw [e]
    exact Q.mul_mem ha h1
  have hy₁Y : y₁ ∉ Y := fun hmem =>
    hc (d.inf_eq_one hy hy1 hyQ (hcexp ▸ Y.mul_mem hmem (Y.inv_mem hy)) hcQ)
  have haG : a ∈ G := d.QG ha
  obtain ⟨hcomm, hO1⟩ := d.sec.pair_orth hy hy1 haG (d.conj_sup_three ha) hy₁Y
  have hy3 : y ^ 3 = 1 := d.sec.pow_three hy
  have hy₁3 : y₁ ^ 3 = 1 := by
    have : y₁ ^ 3 = a * y ^ 3 * a⁻¹ := conj_pow
    rw [this, hy3]; group
  have hrel : y₂ * y₁⁻¹ = y₁ * y⁻¹ := by
    have h1 : a * c * a⁻¹ = c := by rw [hac]; group
    have e : a * c * a⁻¹ = y₂ * y₁⁻¹ := by
      rw [hcexp, hy₂def, hy₁def]; group
    rw [← e, h1, hcexp]
  have hy₂eq : y₂ * (y * y₁) = 1 := by
    have h2 : y₂ = y₁ * y⁻¹ * y₁ := by
      rw [← mul_inv_eq_iff_eq_mul]; exact hrel
    have h3 : y₁ * y = y * y₁ := hcomm.symm
    calc y₂ * (y * y₁) = (y₁ * y⁻¹ * y₁) * (y * y₁) := by rw [h2]
      _ = y₁ * y⁻¹ * (y₁ * y) * y₁ := by group
      _ = y₁ * y⁻¹ * (y * y₁) * y₁ := by rw [h3]
      _ = y₁ * y₁ * y₁ := by simp [mul_assoc]
      _ = y₁ ^ 3 := (pow_three' y₁).symm
      _ = 1 := hy₁3
  have hy₂inv : y₂ = (y * y₁)⁻¹ := eq_inv_of_mul_eq_one_left hy₂eq
  set U : Subgroup V := commV Y with hUdef
  have hzY : Subgroup.zpowers y = Y := d.sec.zpowers_eq hy hy1
  have hfpf : ∀ u ∈ U, y u = u → u = 1 := fun u hu hyu => by
    rw [hUdef, ← hzY] at hu
    exact eq_one_of_mem_commV_of_fixed d.sec.elem hy3 hu hyu
  have hUy : ∀ u ∈ U, y u ∈ U := fun u hu => commV_invariant hy hu
  have hUle : U ≤ commV (Subgroup.zpowers y₂) := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := exists_apply_mul_inv_eq hUy hfpf hw
    have h1 : (y * y₁) u = y u := by
      rw [MulAut.mul_apply, hO1 u hu]
    have h2 : y u * u⁻¹ = (y * y₁) u * u⁻¹ := by rw [h1]
    rw [h2]
    have hmem : (y * y₁) ∈ Subgroup.zpowers y₂ := by
      rw [hy₂inv, Subgroup.zpowers_inv]
      exact Subgroup.mem_zpowers _
    exact G6.mem_commV_of_mem hmem u
  have hy₂1 : y₂ ≠ 1 := fun e => hy1 (by
    have h1 : (a * a) * y * (a * a)⁻¹ = 1 := by
      have : y₂ = (a * a) * y * (a * a)⁻¹ := by rw [hy₂def, hy₁def]; group
      rw [← this]; exact e
    calc y = (a * a)⁻¹ * ((a * a) * y * (a * a)⁻¹) * (a * a) := by group
      _ = 1 := by rw [h1]; group)
  have hy₂mem : y₂ ∈ conjSub (a * a) Y := by
    have : y₂ = (a * a) * y * (a * a)⁻¹ := by rw [hy₂def, hy₁def]; group
    rw [this]; exact conj_mem_conjSub hy
  have hzy₂ : Subgroup.zpowers y₂ = conjSub (a * a) Y :=
    zpowers_eq_of_card_three (by rw [card_conjSub, d.sec.ycard]) hy₂mem hy₂1
  rw [hzy₂] at hUle
  have hUU : U = commV (conjSub (a * a) Y) :=
    Subgroup.eq_of_le_of_card_ge hUle (by rw [card_commV_conjSub, hUdef])
  have hstab : (a * a) ∈ stabV (commV Y) := stabV_of_commV_conjSub_eq hUU
  have hnorm := d.sec.normalizer_of_stabV ⟨G.mul_mem haG haG, hstab⟩
  have hy₂Y : y₂ ∈ Y := by
    have := (Subgroup.mem_normalizer_iff.mp hnorm y).mp hy
    have e : y₂ = (a * a) * y * (a * a)⁻¹ := by rw [hy₂def, hy₁def]; group
    rw [e]; exact this
  apply hy₁Y
  have : y * y₁ ∈ Y := by
    have := Y.inv_mem hy₂Y
    rwa [hy₂inv, inv_inv] at this
  have e : y₁ = y⁻¹ * (y * y₁) := by group
  rw [e]
  exact Y.mul_mem (Y.inv_mem hy) this

end CFSG.CGT.PushingUpLit.CGT6E
