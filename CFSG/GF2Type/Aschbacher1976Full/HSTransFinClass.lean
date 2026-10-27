module

public import CFSG.GF2Type.Aschbacher1976Full.HSTransFinData
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Algebra.GroupWithZero.Units.Fintype

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.TransFin

open Equiv CFSG.GF2Type.Aschbacher1976Full.HS.Six

theorem even_invol_supp {σ : Perm (Fin 6)} (h2 : σ * σ = 1) (h1 : σ ≠ 1)
    (hs : Perm.sign σ = 1) : σ.support.card = 4 := by
  have hsq : σ ^ 2 = 1 := by rw [sq]; exact h2
  have hord : orderOf σ = 2 := orderOf_eq_prime hsq h1
  have hp : (orderOf σ).Prime := by rw [hord]; exact Nat.prime_two
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order hp
  rw [hord] at hn
  have hsum : σ.support.card = 2 * (n + 1) := by
    rw [← Equiv.Perm.sum_cycleType, hn]; simp; ring
  have hle : σ.support.card ≤ 6 := by
    have := Finset.card_le_univ σ.support
    simpa using this
  have hsign := Equiv.Perm.sign_of_cycleType σ
  rw [hs, hn, Multiset.sum_replicate, Multiset.card_replicate] at hsign
  have hev : Even ((n + 1) * 2 + (n + 1)) :=
    (neg_one_pow_eq_one_iff_even (R := ℤˣ) (by decide)).1 hsign.symm
  obtain ⟨m, hm⟩ := hev
  omega

theorem exists_even_pair {Q : Type*} [Group Q] (ι : Q →* Perm (Fin 6)) (Y : Subgroup Q)
    (hcard : 8 ≤ Nat.card Y) :
    ∃ d ∈ Y, ∃ e ∈ Y, d ≠ 1 ∧ e ≠ 1 ∧ d ≠ e ∧ Perm.sign (ι d) = 1 ∧ Perm.sign (ι e) = 1 := by
  classical
  have hfin : Finite Y := Nat.finite_of_card_ne_zero (by omega)
  let ρ : Y →* ℤˣ := (Perm.sign.comp ι).comp Y.subtype
  have h1 : Nat.card ρ.ker * ρ.ker.index = Nat.card Y := Subgroup.card_mul_index _
  have h2 : ρ.ker.index = Nat.card ρ.range := Subgroup.index_ker ρ
  have h3 : Nat.card ρ.range ≤ 2 := by
    have : Nat.card ρ.range ∣ Nat.card ℤˣ := Subgroup.card_subgroup_dvd_card _
    have h : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card]; exact Fintype.card_units_int
    rw [h] at this
    exact Nat.le_of_dvd (by norm_num) this
  have h4 : 3 < Nat.card ρ.ker := by
    by_contra hcon
    push Not at hcon
    have : Nat.card ρ.ker * ρ.ker.index ≤ 3 * 2 := Nat.mul_le_mul hcon (h2 ▸ h3)
    omega
  haveI : Fintype ρ.ker := Fintype.ofFinite _
  have h5 : 1 < (Finset.univ.erase (1 : ρ.ker)).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h5
  rw [Finset.mem_erase] at ha hb
  have hne : ∀ c : ρ.ker, c ≠ 1 → ((c : Y) : Q) ≠ 1 := by
    intro c hc h
    apply hc
    exact Subtype.ext (Subtype.ext h)
  have hsg : ∀ c : ρ.ker, Perm.sign (ι ((c : Y) : Q)) = 1 := fun c => c.2
  refine ⟨((a : Y) : Q), (a : Y).2, ((b : Y) : Q), (b : Y).2, hne a ha.1, hne b hb.1, ?_, hsg a,
    hsg b⟩
  intro h
  exact hab (Subtype.ext (Subtype.ext h))

theorem conj_of_cen {Q : Type*} [Group Q] (ι : Q →* Perm (Fin 6)) (hι : Function.Injective ι)
    (Y : Subgroup Q) (hcard : 8 ≤ Nat.card Y) (σ : Perm (Fin 6)) (L : List (Perm (Fin 6)))
    (hnd : L.Nodup) (hlen : L.length = 8) (hcen : ∀ y ∈ Y, σ * ι y * σ⁻¹ ∈ L) :
    ∀ x ∈ L, ∃ y ∈ Y, σ * ι y * σ⁻¹ = x := by
  classical
  have hfin : Finite Y := Nat.finite_of_card_ne_zero (by omega)
  haveI : Fintype Y := Fintype.ofFinite Y
  let f : Y → Perm (Fin 6) := fun y => σ * ι y * σ⁻¹
  have hf : Function.Injective f := by
    intro y z h
    have : ι y = ι z := mul_left_cancel (mul_right_cancel h)
    exact Subtype.ext (hι this)
  have hsub : Finset.univ.image f ⊆ L.toFinset := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
    exact List.mem_toFinset.2 (hcen y y.2)
  have hcardS : (Finset.univ.image f).card = Nat.card Y := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Nat.card_eq_fintype_card]
  have hcardL : L.toFinset.card = 8 := by rw [List.toFinset_card_of_nodup hnd, hlen]
  have heq : Finset.univ.image f = L.toFinset :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  intro x hx
  have : x ∈ Finset.univ.image f := heq ▸ List.mem_toFinset.2 hx
  obtain ⟨y, -, hy⟩ := Finset.mem_image.1 this
  exact ⟨y, y.2, hy⟩

theorem exists_conj_Y {Q : Type*} [Group Q] (ι : Q →* Perm (Fin 6)) (hι : Function.Injective ι)
    (Y : Subgroup Q) (hYc : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) (hYsq : ∀ x ∈ Y, x * x = 1)
    (hcard : 8 ≤ Nat.card Y) :
    ∃ σ : Perm (Fin 6), ∃ L : List (Perm (Fin 6)), (L = Y1L ∨ L = Y2L) ∧
      (∀ y ∈ Y, σ * ι y * σ⁻¹ ∈ L) ∧ (∀ x ∈ L, ∃ y ∈ Y, σ * ι y * σ⁻¹ = x) := by
  obtain ⟨d, hd, e, he, hd1, he1, hde, hsd, hse⟩ := exists_even_pair ι Y hcard
  have hdeY : d * e ∈ Y := Y.mul_mem hd he
  have hd2 : ι d * ι d = 1 := by rw [← map_mul, hYsq d hd, map_one]
  have he2 : ι e * ι e = 1 := by rw [← map_mul, hYsq e he, map_one]
  have hde2 : ι (d * e) * ι (d * e) = 1 := by rw [← map_mul, hYsq _ hdeY, map_one]
  have hd1' : ι d ≠ 1 := fun h => hd1 (hι (by rw [h, map_one]))
  have he1' : ι e ≠ 1 := fun h => he1 (hι (by rw [h, map_one]))
  have hde1 : d * e ≠ 1 := by
    intro h
    exact hde (by
      have := eq_inv_of_mul_eq_one_left h
      rw [this]
      exact (eq_inv_of_mul_eq_one_left (hYsq e he)).symm)
  have hde1' : ι (d * e) ≠ 1 := fun h => hde1 (hι (by rw [h, map_one]))
  have hsde : Perm.sign (ι (d * e)) = 1 := by rw [map_mul, map_mul, hsd, hse, mul_one]
  have c1 := even_invol_supp hd2 hd1' hsd
  have c2 := even_invol_supp he2 he1' hse
  have c3 := even_invol_supp hde2 hde1' hsde
  have hc : ι d * ι e = ι e * ι d := by rw [← map_mul, ← map_mul, hYc d hd e he]
  obtain ⟨-, σ, hσ⟩ := wlog_pair hd2 he2 (fun h => hde (hι h)) hc (by rw [c1, c2])
    (by rw [map_mul] at c3; rw [c3, c1])
  have hconj : ∀ y ∈ Y, ∀ (d' e' : Perm (Fin 6)), σ * ι d * σ⁻¹ = d' → σ * ι e * σ⁻¹ = e' →
      (σ * ι y * σ⁻¹) * d' = d' * (σ * ι y * σ⁻¹) ∧
        (σ * ι y * σ⁻¹) * e' = e' * (σ * ι y * σ⁻¹) := by
    intro y hy d' e' hd' he'
    subst hd' he'
    have h1 : ι y * ι d = ι d * ι y := by rw [← map_mul, ← map_mul, hYc y hy d hd]
    have h2 : ι y * ι e = ι e * ι y := by rw [← map_mul, ← map_mul, hYc y hy e he]
    constructor
    · calc σ * ι y * σ⁻¹ * (σ * ι d * σ⁻¹) = σ * (ι y * ι d) * σ⁻¹ := by group
        _ = σ * (ι d * ι y) * σ⁻¹ := by rw [h1]
        _ = σ * ι d * σ⁻¹ * (σ * ι y * σ⁻¹) := by group
    · calc σ * ι y * σ⁻¹ * (σ * ι e * σ⁻¹) = σ * (ι y * ι e) * σ⁻¹ := by group
        _ = σ * (ι e * ι y) * σ⁻¹ := by rw [h2]
        _ = σ * ι e * σ⁻¹ * (σ * ι y * σ⁻¹) := by group
  rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hcen : ∀ y ∈ Y, σ * ι y * σ⁻¹ ∈ Y1L := by
      intro y hy
      obtain ⟨c1, c2⟩ := hconj y hy dA eA h1 h2
      refine mem_map_tab_iff.1 (cenA _ (mem_allT _) ?_ ?_)
      · rw [← tab_mul, ← tab_mul, c1]
      · rw [← tab_mul, ← tab_mul, c2]
    exact ⟨σ, Y1L, Or.inl rfl, hcen, conj_of_cen ι hι Y hcard σ Y1L Y1L_nodup Y1L_length hcen⟩
  · have hcen : ∀ y ∈ Y, σ * ι y * σ⁻¹ ∈ Y2L := by
      intro y hy
      obtain ⟨c1, c2⟩ := hconj y hy dB eB h1 h2
      refine mem_map_tab_iff.1 (cenB _ (mem_allT _) ?_ ?_)
      · rw [← tab_mul, ← tab_mul, c1]
      · rw [← tab_mul, ← tab_mul, c2]
    exact ⟨σ, Y2L, Or.inr rfl, hcen, conj_of_cen ι hι Y hcard σ Y2L Y2L_nodup Y2L_length hcen⟩

end CFSG.GF2Type.Aschbacher1976Full.HS.TransFin
