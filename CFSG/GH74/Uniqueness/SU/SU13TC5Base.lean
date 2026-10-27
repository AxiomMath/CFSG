module

public import CFSG.GH74.Uniqueness.SU.SU13TC4A
public import CFSG.GH74.Uniqueness.SU.SU13TC2LL

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G] [Finite G] {z : G}

abbrev Asub {e : Elts G z} {e9 : Elts9 z e} {f' : FPart z e} (E9 : EPart9 z e e9 f') (hWc : WAbel e) :
    Subgroup G := E9.E ⊔ Zsub (Vsub z e.s₁ hWc) E9.D

section Base

variable {e : Elts G z} {e9 : Elts9 z e} (f : FPart9 z e) (E9 : EPart9 z e e9 f.toFPart) (hWc : WAbel e)

theorem t_mem_NHE : e.t ∈ NHE E9.E z := by
  have ht2 : e.t * e.t = 1 := by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two e.t_ord
  have hti : e.t⁻¹ = e.t := inv_eq_of_mul_eq_one_right ht2
  refine mem_inf.mpr ⟨?_, mem_centralizer_singleton_iff.mpr e.t_comm⟩
  rw [mem_normalizer_iff]
  intro x
  refine ⟨E9.t_norm x, fun hx => ?_⟩
  have := E9.t_norm _ hx
  rw [hti] at this
  have h : e.t * (e.t * x * e.t) * e.t = x := by
    calc e.t * (e.t * x * e.t) * e.t = (e.t * e.t) * x * (e.t * e.t) := by group
      _ = x := by rw [ht2]; group
  rwa [h] at this

theorem z_mem_NHE : z ∈ NHE E9.E z := by
  refine mem_inf.mpr ⟨?_, mem_centralizer_singleton_iff.mpr rfl⟩
  rw [mem_normalizer_iff]
  intro x
  have hc : ∀ y ∈ E9.E, z * y * z⁻¹ = y := fun y hy => by
    have := E9.Es_comm y (E9.Es_ge hy)
    rw [← this]; group
  refine ⟨fun hx => by rw [hc x hx]; exact hx, fun hx => ?_⟩
  have h : z * x * z⁻¹ = x := by
    have h1 := hc (z * x * z⁻¹) hx
    calc z * x * z⁻¹ = z⁻¹ * (z * (z * x * z⁻¹) * z⁻¹) * z := by group
      _ = z⁻¹ * (z * x * z⁻¹) * z := by rw [h1]
      _ = x := by group
  rw [h] at hx
  exact hx

theorem A_inf_cent_z (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5) (hz : orderOf z = 2) :
    Asub E9 hWc ⊓ centralizer ({z} : Set G) = E9.E := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxA, hxz⟩ := mem_inf.mp hx
    obtain ⟨a, ha, ζ, hζ, rfl⟩ := A_mem f E9 hWc hxA
    have hcz : z * (a * ζ) = (a * ζ) * z := (mem_centralizer_singleton_iff.mp hxz).symm
    have hza : z * a = a * z := (E9.Es_comm a (E9.Es_ge ha)).symm
    have hζz : z * ζ * z⁻¹ = ζ⁻¹ := hζ.1.2
    have h1 : ζ = ζ⁻¹ := by
      calc ζ = a⁻¹ * (a * ζ) := by group
        _ = a⁻¹ * (z * (a * ζ) * z⁻¹) := by rw [hcz]; group
        _ = a⁻¹ * ((z * a * z⁻¹) * (z * ζ * z⁻¹)) := by group
        _ = a⁻¹ * (a * ζ⁻¹) := by rw [hζz, show z * a * z⁻¹ = a by rw [hza]; group]
        _ = ζ⁻¹ := by group
    have hζ3 : ζ ^ 3 = 1 := V_exp hz f hWc hW5 ζ hζ.1
    have hζ1 : ζ = 1 := by
      have h2 : ζ * ζ = 1 := by
        calc ζ * ζ = ζ * ζ⁻¹ := by rw [← h1]
          _ = 1 := mul_inv_cancel ζ
      calc ζ = ζ ^ 3 * (ζ * ζ)⁻¹ := by group
        _ = 1 := by rw [hζ3, h2, inv_one, mul_one]
    rw [hζ1, mul_one]; exact ha
  · intro x hx
    exact mem_inf.mpr ⟨mem_sup_left hx, mem_centralizer_singleton_iff.mpr (E9.Es_comm x (E9.Es_ge hx))⟩

theorem zpowers_s₂_le_E : zpowers e.s₂ ≤ E9.E := (zpowers_le).mpr E9.s₂_mem

theorem A_inf_cent_R (hz : orderOf z = 2) (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5)
    (hm : MPart9 z e E9.E) :
    Asub E9 hWc ⊓ centralizer ((kfour hz e : Subgroup G) : Set G) = zpowers e.s₂ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxA, hxK⟩ := mem_inf.mp hx
    have hxz : x * z = z * x := (mem_centralizer_iff.mp hxK z (z_mem_kfour hz e)).symm
    have hxt : e.t * x = x * e.t := mem_centralizer_iff.mp hxK e.t (t_mem_kfour hz e)
    have hxE : x ∈ E9.E := by
      have : x ∈ Asub E9 hWc ⊓ centralizer ({z} : Set G) :=
        mem_inf.mpr ⟨hxA, mem_centralizer_singleton_iff.mpr hxz⟩
      rwa [A_inf_cent_z f E9 hWc hW5 hz] at this
    exact hm.cent_t x hxE hxt
  · intro x hx
    refine mem_inf.mpr ⟨mem_sup_left (zpowers_s₂_le_E f E9 hx), mem_centralizer_iff.mpr fun y hy => ?_⟩
    obtain ⟨k, rfl⟩ := hx
    have hcy : Commute y e.s₂ := by
      rcases kfour_mem hz e hy with rfl | rfl | rfl | rfl
      · exact Commute.mul_left e.t_s₂ e.s₂_comm.symm
      · exact e.t_s₂
      · exact e.s₂_comm.symm
      · exact Commute.one_left _
    exact (hcy.zpow_right k).eq

theorem card_A_cent_t (hz : orderOf z = 2) (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5)
    (l : Lem232 z e) (hm : MPart9 z e E9.E) :
    Nat.card (Asub E9 hWc ⊓ centralizer ({e.t} : Set G) : Subgroup G) = 9 := by
  have : IsKleinFour (kfour hz e) := isKleinFour_kfour hz e
  have hz1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hz; exact absurd hz (by norm_num)
  have ht1 : e.t ≠ 1 := by
    intro h; have := e.t_ord; rw [h, orderOf_one] at this; exact absurd this (by norm_num)
  have hNA := NHE_le_normalizer_A f E9 hWc hz hW5 l
  have hAodd : Odd (Nat.card (Asub E9 hWc)) := by rw [A_card f E9 hWc hz hW5]; decide
  have htzN : e.t * z ∈ NHE E9.E z := (NHE E9.E z).mul_mem (t_mem_NHE f E9) (z_mem_NHE f E9)
  have hTn : kfour hz e ≤ normalizer ((Asub E9 hWc : Subgroup G) : Set G) := by
    intro x hx
    rcases kfour_mem hz e hx with rfl | rfl | rfl | rfl
    · exact hNA htzN
    · exact hNA (t_mem_NHE f E9)
    · exact hNA (z_mem_NHE f E9)
    · exact one_mem _
  have hBW := CFSG.ABGLocalTools.card_mul_card_centralizer_four_sq (T := kfour hz e) (K := Asub E9 hWc)
    hAodd hTn (a := e.t) (b := z) (t_mem_kfour hz e) (z_mem_kfour hz e) ht1 hz1 e.t_ne
  rw [A_inf_cent_R f E9 hWc hz hW5 hm, A_inf_cent_z f E9 hWc hW5 hz, A_card f E9 hWc hz hW5,
    Nat.card_zpowers, e.s₂_ord, E9.E_card] at hBW
  have htz2 : orderOf (e.t * z) = 2 := orderOf_mul_eq_two_of_commute e.t_ord hz e.t_comm e.t_ne
  have htzz : e.t * z ≠ z := by
    intro h
    apply ht1
    calc e.t = e.t * z * z⁻¹ := by group
      _ = z * z⁻¹ := by rw [h]
      _ = 1 := mul_inv_cancel z
  obtain ⟨g, hgN, hg⟩ := E9.invClass (e.t * z) htzN htz2 htzz
  have hconj := card_inf_centralizer_conj (Y := Asub E9 hWc) (hNA hgN) e.t
  rw [hg] at hconj
  rw [hconj] at hBW
  set c := Nat.card (Asub E9 hWc ⊓ centralizer ({e.t} : Set G) : Subgroup G) with hc
  have h1 : c * c = 9 * 9 := by
    norm_num at hBW
    nlinarith [hBW]
  exact Nat.mul_self_inj.mp h1

end Base

end CFSG.GH74.Uniqueness.SU.SU13
