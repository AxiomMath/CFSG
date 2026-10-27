module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

theorem map_oddCore_le {G : Type*} [Group G] [Finite G] (φ : G ≃* G) :
    (oddCore G).map φ.toMonoidHom ≤ oddCore G := by
  apply le_oddCore_of_normal (Subgroup.Normal.map (oddCore_normal (G := G)) _ φ.surjective)
  have hc : Nat.card ((oddCore G).map φ.toMonoidHom) = Nat.card (oddCore G) :=
    Nat.card_congr ((oddCore G).equivMapOfInjective _ φ.injective).toEquiv.symm
  rw [hc]
  exact odd_card_oddCore

theorem oddCore_eq_bot_of_normal {C : Type*} [Group C] [Finite C] (M : Subgroup C) [M.Normal]
    (h : oddCore C = ⊥) : oddCore M = ⊥ := by
  set K : Subgroup C := (oddCore M).map M.subtype with hK
  have hKn : K.Normal := by
    refine ⟨?_⟩
    rintro _ ⟨m, hm, rfl⟩ c
    have hmem : (MulAut.conjNormal c : MulAut M) m ∈ oddCore M :=
      map_oddCore_le (MulAut.conjNormal c) ⟨m, hm, rfl⟩
    exact ⟨_, hmem, by simp [MulAut.conjNormal_apply]⟩
  have hodd : Odd (Nat.card K) := by
    rw [hK, Nat.card_congr ((oddCore M).equivMapOfInjective _ M.subtype_injective).toEquiv.symm]
    exact odd_card_oddCore
  have hle : K ≤ oddCore C := le_oddCore_of_normal hKn hodd
  rw [h, le_bot_iff, hK] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective (oddCore M) M.subtype_injective).mp hle

theorem oddCore_prod_eq_bot {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (hA : oddCore A = ⊥) (hB : oddCore B = ⊥) : oddCore (A × B) = ⊥ := by
  set N : Subgroup (A × B) := oddCore (A × B) with hN
  have h1 : N.map (MonoidHom.fst A B) ≤ oddCore A := by
    refine le_oddCore_of_normal (Subgroup.Normal.map inferInstance _ fun a => ⟨(a, 1), rfl⟩) ?_
    exact Odd.of_dvd_nat (odd_card_oddCore (G := A × B)) (Subgroup.card_map_dvd _ _)
  have h2 : N.map (MonoidHom.snd A B) ≤ oddCore B := by
    refine le_oddCore_of_normal (Subgroup.Normal.map inferInstance _ fun b => ⟨(1, b), rfl⟩) ?_
    exact Odd.of_dvd_nat (odd_card_oddCore (G := A × B)) (Subgroup.card_map_dvd _ _)
  rw [hA] at h1
  rw [hB] at h2
  refine eq_bot_iff.mpr fun x hx => ?_
  have hx1 : x.1 ∈ (⊥ : Subgroup A) := h1 ⟨x, hx, rfl⟩
  have hx2 : x.2 ∈ (⊥ : Subgroup B) := h2 ⟨x, hx, rfl⟩
  rw [Subgroup.mem_bot] at hx1 hx2 ⊢
  exact Prod.ext hx1 hx2

theorem oddCore_eq_bot_of_isPGroup_two {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G) :
    oddCore G = ⊥ := by
  have hN : IsPGroup 2 (oddCore G) := hG.to_subgroup _
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hN
  have hodd : Odd (Nat.card (oddCore G)) := odd_card_oddCore
  rw [hk] at hodd
  have hk0 : k = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hne).mpr even_two)
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq _ hk

theorem card_subgroupOf_dvd {G : Type*} [Group G] (H K : Subgroup G) :
    Nat.card (H.subgroupOf K) ∣ Nat.card H := by
  let f : H.subgroupOf K →* H := ((K.subtype).comp (H.subgroupOf K).subtype).codRestrict H
    fun x => Subgroup.mem_subgroupOf.mp x.2
  refine Subgroup.card_dvd_of_injective f fun x y hxy => ?_
  have h : ((x : K) : G) = ((y : K) : G) := congrArg (fun z : H => (z : G)) hxy
  exact Subtype.ext (Subtype.ext h)

theorem eq_one_of_mem_oddCore_of_commute {C : Type*} [Group C] [Finite C] {a : C}
    (hA : oddCore ↥(Subgroup.centralizer ({a} : Set C)) = ⊥) {x : C} (hx : x ∈ oddCore C)
    (hxa : x * a = a * x) : x = 1 := by
  set Z : Subgroup C := Subgroup.centralizer ({a} : Set C) with hZ
  have hn : ((oddCore C).subgroupOf Z).Normal := Subgroup.Normal.subgroupOf inferInstance Z
  have hodd : Odd (Nat.card ((oddCore C).subgroupOf Z)) :=
    Odd.of_dvd_nat (odd_card_oddCore (G := C)) (card_subgroupOf_dvd _ _)
  have hle := le_oddCore_of_normal hn hodd
  rw [hA] at hle
  have hxZ : x ∈ Z := Subgroup.mem_centralizer_singleton_iff.mpr hxa
  have hx' : (⟨x, hxZ⟩ : Z) ∈ (oddCore C).subgroupOf Z := hx
  have := hle hx'
  rw [Subgroup.mem_bot] at this
  exact congrArg Subtype.val this

theorem eq_inv_of_centralizer_trivial {C : Type*} [Group C] {N : Subgroup C} [Finite N] {t : C}
    (htt : t * t = 1) (hN : ∀ x ∈ N, t * x * t⁻¹ ∈ N)
    (hC : ∀ x ∈ N, x * t = t * x → x = 1) : ∀ x ∈ N, t * x * t⁻¹ = x⁻¹ := by
  have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  let f : N → N := fun x => ⟨(x : C)⁻¹ * (t * x * t⁻¹), N.mul_mem (N.inv_mem x.2) (hN x x.2)⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have h : (x : C)⁻¹ * (t * x * t⁻¹) = (y : C)⁻¹ * (t * y * t⁻¹) := congrArg Subtype.val hxy
    have h' : (x : C)⁻¹ * t * x = (y : C)⁻¹ * t * y :=
      calc (x : C)⁻¹ * t * x = ((x : C)⁻¹ * (t * x * t⁻¹)) * t := by group
        _ = ((y : C)⁻¹ * (t * y * t⁻¹)) * t := by rw [h]
        _ = (y : C)⁻¹ * t * y := by group
    have hc : ((y : C) * (x : C)⁻¹) * t = t * ((y : C) * (x : C)⁻¹) :=
      calc ((y : C) * (x : C)⁻¹) * t = y * ((x : C)⁻¹ * t * x) * (x : C)⁻¹ := by group
        _ = y * ((y : C)⁻¹ * t * y) * (x : C)⁻¹ := by rw [h']
        _ = t * ((y : C) * (x : C)⁻¹) := by group
    have h1 := hC _ (N.mul_mem y.2 (N.inv_mem x.2)) hc
    exact Subtype.ext (mul_inv_eq_one.mp h1).symm
  obtain hsurj := Finite.injective_iff_surjective.mp hinj
  intro u hu
  obtain ⟨x, hx⟩ := hsurj ⟨u, hu⟩
  have hu' : (x : C)⁻¹ * (t * x * t⁻¹) = u := congrArg Subtype.val hx
  rw [← hu']
  calc t * ((x : C)⁻¹ * (t * x * t⁻¹)) * t⁻¹
      = t * (x : C)⁻¹ * t * x * (t * t)⁻¹ := by group
    _ = t * (x : C)⁻¹ * t * x := by rw [htt, inv_one, mul_one]
    _ = ((x : C)⁻¹ * (t * x * t⁻¹))⁻¹ := by
        have e : ((x : C)⁻¹ * (t * x * t⁻¹))⁻¹ = t * (x : C)⁻¹ * t⁻¹ * x := by group
        rw [e, ht]

theorem oddCore_eq_bot_of_three_involutions {C : Type*} [Group C] [Finite C] {a b : C}
    (ha : a * a = 1) (hb : b * b = 1)
    (hA : oddCore ↥(Subgroup.centralizer ({a} : Set C)) = ⊥)
    (hB : oddCore ↥(Subgroup.centralizer ({b} : Set C)) = ⊥)
    (hAB : oddCore ↥(Subgroup.centralizer ({a * b} : Set C)) = ⊥) : oddCore C = ⊥ := by
  have hnorm : ∀ x ∈ oddCore C, ∀ g : C, g * x * g⁻¹ ∈ oddCore C :=
    fun x hx g => (oddCore_normal (G := C)).conj_mem x hx g
  have hia : ∀ x ∈ oddCore C, a * x * a⁻¹ = x⁻¹ :=
    eq_inv_of_centralizer_trivial ha (fun x hx => hnorm x hx a)
      (fun x hx hxa => eq_one_of_mem_oddCore_of_commute hA hx hxa)
  have hib : ∀ x ∈ oddCore C, b * x * b⁻¹ = x⁻¹ :=
    eq_inv_of_centralizer_trivial hb (fun x hx => hnorm x hx b)
      (fun x hx hxb => eq_one_of_mem_oddCore_of_commute hB hx hxb)
  refine eq_bot_iff.mpr fun x hx => ?_
  rw [Subgroup.mem_bot]
  refine eq_one_of_mem_oddCore_of_commute hAB hx ?_
  have h1 := hib x hx
  have h2 := hia x⁻¹ (inv_mem hx)
  have h3 : (a * b) * x * (a * b)⁻¹ = x :=
    calc (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
      _ = a * x⁻¹ * a⁻¹ := by rw [h1]
      _ = x := by rw [h2, inv_inv]
  exact (mul_inv_eq_iff_eq_mul.mp h3).symm

end CFSG.OddStandard.SmallF3.Omega
