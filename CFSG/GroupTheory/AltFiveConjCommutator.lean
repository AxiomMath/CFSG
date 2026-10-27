module

public import CFSG.Permutation.AlternatingAutomorphism.Conjugation

public section

namespace CFSG.GroupTheory

theorem alt5_exists_conj_comm_order (σ : Equiv.Perm (Fin 5)) (hσ : σ ≠ 1) :
    ∃ x ∈ alternatingGroup (Fin 5),
      orderOf (x⁻¹ * σ * x * σ⁻¹) = 3 ∨ orderOf (x⁻¹ * σ * x * σ⁻¹) = 5 := by
  have hdec : ∀ σ : Equiv.Perm (Fin 5), σ ≠ 1 →
      ∃ x : alternatingGroup (Fin 5),
        (((x : Equiv.Perm (Fin 5))⁻¹ * σ * x * σ⁻¹) ^ 3 = 1 ∧
          (x : Equiv.Perm (Fin 5))⁻¹ * σ * x * σ⁻¹ ≠ 1) ∨
        (((x : Equiv.Perm (Fin 5))⁻¹ * σ * x * σ⁻¹) ^ 5 = 1 ∧
          (x : Equiv.Perm (Fin 5))⁻¹ * σ * x * σ⁻¹ ≠ 1) := by
    decide +kernel
  obtain ⟨x, hx⟩ := hdec σ hσ
  refine ⟨x, x.property, ?_⟩
  rcases hx with ⟨h3, hne3⟩ | ⟨h5, hne5⟩
  · exact Or.inl (orderOf_eq_prime h3 hne3)
  · right
    have hdvd : orderOf (x⁻¹ * σ * x * σ⁻¹) ∣ 5 :=
      orderOf_dvd_iff_pow_eq_one.mpr h5
    rcases Nat.prime_five.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne5
    · exact h

theorem exists_inv_mul_apply_order_three_or_five {H : Type*} [Group H]
    (e : H ≃* alternatingGroup (Fin 5)) (β : MulAut H) (hβ : β ≠ 1) :
    ∃ x : H, orderOf (x⁻¹ * β x) = 3 ∨ orderOf (x⁻¹ * β x) = 5 := by
  let β' : MulAut (alternatingGroup (Fin 5)) := e.symm.trans (β.trans e)
  have hβ'apply : ∀ y : alternatingGroup (Fin 5), β' y = e (β (e.symm y)) := fun _ => rfl
  have hβ' : β' ≠ 1 := by
    intro h1
    apply hβ
    ext h
    have h2 : β' (e h) = e h := by
      simpa using congrArg (fun f : MulAut (alternatingGroup (Fin 5)) => f (e h)) h1
    simpa using e.injective (by simpa [hβ'apply] using h2)
  obtain ⟨σ, hσ⟩ :=
    CFSG.AlternatingAutomorphism.exists_perm_conj (Or.inl (by simp)) β'
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hβ'
    apply MulEquiv.ext
    intro g
    have hg := hσ g
    rw [h1] at hg
    simpa using hg
  obtain ⟨x, hxmem, hxord⟩ := alt5_exists_conj_comm_order σ hσ1
  let xa : alternatingGroup (Fin 5) := ⟨x, hxmem⟩
  have hxa : (xa : Equiv.Perm (Fin 5)) = x := rfl
  have hxβ : (β' xa : Equiv.Perm (Fin 5)) = σ * x * σ⁻¹ := by
    rw [hσ xa, hxa]
  have hcoe : ((xa⁻¹ * β' xa : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) =
      x⁻¹ * σ * x * σ⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hxβ, hxa]
    simp only [mul_assoc]
  have horder : orderOf (xa⁻¹ * β' xa) = orderOf (x⁻¹ * σ * x * σ⁻¹) := by
    rw [← orderOf_injective (alternatingGroup (Fin 5)).subtype Subtype.coe_injective
      (xa⁻¹ * β' xa)]
    exact congrArg orderOf hcoe
  have hmain : orderOf ((e.symm xa)⁻¹ * β (e.symm xa)) = orderOf (xa⁻¹ * β' xa) := by
    have h1 : (e.symm xa)⁻¹ * β (e.symm xa) = e.symm (xa⁻¹ * β' xa) := by
      apply e.injective
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, ← hβ'apply xa]
    rw [h1]
    exact orderOf_injective e.symm.toMonoidHom e.symm.injective _
  refine ⟨e.symm xa, ?_⟩
  rw [hmain, horder]
  exact hxord

theorem exists_inv_mul_conj_order_three_or_five {G : Type*} [Group G] {H : Subgroup G}
    (e : ↥H ≃* alternatingGroup (Fin 5)) {φ : G} (hnorm : ∀ x ∈ H, φ * x * φ⁻¹ ∈ H)
    (hne : ¬ ∀ x ∈ H, φ * x = x * φ) :
    ∃ x ∈ H, orderOf (x⁻¹ * (φ * x * φ⁻¹)) = 3 ∨ orderOf (x⁻¹ * (φ * x * φ⁻¹)) = 5 := by
  have : Finite ↥H := Finite.of_equiv _ e.symm.toEquiv
  have hmap_le : H.map (MulAut.conj φ).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hnorm x hx
  have hmap_eq : H.map (MulAut.conj φ).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hmap_le (by
      rw [Subgroup.card_map_of_injective (MulAut.conj φ).injective])
  have hmap_eq' : H.map (↑(MulAut.conj φ)) = H := hmap_eq
  let β : MulAut ↥H :=
    ((MulAut.conj φ).subgroupMap H).trans (MulEquiv.subgroupCongr hmap_eq')
  have hβcoe : ∀ x : ↥H, ((β x : ↥H) : G) = φ * (x : G) * φ⁻¹ := by
    intro x
    simp only [β, MulEquiv.trans_apply]
    rw [MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]
  have hβne : β ≠ 1 := by
    intro hβ1
    apply hne
    intro x hx
    have hxβ : β ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [hβ1]; rfl
    have hcoe := congrArg (fun z : ↥H => (z : G)) hxβ
    rw [hβcoe] at hcoe
    calc φ * x = (φ * x * φ⁻¹) * φ := by group
      _ = x * φ := by rw [hcoe]
  obtain ⟨x, hxord⟩ := exists_inv_mul_apply_order_three_or_five e β hβne
  refine ⟨(x : G), x.2, ?_⟩
  have hycoe : ((x⁻¹ * β x : ↥H) : G) = (x : G)⁻¹ * (φ * (x : G) * φ⁻¹) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hβcoe]
  have hordβ : orderOf (x⁻¹ * β x : ↥H) = orderOf ((x : G)⁻¹ * (φ * (x : G) * φ⁻¹)) := by
    rw [← orderOf_injective H.subtype Subtype.coe_injective (x⁻¹ * β x)]
    exact congrArg orderOf hycoe
  rw [← hordβ]
  exact hxord

theorem eq_one_one_of_central {C : Type} [CommGroup C]
    {x : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) × C}
    (hx : ∀ y, x * y = y * x) : x.1 = 1 ∧ x.2.1 = 1 := by
  have hc : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by norm_num)
  constructor
  · have hmem : x.1 ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := hx (g, 1, 1)
      have h1 := congrArg Prod.fst h
      simpa using h1.symm
    rw [hc] at hmem
    exact Subgroup.mem_bot.mp hmem
  · have hmem : x.2.1 ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := hx (1, g, 1)
      have h1 := congrArg (fun z => z.2.1) h
      simpa using h1.symm
    rw [hc] at hmem
    exact Subgroup.mem_bot.mp hmem

theorem card_le_of_isPerfect_of_mulEquiv {X C : Type} [Group X] [Finite X] [CommGroup C]
    (e : X ≃* (alternatingGroup (Fin 5) × alternatingGroup (Fin 5) × C)) {P : Subgroup X}
    (hP : ⁅P, P⁆ = P) : Nat.card P ≤ 3600 := by
  classical
  have : Finite C := Finite.of_surjective (fun x : X => (e x).2.2)
    (fun c => ⟨e.symm (1, 1, c), by simp⟩)
  let π : X →* C := (MonoidHom.snd _ _).comp ((MonoidHom.snd _ _).comp e.toMonoidHom)
  have hπ : Function.Surjective π := fun c => ⟨e.symm (1, 1, c), by simp [π]⟩
  have hPker : P ≤ π.ker := by
    have hmap : P.map π = ⊥ := by
      have h1 : (⁅P, P⁆).map π = ⁅P.map π, P.map π⁆ := Subgroup.map_commutator P P π
      rw [hP] at h1
      rw [h1, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact mul_comm y x
    rw [← Subgroup.map_eq_bot_iff]
    exact hmap
  have hcardX : Nat.card X = 3600 * Nat.card C := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_prod, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
    ring
  have hindex : π.ker.index = Nat.card C := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hπ, Subgroup.card_top]
  have hker : Nat.card π.ker = 3600 := by
    have h := Subgroup.card_mul_index π.ker
    rw [hindex, hcardX] at h
    have hC : 0 < Nat.card C := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hC h
  calc Nat.card P ≤ Nat.card π.ker := Subgroup.card_le_of_le hPker
    _ = 3600 := hker

end CFSG.GroupTheory
