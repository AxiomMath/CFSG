module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.Alt

open Equiv Equiv.Perm QuaternionGroup

theorem q8_eq_or_sq : ∀ x : QuaternionGroup 2, x ≠ 1 → x = a 2 ∨ x * x = a 2 := by
  decide

variable {α : Type*}

theorem perm_inv_apply_self (f : Perm α) (x : α) : f⁻¹ (f x) = x :=
  f.symm_apply_apply x

theorem perm_apply_inv_self (f : Perm α) (x : α) : f (f⁻¹ x) = x :=
  f.apply_symm_apply x

theorem q8_apply_apply (q : QuaternionGroup 2 →* Perm α) (y x : QuaternionGroup 2) (r : α) :
    q y (q x r) = q (y * x) r := by
  rw [map_mul, Perm.mul_apply]

theorem orbit_injective (q : QuaternionGroup 2 →* Perm α) {r : α} (hr : q (a 2) r ≠ r) :
    Function.Injective fun y => q y r := by
  intro y y' hyy
  simp only at hyy
  by_contra hne
  have h1 : q (y'⁻¹ * y) r = r := by
    rw [← q8_apply_apply, hyy, q8_apply_apply, inv_mul_cancel, map_one, Perm.one_apply]
  have hne' : y'⁻¹ * y ≠ 1 := fun h' => hne (inv_mul_eq_one.mp h').symm
  rcases q8_eq_or_sq _ hne' with h2 | h2
  · exact hr (h2 ▸ h1)
  · apply hr
    rw [← h2, ← q8_apply_apply, h1, h1]

theorem exists_eq_of_moved [Fintype α] [DecidableEq α] (hα : Fintype.card α < 16)
    (q : QuaternionGroup 2 →* Perm α) {p r : α} (hp : q (a 2) p ≠ p) (hr : q (a 2) r ≠ r) :
    ∃ y, q y p = r := by
  by_contra hno
  push Not at hno
  have hdisj : Disjoint (Finset.univ.image fun y => q y p)
      (Finset.univ.image fun y => q y r) := by
    rw [Finset.disjoint_left]
    intro b hb hb'
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨y', -, hy'⟩ := Finset.mem_image.1 hb'
    apply hno (y'⁻¹ * y)
    rw [← q8_apply_apply, ← hy', q8_apply_apply, inv_mul_cancel, map_one, Perm.one_apply]
  have h1 := Finset.card_union_of_disjoint hdisj
  rw [Finset.card_image_of_injective _ (orbit_injective q hp),
    Finset.card_image_of_injective _ (orbit_injective q hr), Finset.card_univ,
    QuaternionGroup.card] at h1
  have h2 := Finset.card_le_univ
    ((Finset.univ.image fun y => q y p) ∪ (Finset.univ.image fun y => q y r))
  omega

@[expose] def wit (x : QuaternionGroup 2) : QuaternionGroup 2 :=
  swap 1 (a 1) (swap (xa 0) (xa 1) (xa 0 * swap (xa 0) (xa 1) (swap 1 (a 1) x)))

theorem wit_comm : ∀ x : QuaternionGroup 2, wit (a 2 * x) = a 2 * wit x := by
  decide

theorem wit_not_left : ∀ z : QuaternionGroup 2, ∃ x, z * wit x ≠ wit (a 1 * x) := by
  decide

theorem swap_swap_q8 : ∀ x : QuaternionGroup 2,
    swap 1 (a 1) (swap (xa 0) (xa 1) (swap (xa 0) (xa 1) (swap 1 (a 1) x))) = x := by
  decide

theorem exists_witness [Fintype α] [DecidableEq α] (q : QuaternionGroup 2 →* Perm α) {p : α}
    (hp : q (a 2) p ≠ p) :
    ∃ σ : Perm α, sign σ = 1 ∧
      (σ * q (xa 0) * σ⁻¹) * q (a 2) = q (a 2) * (σ * q (xa 0) * σ⁻¹) ∧
      ∀ (w : Perm α) (z : QuaternionGroup 2),
        w * (σ * q (xa 0) * σ⁻¹) = (σ * q (xa 0) * σ⁻¹) * q (a 1) →
          ¬ ∀ y, w (q y p) = q (z * y) p := by
  set P : QuaternionGroup 2 → α := fun y => q y p with hPdef
  have hP : Function.Injective P := orbit_injective q hp
  set σ : Perm α := swap (P 1) (P (a 1)) * swap (P (xa 0)) (P (xa 1)) with hσdef
  have hσP : ∀ x, σ (P x) = P (swap 1 (a 1) (swap (xa 0) (xa 1) x)) := fun x => by
    rw [hσdef, Perm.mul_apply, hP.swap_apply, hP.swap_apply]
  have hσiP : ∀ x, σ⁻¹ (P x) = P (swap (xa 0) (xa 1) (swap 1 (a 1) x)) := fun x => by
    rw [Perm.inv_eq_iff_eq, hσP, swap_swap_q8]
  have hoff : ∀ (y : QuaternionGroup 2) (r : α), r ∉ Set.range P → q y r ∉ Set.range P := by
    rintro y r hr ⟨x, hx⟩
    apply hr
    refine ⟨y⁻¹ * x, ?_⟩
    simp only [hPdef] at hx ⊢
    rw [← q8_apply_apply, hx, ← Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Perm.one_apply]
  have hσo : ∀ r, r ∉ Set.range P → σ r = r := by
    intro r hr
    have hne : ∀ y, r ≠ P y := fun y h => hr ⟨y, h.symm⟩
    rw [hσdef, Perm.mul_apply, swap_apply_of_ne_of_ne (hne _) (hne _),
      swap_apply_of_ne_of_ne (hne _) (hne _)]
  have hσio : ∀ r, r ∉ Set.range P → σ⁻¹ r = r := fun r hr => by
    rw [Perm.inv_eq_iff_eq, hσo r hr]
  set v : Perm α := σ * q (xa 0) * σ⁻¹ with hvdef
  have hvP : ∀ x, v (P x) = P (wit x) := fun x => by
    rw [hvdef, Perm.mul_apply, Perm.mul_apply, hσiP]
    simp only [hPdef]
    rw [q8_apply_apply]
    exact hσP _
  have hvo : ∀ r, r ∉ Set.range P → v r = q (xa 0) r := fun r hr => by
    rw [hvdef, Perm.mul_apply, Perm.mul_apply, hσio r hr, hσo _ (hoff _ r hr)]
  have hsign : sign σ = 1 := by
    have h1 : P 1 ≠ P (a 1) := hP.ne (by decide)
    have h2 : P (xa 0) ≠ P (xa 1) := hP.ne (by decide)
    rw [hσdef, Perm.sign_mul, Perm.sign_swap h1, Perm.sign_swap h2]
    exact Int.units_mul_self _
  have hcomm : v * q (a 2) = q (a 2) * v := by
    ext r
    show v (q (a 2) r) = q (a 2) (v r)
    by_cases hr : r ∈ Set.range P
    · obtain ⟨x, rfl⟩ := hr
      have e1 : q (a 2) (P x) = P (a 2 * x) := q8_apply_apply q _ _ _
      have e2 : q (a 2) (P (wit x)) = P (a 2 * wit x) := q8_apply_apply q _ _ _
      rw [e1, hvP, hvP, e2, wit_comm]
    · rw [hvo r hr, hvo _ (hoff _ r hr), q8_apply_apply, q8_apply_apply,
        show xa 0 * a 2 = a 2 * (xa 0 : QuaternionGroup 2) by decide]
  have hnl : ∀ (w : Perm α) (z : QuaternionGroup 2), w * v = v * q (a 1) →
      ¬ ∀ y, w (q y p) = q (z * y) p := by
    intro w z hw hall
    obtain ⟨x, hx⟩ := wit_not_left z
    apply hx
    apply hP
    have h1 : w (v (P x)) = v (q (a 1) (P x)) := by
      rw [← Perm.mul_apply, hw, Perm.mul_apply]
    have e1 : q (a 1) (P x) = P (a 1 * x) := q8_apply_apply q _ _ _
    rw [hvP, e1, hvP] at h1
    exact (hall (wit x)).symm.trans h1
  exact ⟨σ, hsign, hcomm, hnl⟩

theorem exists_perm_embedding {Y : Type*} [Group Y] {N : Subgroup Y} [N.Normal] {m : ℕ}
    (hm : 5 ≤ m) (hm6 : m ≠ 6) (e : ↥N ≃* alternatingGroup (Fin m))
    (hC : Subgroup.centralizer (N : Set Y) = ⊥) :
    ∃ ι : Y →* Perm (Fin m), Function.Injective ι ∧
      ∀ x : ↥N, ι (x : Y) = (e x : Perm (Fin m)) := by
  have hbij : Function.Bijective (MulAut.conjNormal (H := alternatingGroup (Fin m)) :
      Perm (Fin m) →* MulAut (alternatingGroup (Fin m))) :=
    CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m hm hm6
  let c : Perm (Fin m) ≃* MulAut (alternatingGroup (Fin m)) := MulEquiv.ofBijective _ hbij
  let g : Y →* MulAut ↥N := MulAut.conjNormal
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : y ∈ Subgroup.centralizer (N : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have := congrArg (fun α : MulAut ↥N => ((α ⟨b, hb⟩ : ↥N) : Y)) hy
      simp only [g, MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc b * y = (y * b * y⁻¹) * y := by rw [this]
        _ = y * b := by group
    rw [hC, Subgroup.mem_bot] at h1
    exact h1
  refine ⟨c.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp g),
    c.symm.injective.comp ((MulAut.congr e).injective.comp hg), fun x => ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [MulEquiv.symm_apply_eq]
  ext b
  have h1 : (MulAut.conjNormal (x : Y) (e.symm b) : ↥N) = x * e.symm b * x⁻¹ :=
    Subtype.ext (by rw [MulAut.conjNormal_apply]; rfl)
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, g, h1, map_mul, map_inv,
    MulEquiv.apply_symm_apply, c, MulEquiv.ofBijective_apply, MulAut.conjNormal_apply]
  rfl

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.Alt
