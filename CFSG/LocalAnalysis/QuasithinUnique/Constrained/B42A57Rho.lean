module

public import CFSG.Quasithin.Background.FFStarTransport
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.QuasithinUnique.B42A57

open CFSG.Quasithin Equiv

variable {S : Type} [CommGroup S]

theorem fixV_map_conj (X : Subgroup (MulAut S)) (g : MulAut S) :
    fixV (X.map (MulAut.conj g).toMonoidHom) = (fixV X).map (g : S ≃* S).toMonoidHom :=
  fixV_map_conj_eq X g

theorem card_fixV_map_conj (X : Subgroup (MulAut S)) (g : MulAut S) :
    Nat.card (fixV (X.map (MulAut.conj g).toMonoidHom)) = Nat.card (fixV X) := by
  rw [fixV_map_conj]
  exact Subgroup.card_map_of_injective (g : S ≃* S).injective

theorem card_map_conj (X : Subgroup (MulAut S)) (g : MulAut S) :
    Nat.card (X.map (MulAut.conj g).toMonoidHom) = Nat.card X :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem isFFStarOffender_conj {G A : Subgroup (MulAut S)} (h : IsFFStarOffender G A)
    {g : MulAut S} (hg : g ∈ G) :
    IsFFStarOffender G (A.map (MulAut.conj g).toMonoidHom) :=
  isFFStarOffender_map_conj h hg

theorem isMinOff_conj {G A : Subgroup (MulAut S)} (h : IsFFStarOffender G A)
    (hmin : ∀ B : Subgroup (MulAut S), IsFFStarOffender G B → Nat.card A ≤ Nat.card B)
    {g : MulAut S} (hg : g ∈ G) :
    IsFFStarOffender G (A.map (MulAut.conj g).toMonoidHom) ∧
      ∀ B : Subgroup (MulAut S), IsFFStarOffender G B →
        Nat.card (A.map (MulAut.conj g).toMonoidHom) ≤ Nat.card B := by
  refine ⟨isFFStarOffender_conj h hg, fun B hB => ?_⟩
  rw [card_map_conj]
  exact hmin B hB

@[expose] def conjE (σ : Perm (Fin 7)) (E : Subgroup (Perm (Fin 7))) : Subgroup (Perm (Fin 7)) :=
  E.map (MulAut.conj σ).toMonoidHom

theorem mem_conjE {σ : Perm (Fin 7)} {E : Subgroup (Perm (Fin 7))} {x : Perm (Fin 7)} :
    x ∈ conjE σ E ↔ σ⁻¹ * x * σ ∈ E := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    show σ⁻¹ * (σ * y * σ⁻¹) * σ ∈ E
    have : σ⁻¹ * (σ * y * σ⁻¹) * σ = y := by group
    rw [this]
    exact hy
  · intro hx
    refine ⟨σ⁻¹ * x * σ, hx, ?_⟩
    show σ * (σ⁻¹ * x * σ) * σ⁻¹ = x
    group

theorem card_conjE (σ : Perm (Fin 7)) (E : Subgroup (Perm (Fin 7))) :
    Nat.card (conjE σ E) = Nat.card E :=
  Subgroup.card_map_of_injective (MulAut.conj σ).injective

@[expose] def Cs (ρ : Perm (Fin 7) →* MulAut S) (E : Subgroup (Perm (Fin 7))) : Subgroup S :=
  fixV (E.map ρ)

variable (ρ : Perm (Fin 7) →* MulAut S)

theorem mem_Cs {E : Subgroup (Perm (Fin 7))} {v : S} : v ∈ Cs ρ E ↔ ∀ x ∈ E, ρ x v = v := by
  unfold Cs
  rw [mem_fixV]
  constructor
  · intro h x hx
    exact h (ρ x) (Subgroup.mem_map_of_mem ρ hx)
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    exact h x hx

theorem Cs_anti {E E' : Subgroup (Perm (Fin 7))} (h : E ≤ E') : Cs ρ E' ≤ Cs ρ E :=
  fun _ hv => (mem_Cs ρ).2 fun x hx => (mem_Cs ρ).1 hv x (h hx)

theorem mem_Cs_closure {X : Set (Perm (Fin 7))} {v : S} :
    v ∈ Cs ρ (Subgroup.closure X) ↔ ∀ x ∈ X, ρ x v = v := by
  constructor
  · intro h x hx
    exact (mem_Cs ρ).1 h x (Subgroup.subset_closure hx)
  · intro h
    refine (mem_Cs ρ).2 fun x hx => ?_
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact h x hx
    | one => simp
    | mul x y _ _ hx hy => rw [map_mul, MulAut.mul_apply, hy, hx]
    | inv x _ hx =>
      have := congrArg (fun w => (ρ x)⁻¹ w) hx
      simpa [map_inv] using this.symm

theorem mem_Cs_conj (σ : Perm (Fin 7)) (E : Subgroup (Perm (Fin 7))) {v : S} :
    v ∈ Cs ρ (conjE σ E) ↔ (ρ σ)⁻¹ v ∈ Cs ρ E := by
  rw [mem_Cs, mem_Cs]
  constructor
  · intro h y hy
    have := h (σ * y * σ⁻¹) (mem_conjE.2 (by
      have e : σ⁻¹ * (σ * y * σ⁻¹) * σ = y := by group
      rw [e]; exact hy))
    rw [map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply] at this
    have h2 := congrArg (fun w => (ρ σ)⁻¹ w) this
    simpa [MulAut.mul_apply] using h2
  · intro h x hx
    have hy := h (σ⁻¹ * x * σ) (mem_conjE.1 hx)
    have e : x = σ * (σ⁻¹ * x * σ) * σ⁻¹ := by group
    rw [e]
    simp only [map_mul, map_inv, MulAut.mul_apply]
    have : (ρ σ) ((ρ (σ⁻¹ * x * σ)) ((ρ σ)⁻¹ v)) = v := by
      rw [hy]; simp
    simpa [map_mul, map_inv, MulAut.mul_apply] using this

theorem card_Cs_conj (σ : Perm (Fin 7)) (E : Subgroup (Perm (Fin 7))) :
    Nat.card (Cs ρ (conjE σ E)) = Nat.card (Cs ρ E) := by
  refine Nat.card_congr
    { toFun := fun v => ⟨(ρ σ)⁻¹ v, (mem_Cs_conj ρ σ E).1 v.2⟩
      invFun := fun w => ⟨ρ σ w, (mem_Cs_conj ρ σ E).2 (by simp)⟩
      left_inv := fun v => Subtype.ext (by simp)
      right_inv := fun w => Subtype.ext (by simp) }

section Klein

variable {x y : Perm (Fin 7)} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x)

include hx hy hxy

theorem klein_mul_mem {a b : Perm (Fin 7)} (ha : a ∈ ({1, x, y, x * y} : Set (Perm (Fin 7))))
    (hb : b ∈ ({1, x, y, x * y} : Set (Perm (Fin 7)))) :
    a * b ∈ ({1, x, y, x * y} : Set (Perm (Fin 7))) := by
  have p_yx : y * x = x * y := hxy.symm
  have p_x_xy : x * (x * y) = y := by rw [← mul_assoc, hx, one_mul]
  have p_y_xy : y * (x * y) = x := by rw [← mul_assoc, ← hxy, mul_assoc, hy, mul_one]
  have p_xy_x : x * y * x = y := by rw [mul_assoc, ← hxy, ← mul_assoc, hx, one_mul]
  have p_xy_y : x * y * y = x := by rw [mul_assoc, hy, mul_one]
  have p_xy_xy : x * y * (x * y) = 1 := by rw [mul_assoc, p_y_xy, hx]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    simp [hx, hy, p_yx, p_x_xy, p_y_xy, p_xy_x, p_xy_y, p_xy_xy]

@[expose] def kleinSub : Subgroup (Perm (Fin 7)) where
  carrier := {1, x, y, x * y}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => klein_mul_mem hx hy hxy ha hb
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
    rcases ha with rfl | rfl | rfl | rfl
    · simp
    · simp [hxi]
    · simp [hyi]
    · right; right; right
      rw [mul_inv_rev, hxi, hyi, ← hxy]

theorem mem_kleinSub {a : Perm (Fin 7)} :
    a ∈ kleinSub hx hy hxy ↔ a = 1 ∨ a = x ∨ a = y ∨ a = x * y := by
  show a ∈ ({1, x, y, x * y} : Set (Perm (Fin 7))) ↔ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

theorem closure_pair_eq : Subgroup.closure ({x, y} : Set (Perm (Fin 7))) = kleinSub hx hy hxy := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro a ha
    rcases ha with rfl | rfl
    · exact (mem_kleinSub hx hy hxy).2 (Or.inr (Or.inl rfl))
    · exact (mem_kleinSub hx hy hxy).2 (Or.inr (Or.inr (Or.inl rfl)))
  · intro a ha
    rcases (mem_kleinSub hx hy hxy).1 ha with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

theorem card_closure_pair (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) :
    Nat.card (Subgroup.closure ({x, y} : Set (Perm (Fin 7)))) = 4 := by
  rw [closure_pair_eq hx hy hxy]
  have h1 : Nat.card (kleinSub hx hy hxy) = (({1, x, y, x * y} : Set (Perm (Fin 7))).ncard) :=
    Nat.card_coe_set_eq _
  rw [h1]
  have hxy1 : x * y ≠ 1 := fun h => hne (by
    have h1 : x⁻¹ = y := inv_eq_of_mul_eq_one_right h
    have h2 : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    rw [← h2, h1])
  have hxxy : x ≠ x * y := fun h => hy1 (by simpa using h)
  have hyxy : y ≠ x * y := fun h => hx1 (by simpa using h)
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hyxy]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne, hxxy⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hx1.symm, hy1.symm, hxy1.symm⟩

end Klein

theorem closure_single_eq {x : Perm (Fin 7)} (hx : x * x = 1) :
    (Subgroup.closure ({x} : Set (Perm (Fin 7))) : Set (Perm (Fin 7))) = {1, x} := by
  ext a
  constructor
  · intro ha
    have : Subgroup.closure ({x} : Set (Perm (Fin 7))) = Subgroup.zpowers x :=
      (Subgroup.zpowers_eq_closure x).symm
    rw [SetLike.mem_coe, this, Subgroup.mem_zpowers_iff] at ha
    obtain ⟨k, rfl⟩ := ha
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      have : k = 2 * (k / 2) := by omega
      rw [this, zpow_mul, zpow_two, hx, one_zpow]
    · right
      have hk : k = 2 * (k / 2) + 1 := by omega
      have : x ^ k = x := by
        rw [hk, zpow_add, zpow_mul, zpow_two, hx, one_zpow, one_mul, zpow_one]
      rw [this]
      exact Set.mem_singleton x
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.subset_closure (by simp)

theorem card_closure_single {x : Perm (Fin 7)} (hx : x * x = 1) (hx1 : x ≠ 1) :
    Nat.card (Subgroup.closure ({x} : Set (Perm (Fin 7)))) = 2 := by
  have h1 : Nat.card (Subgroup.closure ({x} : Set (Perm (Fin 7)))) =
      (((Subgroup.closure ({x} : Set (Perm (Fin 7))) : Subgroup (Perm (Fin 7))) :
        Set (Perm (Fin 7))).ncard) := Nat.card_coe_set_eq _
  rw [h1, closure_single_eq hx, Set.ncard_pair hx1.symm]

end CFSG.QuasithinUnique.B42A57
