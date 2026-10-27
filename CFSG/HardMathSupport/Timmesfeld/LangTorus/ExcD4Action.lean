module

public import CFSG.RankThree.PartOne.KE6.E6LAct
public import CFSG.RankThree.PartOne.KD4T.Inj

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE6

instance instE6SubE6 : E6Sub .E6 :=
  have h : Tag.E6.rank ≤ Tag.E6.rank := le_rfl
  ⟨h, fun k l => sub_eq_zero.1 ((by decide +revert : ∀ (h : Tag.E6.rank ≤ Tag.E6.rank)
    (k l : Fin Tag.E6.rank), Tag.E6.cartan (Fin.castLE h k) (Fin.castLE h l) -
      Tag.E6.cartan k l = 0) h k l), by decide +kernel, by decide +kernel,
    fun j i h1 h2 h3 => sub_zero (Tag.E6.cartan j i) ▸ (by decide :
      ∀ j i : Fin Tag.E6.rank, 1 ≤ j.val → j.val ≤ 4 → Tag.E6.rank ≤ i.val →
        Tag.E6.cartan j i - 0 = 0) j i h1 h2 h3⟩

@[expose] def D4Supp (a : Fin 36) : Prop := posRoot6 a 0 = 0 ∧ posRoot6 a 5 = 0

instance (a : Fin 36) : Decidable (D4Supp a) := by
  unfold D4Supp
  infer_instance

@[expose] def D4Leaves (a1 a2 a4 : Fin 36) : Prop :=
  (a1 = 4 ∧ a2 = 3 ∧ a4 = 1) ∨ (a1 = 4 ∧ a2 = 1 ∧ a4 = 3) ∨ (a1 = 3 ∧ a2 = 4 ∧ a4 = 1) ∨
    (a1 = 3 ∧ a2 = 1 ∧ a4 = 4) ∨ (a1 = 1 ∧ a2 = 4 ∧ a4 = 3) ∨ (a1 = 1 ∧ a2 = 3 ∧ a4 = 4)

instance (a1 a2 a4 : Fin 36) : Decidable (D4Leaves a1 a2 a4) := by
  unfold D4Leaves
  infer_instance

@[expose] def D4Gram (τ : Tag) [E6Sub τ] (a b : Fin 36) (i j : Fin Tag.E6.rank) : Prop :=
  iform (τ := τ) (e6Lat τ (posRoot6 a)) (e6Lat τ (posRoot6 b)) =
    iform (τ := τ) (Pi.single (e6Idx i) 1) (Pi.single (e6Idx j) 1)

instance (τ : Tag) [E6Sub τ] (a b : Fin 36) (i j : Fin Tag.E6.rank) :
    Decidable (D4Gram τ a b i j) := by
  unfold D4Gram
  infer_instance

@[expose] def D4Base4 (τ : Tag) [E6Sub τ] (a3 a1 a2 : Fin 36) : Prop :=
  ∀ a4 : Fin 36, D4Supp a4 → D4Gram τ a4 a3 4 3 → D4Gram τ a4 a1 4 1 → D4Gram τ a4 a2 4 2 →
    a3 = 2 ∧ D4Leaves a1 a2 a4

instance (τ : Tag) [E6Sub τ] (a3 a1 a2 : Fin 36) : Decidable (D4Base4 τ a3 a1 a2) := by
  unfold D4Base4
  infer_instance

@[expose] def D4Base3 (τ : Tag) [E6Sub τ] (a3 a1 : Fin 36) : Prop :=
  ∀ a2 : Fin 36, D4Supp a2 → D4Gram τ a2 a3 2 3 → D4Gram τ a2 a1 2 1 → D4Base4 τ a3 a1 a2

instance (τ : Tag) [E6Sub τ] (a3 a1 : Fin 36) : Decidable (D4Base3 τ a3 a1) := by
  unfold D4Base3
  infer_instance

@[expose] def D4Base2 (τ : Tag) [E6Sub τ] (a3 : Fin 36) : Prop :=
  ∀ a1 : Fin 36, D4Supp a1 → D4Gram τ a1 a3 1 3 → D4Base3 τ a3 a1

instance (τ : Tag) [E6Sub τ] (a3 : Fin 36) : Decidable (D4Base2 τ a3) := by
  unfold D4Base2
  infer_instance

@[expose] def D4BaseSearch (τ : Tag) [E6Sub τ] : Prop :=
  ∀ a3 : Fin 36, D4Supp a3 → D4Base2 τ a3

instance (τ : Tag) [E6Sub τ] : Decidable (D4BaseSearch τ) := by
  unfold D4BaseSearch
  infer_instance

theorem d4Base_E6 : D4BaseSearch .E6 := by decide +kernel

theorem d4Base_E7 : D4BaseSearch .E7 := by decide +kernel

theorem d4Base_E8 : D4BaseSearch .E8 := by decide +kernel


section Leaves

variable {τ : Tag} [E6Sub τ]

@[expose] def IsD4LeafPerm (σ : Equiv.Perm (Fin τ.rank)) : Prop :=
  σ = 1 ∨ σ = Equiv.swap (e6Idx 1) (e6Idx 2) ∨ σ = Equiv.swap (e6Idx 1) (e6Idx 4) ∨
    σ = Equiv.swap (e6Idx 2) (e6Idx 4) ∨ σ = List.formPerm [e6Idx 1, e6Idx 2, e6Idx 4] ∨
    σ = List.formPerm [e6Idx 1, e6Idx 4, e6Idx 2]

theorem e6Idx_ne {i j : Fin Tag.E6.rank} (h : i ≠ j) : e6Idx (τ := τ) i ≠ e6Idx j :=
  e6Idx_injective.ne h

theorem e6Idx_val' (k : Fin Tag.E6.rank) : (e6Idx (τ := τ) k).val = k.val := rfl

theorem e6Idx_mem_d4Set' (k : Fin Tag.E6.rank) (h1 : 1 ≤ k.val) (h4 : k.val ≤ 4) :
    e6Idx (τ := τ) k ∈ d4Set τ :=
  ⟨by rw [e6Idx_val']; exact h1, by rw [e6Idx_val']; exact h4⟩

theorem IsD4LeafPerm.apply_of_ne {σ : Equiv.Perm (Fin τ.rank)} (hσ : IsD4LeafPerm σ)
    {i : Fin τ.rank} (h1 : i ≠ e6Idx 1) (h2 : i ≠ e6Idx 2) (h4 : i ≠ e6Idx 4) : σ i = i := by
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact Equiv.swap_apply_of_ne_of_ne h1 h2
  · exact Equiv.swap_apply_of_ne_of_ne h1 h4
  · exact Equiv.swap_apply_of_ne_of_ne h2 h4
  · rw [List.formPerm_cons_cons, List.formPerm_pair, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne h2 h4, Equiv.swap_apply_of_ne_of_ne h1 h2]
  · rw [List.formPerm_cons_cons, List.formPerm_pair, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne h4 h2, Equiv.swap_apply_of_ne_of_ne h1 h4]

theorem IsD4LeafPerm.mem_d4Set {σ : Equiv.Perm (Fin τ.rank)} (hσ : IsD4LeafPerm σ)
    {i : Fin τ.rank} (hi : i ∈ d4Set τ) : σ i ∈ d4Set τ := by
  have h1 : e6Idx (τ := τ) 1 ∈ d4Set τ := e6Idx_mem_d4Set' 1 (by decide) (by decide)
  have h2 : e6Idx (τ := τ) 2 ∈ d4Set τ := e6Idx_mem_d4Set' 2 (by decide) (by decide)
  have h4 : e6Idx (τ := τ) 4 ∈ d4Set τ := e6Idx_mem_d4Set' 4 (by decide) (by decide)
  by_cases hi1 : i = e6Idx 1
  · subst hi1
    rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [List.formPerm_cons_cons, Equiv.swap_apply_of_ne_of_ne, e6Idx_ne, h1, h2, h4]
  by_cases hi2 : i = e6Idx 2
  · subst hi2
    rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [List.formPerm_cons_cons, Equiv.swap_apply_of_ne_of_ne, e6Idx_ne, h1, h2, h4]
  by_cases hi4 : i = e6Idx 4
  · subst hi4
    rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [List.formPerm_cons_cons, Equiv.swap_apply_of_ne_of_ne, e6Idx_ne, h1, h2, h4]
  rw [hσ.apply_of_ne hi1 hi2 hi4]
  exact hi

theorem IsD4LeafPerm.inv {σ : Equiv.Perm (Fin τ.rank)} (hσ : IsD4LeafPerm σ) :
    IsD4LeafPerm σ⁻¹ := by
  have h12 : e6Idx (τ := τ) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := τ) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := τ) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hc : List.formPerm [e6Idx (τ := τ) 1, e6Idx 2, e6Idx 4] *
      List.formPerm [e6Idx 1, e6Idx 4, e6Idx 2] = 1 := by
    refine Equiv.ext fun x => ?_
    simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one, Equiv.Perm.mul_apply,
      Equiv.Perm.one_apply]
    by_cases hx1 : x = e6Idx 1
    · subst hx1
      simp [Equiv.swap_apply_of_ne_of_ne, h12, h14]
    by_cases hx2 : x = e6Idx 2
    · subst hx2
      simp [Equiv.swap_apply_of_ne_of_ne, h12, h14]
    by_cases hx4 : x = e6Idx 4
    · subst hx4
      simp [Equiv.swap_apply_of_ne_of_ne, h24, h12.symm, h14.symm, h24.symm]
    rw [Equiv.swap_apply_of_ne_of_ne hx4 hx2, Equiv.swap_apply_of_ne_of_ne hx1 hx4,
      Equiv.swap_apply_of_ne_of_ne hx2 hx4, Equiv.swap_apply_of_ne_of_ne hx1 hx2]
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl inv_one
  · exact Or.inr (Or.inl (Equiv.swap_inv _ _))
  · exact Or.inr (Or.inr (Or.inl (Equiv.swap_inv _ _)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Equiv.swap_inv _ _))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (inv_eq_of_mul_eq_one_right hc)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_left hc)))))

theorem IsD4LeafPerm.eq_cycle {σ : Equiv.Perm (Fin τ.rank)} (hσ : IsD4LeafPerm σ)
    (h1 : σ ≠ 1) (h2 : σ * σ ≠ 1) :
    σ = List.formPerm [e6Idx 1, e6Idx 2, e6Idx 4] ∨
      σ = List.formPerm [e6Idx 1, e6Idx 4, e6Idx 2] := by
  rcases hσ with rfl | rfl | rfl | rfl | h | h
  · exact absurd rfl h1
  · exact absurd (Equiv.swap_mul_self _ _) h2
  · exact absurd (Equiv.swap_mul_self _ _) h2
  · exact absurd (Equiv.swap_mul_self _ _) h2
  · exact Or.inl h
  · exact Or.inr h

end Leaves

theorem posRoot6_d4 : posRoot6 4 = Pi.single 1 1 ∧ posRoot6 3 = Pi.single 2 1 ∧
    posRoot6 2 = Pi.single 3 1 ∧ posRoot6 1 = Pi.single 4 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext i <;> revert i <;> decide

section Action


variable {τ : Tag} [E6Sub τ]

theorem exists_posRoot6_of_mem_d4 {γ : Fin τ.rank → ℤ} (hγ : γ ∈ parabolicRoots τ (d4Set τ))
    (hpos : 0 < height γ) : ∃ a : Fin 36, D4Supp a ∧ e6Lat τ (posRoot6 a) = γ := by
  have hγ6 : γ ∈ parabolicRoots τ (e6Set τ) := ⟨hγ.1, fun i hi => hγ.2 i fun h => hi (by
    have := h.2
    change i.val < Tag.E6.rank
    have : Tag.E6.rank = 6 := rfl
    omega)⟩
  obtain ⟨γ', hγ', rfl⟩ := mem_parabolicRoots_e6Set_iff.1 hγ6
  rw [height_e6Lat'] at hpos
  obtain ⟨a, rfl⟩ := exists_posRoot6 hγ' hpos
  refine ⟨a, ⟨?_, ?_⟩, rfl⟩
  · have h0 := hγ.2 (e6Idx 0) (fun h => by
      have := h.1
      rw [e6Idx_val'] at this
      exact absurd this (by decide))
    rwa [e6Lat_apply_e6Idx] at h0
  · have h5 := hγ.2 (e6Idx 5) (fun h => by
      have := h.2
      rw [e6Idx_val'] at this
      exact absurd this (by decide))
    rwa [e6Lat_apply_e6Idx] at h5

theorem d4_base_of_pos (hsearch : D4BaseSearch τ) {v : WeylGroup τ} (hv : MapsJ τ (d4Set τ) v)
    (hpos : ∀ j ∈ d4Set τ, 0 < height (v • (Pi.single j 1 : Fin τ.rank → ℤ))) :
    ∃ σ : Equiv.Perm (Fin τ.rank), IsD4LeafPerm σ ∧
      ∀ j ∈ d4Set τ, v • (Pi.single j 1 : Fin τ.rank → ℤ) = Pi.single (σ j) 1 := by
  have hex : ∀ k : Fin Tag.E6.rank, 1 ≤ k.val → k.val ≤ 4 → ∃ a : Fin 36, D4Supp a ∧
      e6Lat τ (posRoot6 a) = v • (Pi.single (e6Idx k) 1 : Fin τ.rank → ℤ) := by
    intro k hk1 hk4
    have hkJ := e6Idx_mem_d4Set' (τ := τ) k hk1 hk4
    exact exists_posRoot6_of_mem_d4 (hv _ (single_mem_parabolicRoots hkJ)) (hpos _ hkJ)
  obtain ⟨a1, hs1, ha1⟩ := hex 1 (by decide) (by decide)
  obtain ⟨a2, hs2, ha2⟩ := hex 2 (by decide) (by decide)
  obtain ⟨a3, hs3, ha3⟩ := hex 3 (by decide) (by decide)
  obtain ⟨a4, hs4, ha4⟩ := hex 4 (by decide) (by decide)
  have hg : ∀ {a b : Fin 36} {i j : Fin Tag.E6.rank},
      e6Lat τ (posRoot6 a) = v • (Pi.single (e6Idx i) 1 : Fin τ.rank → ℤ) →
      e6Lat τ (posRoot6 b) = v • (Pi.single (e6Idx j) 1 : Fin τ.rank → ℤ) →
      D4Gram τ a b i j := by
    intro a b i j ha hb
    unfold D4Gram
    rw [ha, hb, iform_smul]
  obtain ⟨h3, hleaves⟩ := hsearch a3 hs3 a1 hs1 (hg ha1 ha3) a2 hs2 (hg ha2 ha3) (hg ha2 ha1)
    a4 hs4 (hg ha4 ha3) (hg ha4 ha1) (hg ha4 ha2)
  obtain ⟨p1, p2, p3, p4⟩ := posRoot6_d4
  have e1 : e6Lat τ (posRoot6 4) = Pi.single (e6Idx 1) 1 := by rw [p1, e6Lat_single]
  have e2 : e6Lat τ (posRoot6 3) = Pi.single (e6Idx 2) 1 := by rw [p2, e6Lat_single]
  have e3 : e6Lat τ (posRoot6 2) = Pi.single (e6Idx 3) 1 := by rw [p3, e6Lat_single]
  have e4 : e6Lat τ (posRoot6 1) = Pi.single (e6Idx 4) 1 := by rw [p4, e6Lat_single]
  subst h3
  rw [e3] at ha3
  have h12 : e6Idx (τ := τ) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := τ) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := τ) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h13 : e6Idx (τ := τ) 1 ≠ e6Idx 3 := e6Idx_ne (by decide)
  have h23 : e6Idx (τ := τ) 2 ≠ e6Idx 3 := e6Idx_ne (by decide)
  have h34 : e6Idx (τ := τ) 3 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hJ : ∀ j ∈ d4Set τ, j = e6Idx 1 ∨ j = e6Idx 2 ∨ j = e6Idx 3 ∨ j = e6Idx 4 := by
    intro j hj
    have h1 := hj.1
    have h4 := hj.2
    have hj6 : j.val < Tag.E6.rank := by
      have : Tag.E6.rank = 6 := rfl
      omega
    obtain ⟨k, rfl⟩ := exists_e6Idx_eq (τ := τ) hj6
    rw [e6Idx_val'] at h1 h4
    have hk : ∀ k : Fin Tag.E6.rank, 1 ≤ k.val → k.val ≤ 4 →
        k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by decide
    rcases hk k h1 h4 with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  rcases hleaves with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine ⟨1, Or.inl rfl, fun j hj => ?_⟩
    rcases hJ j hj with rfl | rfl | rfl | rfl
    · rw [← ha1, e1]; rfl
    · rw [← ha2, e2]; rfl
    · rw [← ha3]; rfl
    · rw [← ha4, e4]; rfl
  · refine ⟨Equiv.swap (e6Idx 2) (e6Idx 4), Or.inr (Or.inr (Or.inr (Or.inl rfl))), fun j hj => ?_⟩
    rcases hJ j hj with rfl | rfl | rfl | rfl
    · rw [← ha1, e1, Equiv.swap_apply_of_ne_of_ne h12 h14]
    · rw [← ha2, e4, Equiv.swap_apply_left]
    · rw [← ha3, Equiv.swap_apply_of_ne_of_ne h23.symm h34]
    · rw [← ha4, e2, Equiv.swap_apply_right]
  · refine ⟨Equiv.swap (e6Idx 1) (e6Idx 2), Or.inr (Or.inl rfl), fun j hj => ?_⟩
    rcases hJ j hj with rfl | rfl | rfl | rfl
    · rw [← ha1, e2, Equiv.swap_apply_left]
    · rw [← ha2, e1, Equiv.swap_apply_right]
    · rw [← ha3, Equiv.swap_apply_of_ne_of_ne h13.symm h23.symm]
    · rw [← ha4, e4, Equiv.swap_apply_of_ne_of_ne h14.symm h24.symm]
  · refine ⟨List.formPerm [e6Idx 1, e6Idx 2, e6Idx 4],
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), fun j hj => ?_⟩
    rcases hJ j hj with rfl | rfl | rfl | rfl <;>
      simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one, Equiv.Perm.mul_apply]
    · rw [← ha1, e2, Equiv.swap_apply_of_ne_of_ne h12 h14, Equiv.swap_apply_left]
    · rw [← ha2, e4, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne h14.symm h24.symm]
    · rw [← ha3, Equiv.swap_apply_of_ne_of_ne h23.symm h34, Equiv.swap_apply_of_ne_of_ne
        h13.symm h23.symm]
    · rw [← ha4, e1, Equiv.swap_apply_right, Equiv.swap_apply_right]
  · refine ⟨List.formPerm [e6Idx 1, e6Idx 4, e6Idx 2],
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), fun j hj => ?_⟩
    rcases hJ j hj with rfl | rfl | rfl | rfl <;>
      simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one, Equiv.Perm.mul_apply]
    · rw [← ha1, e4, Equiv.swap_apply_of_ne_of_ne h14 h12, Equiv.swap_apply_left]
    · rw [← ha2, e1, Equiv.swap_apply_right, Equiv.swap_apply_right]
    · rw [← ha3, Equiv.swap_apply_of_ne_of_ne h34 h23.symm, Equiv.swap_apply_of_ne_of_ne
        h13.symm h34]
    · rw [← ha4, e2, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne h12.symm h24]
  · refine ⟨Equiv.swap (e6Idx 1) (e6Idx 4), Or.inr (Or.inr (Or.inl rfl)), fun j hj => ?_⟩
    rcases hJ j hj with rfl | rfl | rfl | rfl
    · rw [← ha1, e4, Equiv.swap_apply_left]
    · rw [← ha2, e2, Equiv.swap_apply_of_ne_of_ne h12.symm h24]
    · rw [← ha3, Equiv.swap_apply_of_ne_of_ne h13.symm h34]
    · rw [← ha4, e1, Equiv.swap_apply_right]

theorem exists_d4_action (hsearch : D4BaseSearch τ) {w : WeylGroup τ}
    (hw : MapsJ τ (d4Set τ) w) :
    ∃ u ∈ parabolicWeylGroup τ (d4Set τ), ∃ w₀ : WeylGroup τ, w = u * w₀ ∧
      ∃ π : Equiv.Perm (Fin τ.rank), IsD4LeafPerm π ∧
        ∀ j ∈ d4Set τ, w₀ • (Pi.single j 1 : Fin τ.rank → ℤ) = Pi.single (π j) 1 := by
  obtain ⟨u, hu, w₀, hw₀, hm₀, hpos⟩ := exists_descent (d4Set τ) _ w rfl hw
  obtain ⟨σ, hσ, hact⟩ := d4_base_of_pos hsearch hm₀.inv hpos
  refine ⟨u, hu, w₀, hw₀, σ⁻¹, hσ.inv, fun j hj => ?_⟩
  have hj' : σ⁻¹ j ∈ d4Set τ := by
    by_contra hn
    have hne : ∀ k : Fin Tag.E6.rank, 1 ≤ k.val → k.val ≤ 4 → σ⁻¹ j ≠ e6Idx k :=
      fun k h1 h4 h => hn (h ▸ e6Idx_mem_d4Set' k h1 h4)
    have hfix := hσ.apply_of_ne (hne 1 (by decide) (by decide)) (hne 2 (by decide) (by decide))
      (hne 4 (by decide) (by decide))
    have hσσ : σ (σ⁻¹ j) = j := by simp
    rw [hσσ] at hfix
    exact hn (hfix ▸ hj)
  have h1 := hact _ hj'
  have hσσ : σ (σ⁻¹ j) = j := by simp
  rw [hσσ] at h1
  rw [← h1, smul_inv_smul]

end Action

theorem smul_eq_of_simple
    {τ : Tag} {J : Set (Fin τ.rank)} {w u : WeylGroup τ} {π : Equiv.Perm (Fin τ.rank)}
    (h : ∀ j ∈ J, w • (Pi.single j 1 : Fin τ.rank → ℤ) = u • (Pi.single (π j) 1))
    {α : Fin τ.rank → ℤ} (hα : ∀ i ∉ J, α i = 0) : w • α = u • permLattice π α := by
  rw [smul_eq_sum_smul_single w α, smul_eq_sum_smul_single u (permLattice π α)]
  rw [← Equiv.sum_comp π (fun j => permLattice π α j • (u • (Pi.single j 1 : Fin τ.rank → ℤ)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hp : permLattice π α (π j) = α j := by simp [permLattice]
  rw [hp]
  by_cases hj : j ∈ J
  · rw [h j hj]
  · rw [hα j hj, zero_smul, zero_smul]

end CFSG.HardMathSupport.Timmesfeld.LangTorus
