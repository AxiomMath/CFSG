module

public import CFSG.CharacterTheory.Wreathed.AdaptedBaseFusionOrbits

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.AdaptedBaseFusion

open CFSG.Wreathed CFSG.Wreathed.BrauerWong

variable {G : Type} [Group G] {n : ℕ} {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)} {σ υ g : G}
  (h : IsAdaptedBase (modelBase S e) (wreathModelHom S e (Original.a (2 ^ n)))
    (wreathModelHom S e (Original.z (2 ^ n))) σ υ g)
include h

@[expose] noncomputable def sixAut : Fin 6 → MulAut (modelBase S e) :=
  ![1, swapAut S e, h.aut, h.aut * h.aut, swapAut S e * h.aut, swapAut S e * (h.aut * h.aut)]

theorem sixAut_mem (k : Fin 6) : sixAut h k ∈ Subgroup.closure {swapAut S e, h.aut} := by
  have hα : swapAut S e ∈ Subgroup.closure {swapAut S e, h.aut} :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hβ : h.aut ∈ Subgroup.closure {swapAut S e, h.aut} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  fin_cases k
  · exact Subgroup.one_mem _
  · exact hα
  · exact hβ
  · exact Subgroup.mul_mem _ hβ hβ
  · exact Subgroup.mul_mem _ hα hβ
  · exact Subgroup.mul_mem _ hα (Subgroup.mul_mem _ hβ hβ)

theorem aut_aut_left : h.aut (h.aut h.left) = (h.left * h.right)⁻¹ := by
  rw [h.aut_left, h.aut_right]

theorem aut_aut_right : h.aut (h.aut h.right) = h.left := by
  rw [h.aut_right, map_inv, h.aut_left_mul_right, inv_inv]

theorem sixAut_left (k : Fin 6) :
    sixAut h k h.left = ![h.left, h.right, h.right, (h.left * h.right)⁻¹, h.left,
      (h.left * h.right)⁻¹] k := by
  fin_cases k
  · rfl
  · exact swapAut_left h
  · exact h.aut_left
  · exact aut_aut_left h
  · change swapAut S e (h.aut h.left) = h.left
    rw [h.aut_left, swapAut_right h]
  · change swapAut S e (h.aut (h.aut h.left)) = (h.left * h.right)⁻¹
    rw [aut_aut_left h, map_inv, swapAut_left_mul_right h]

theorem sixAut_right (k : Fin 6) :
    sixAut h k h.right = ![h.right, h.left, (h.left * h.right)⁻¹, h.left,
      (h.left * h.right)⁻¹, h.right] k := by
  fin_cases k
  · rfl
  · exact swapAut_right h
  · exact h.aut_right
  · exact aut_aut_right h
  · change swapAut S e (h.aut h.right) = (h.left * h.right)⁻¹
    rw [h.aut_right, map_inv, swapAut_left_mul_right h]
  · change swapAut S e (h.aut (h.aut h.right)) = h.right
    rw [aut_aut_right h, swapAut_left h]

theorem exists_sixAut_eq {φ : MulAut (modelBase S e)}
    (hφ : φ ∈ Subgroup.closure {swapAut S e, h.aut}) : ∃ k, sixAut h k = φ := by
  rcases mem_closure_swapAut_aut h hφ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩

variable [Finite G]

theorem isConj_iff_exists_sixAut (hn : 2 ≤ n) (x y : modelBase S e) :
    IsConj (x : G) (y : G) ↔ ∃ k, sixAut h k x = y := by
  rw [isConj_iff_exists h hn]
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    obtain ⟨k, rfl⟩ := exists_sixAut_eq h hφ
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨sixAut h k, sixAut_mem h k, rfl⟩

theorem left_ne_mul_inv (hn : 2 ≤ n) : h.left ≠ (h.left * h.right)⁻¹ := by
  intro heq
  have hR : h.right⁻¹ = h.left ^ 2 := by
    have h1 : h.left * (h.left * h.right) = 1 := by
      calc h.left * (h.left * h.right) = h.left * (h.left * h.right)⁻¹⁻¹ := by rw [inv_inv]
        _ = (h.left * h.right)⁻¹ * (h.left * h.right)⁻¹⁻¹ := by rw [← heq]
        _ = 1 := by rw [inv_inv, inv_mul_cancel]
    have h2 : h.left ^ 2 * h.right = 1 := by rw [pow_two, mul_assoc, h1]
    rw [eq_comm, ← mul_eq_one_iff_eq_inv]
    exact h2
  have hmem : h.right⁻¹ ∈ Subgroup.zpowers h.left ⊓ Subgroup.zpowers h.right :=
    ⟨hR ▸ Subgroup.npow_mem_zpowers _ 2, Subgroup.inv_mem _ (Subgroup.mem_zpowers _)⟩
  rw [zpowers_left_inf_right' h, Subgroup.mem_bot, inv_eq_one] at hmem
  have hord := orderOf_right' h
  rw [hmem, orderOf_one] at hord
  have : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

theorem right_ne_mul_inv (hn : 2 ≤ n) : h.right ≠ (h.left * h.right)⁻¹ := by
  intro heq
  have h2 := congrArg (swapAut S e) heq
  rw [swapAut_right h, map_inv, swapAut_left_mul_right h] at h2
  exact left_ne_mul_inv h hn h2

theorem sixAut_injective (hn : 2 ≤ n) : Function.Injective (sixAut h) := by
  have hLR := left_ne_right h (by omega)
  have hL := left_ne_mul_inv h hn
  have hR := right_ne_mul_inv h hn
  let f : Fin 3 → modelBase S e := ![h.left, h.right, (h.left * h.right)⁻¹]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact absurd hij hLR
      | exact absurd hij hL
      | exact absurd hij hR
      | exact absurd hij.symm hLR
      | exact absurd hij.symm hL
      | exact absurd hij.symm hR
  let p : Fin 6 → Fin 3 := ![0, 1, 1, 2, 0, 2]
  let q : Fin 6 → Fin 3 := ![1, 0, 2, 0, 2, 1]
  have hpq : Function.Injective (fun k => (p k, q k)) := by decide
  have hleft : ∀ k, sixAut h k h.left = f (p k) := by
    intro k
    rw [sixAut_left]
    fin_cases k <;> rfl
  have hright : ∀ k, sixAut h k h.right = f (q k) := by
    intro k
    rw [sixAut_right]
    fin_cases k <;> rfl
  intro k l hkl
  apply hpq
  have h1 : f (p k) = f (p l) := by rw [← hleft, ← hleft, hkl]
  have h2 : f (q k) = f (q l) := by rw [← hright, ← hright, hkl]
  exact Prod.ext (hf h1) (hf h2)

theorem sixAut_apply_injective (hn : 2 ≤ n) {x : modelBase S e} (hx : x ∉ h.exc) :
    Function.Injective (fun k => sixAut h k x) := by
  intro k l hkl
  apply sixAut_injective h hn
  have hmem : (sixAut h l)⁻¹ * sixAut h k ∈ Subgroup.closure {swapAut S e, h.aut} :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (sixAut_mem h l)) (sixAut_mem h k)
  have hfix : ((sixAut h l)⁻¹ * sixAut h k) x = x := by
    rw [MulAut.mul_apply]
    change (sixAut h l).symm ((sixAut h k) x) = x
    rw [show (sixAut h k) x = (sixAut h l) x from hkl, MulEquiv.symm_apply_apply]
  have h1 := eq_one_of_fixed_of_not_mem_exc h hn hmem hx hfix
  rw [inv_mul_eq_one] at h1
  exact h1.symm

omit [Finite G] in
theorem sixAut_mem_exc (k : Fin 6) {x : modelBase S e} (hx : x ∈ h.exc) : sixAut h k x ∈ h.exc :=
  mem_exc_of_mem_closure h (sixAut_mem h k) hx

theorem not_isConj_of_mem_exc (hn : 2 ≤ n) {x y : modelBase S e} (hx : x ∈ h.exc)
    (hy : y ∉ h.exc) : ¬ IsConj (x : G) (y : G) := by
  rw [isConj_iff_exists_sixAut h hn]
  rintro ⟨k, rfl⟩
  exact hy (sixAut_mem_exc h k hx)

omit [Finite G] in
theorem isConj_mul_zpow_left (k : ℤ) :
    IsConj (((h.left * h.right) ^ k : modelBase S e) : G)
      ((h.left ^ (-k) : modelBase S e) : G) := by
  refine isConj_iff.mpr ⟨g⁻¹, ?_⟩
  have h1 := h.aut_zpow_mul k
  have h2 := congrArg Subtype.val h1
  rw [IsAdaptedBase.aut, conjAut_apply_coe] at h2
  rw [← h2]
  group

omit [Finite G] in
theorem isConj_mul_zpow_right (k : ℤ) :
    IsConj (((h.left * h.right) ^ k : modelBase S e) : G)
      ((h.right ^ (-k) : modelBase S e) : G) := by
  refine (isConj_mul_zpow_left h k).trans (isConj_iff.mpr ⟨g⁻¹, ?_⟩)
  have h2 := congrArg Subtype.val (h.aut_zpow_left (-k))
  rw [IsAdaptedBase.aut, conjAut_apply_coe] at h2
  rw [← h2]
  group

theorem sum_isConj_of_not_mem_exc [Fintype (modelBase S e)] (hn : 2 ≤ n) {x : modelBase S e}
    (hx : x ∉ h.exc) (F : modelBase S e → ℂ) :
    ∑ y ∈ Finset.univ.filter (fun y : modelBase S e => IsConj (x : G) (y : G)), F y =
      ∑ k : Fin 6, F (sixAut h k x) := by
  have himage : Finset.univ.filter (fun y : modelBase S e => IsConj (x : G) (y : G)) =
      Finset.univ.image (fun k => sixAut h k x) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    exact isConj_iff_exists_sixAut h hn x y
  rw [himage, Finset.sum_image fun k _ l _ hkl => sixAut_apply_injective h hn hx hkl]

@[expose] noncomputable def tripleElt (k : ℕ) : Fin 3 → modelBase S e :=
  ![(h.left * h.right) ^ k, (h.left ^ k)⁻¹, (h.right ^ k)⁻¹]

omit [Finite G] in
theorem tripleElt_mem_zpowers (k : ℕ) :
    tripleElt h k 0 ∈ Subgroup.zpowers (h.left * h.right) ∧
      tripleElt h k 1 ∈ Subgroup.zpowers h.left ∧ tripleElt h k 2 ∈ Subgroup.zpowers h.right :=
  ⟨Subgroup.npow_mem_zpowers _ k, Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers _ k),
    Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers _ k)⟩

theorem tripleElt_ne_one {k : ℕ} (hk : k ∈ Finset.Ico 1 (2 ^ n)) (i : Fin 3) :
    tripleElt h k i ≠ 1 := by
  rw [Finset.mem_Ico] at hk
  have hk0 : k ≠ 0 := by omega
  fin_cases i
  · exact pow_ne_one_of_lt_orderOf hk0 (by rw [orderOf_mul' h]; exact hk.2)
  · change (h.left ^ k)⁻¹ ≠ 1
    rw [inv_ne_one]
    exact pow_ne_one_of_lt_orderOf hk0 (by rw [orderOf_left' h]; exact hk.2)
  · change (h.right ^ k)⁻¹ ≠ 1
    rw [inv_ne_one]
    exact pow_ne_one_of_lt_orderOf hk0 (by rw [orderOf_right' h]; exact hk.2)

theorem tripleElt_injOn :
    Set.InjOn (fun p : ℕ × Fin 3 => tripleElt h p.1 p.2)
      ((Finset.Ico 1 (2 ^ n) ×ˢ (Finset.univ : Finset (Fin 3))) : Set (ℕ × Fin 3)) := by
  rintro ⟨k, i⟩ hki ⟨l, j⟩ hlj hkl
  simp only [Set.mem_prod, Finset.mem_coe, Finset.mem_Ico] at hki hlj
  simp only at hkl
  obtain ⟨hk0, hk1, hk2⟩ := tripleElt_mem_zpowers h k
  obtain ⟨hl0, hl1, hl2⟩ := tripleElt_mem_zpowers h l
  have hne := tripleElt_ne_one h (Finset.mem_Ico.mpr hki.1) i
  have hbot : ∀ {K L : Subgroup (modelBase S e)} {x : modelBase S e}, K ⊓ L = ⊥ → x ∈ K →
      x ∈ L → x = 1 := by
    intro K L x hKL hxK hxL
    have hx : x ∈ K ⊓ L := ⟨hxK, hxL⟩
    rwa [hKL, Subgroup.mem_bot] at hx
  have hAB := zpowers_mul_inf_left h
  have hAC := zpowers_mul_inf_right h
  have hBC := zpowers_left_inf_right' h
  have hpowA : ∀ {k l : ℕ}, k < 2 ^ n → l < 2 ^ n →
      (h.left * h.right) ^ k = (h.left * h.right) ^ l → k = l := fun hk hl hkl =>
    pow_injOn_Iio_orderOf (by rw [orderOf_mul' h]; exact hk) (by rw [orderOf_mul' h]; exact hl)
      hkl
  have hpowB : ∀ {k l : ℕ}, k < 2 ^ n → l < 2 ^ n → h.left ^ k = h.left ^ l → k = l :=
    fun hk hl hkl =>
    pow_injOn_Iio_orderOf (by rw [orderOf_left' h]; exact hk) (by rw [orderOf_left' h]; exact hl)
      hkl
  have hpowC : ∀ {k l : ℕ}, k < 2 ^ n → l < 2 ^ n → h.right ^ k = h.right ^ l → k = l :=
    fun hk hl hkl =>
    pow_injOn_Iio_orderOf (by rw [orderOf_right' h]; exact hk)
      (by rw [orderOf_right' h]; exact hl) hkl
  fin_cases i <;> fin_cases j
  · exact Prod.ext (hpowA hki.1.2 hlj.1.2 hkl) rfl
  · exact absurd (hbot hAB hk0 (hkl ▸ hl1)) hne
  · exact absurd (hbot hAC hk0 (hkl ▸ hl2)) hne
  · exact absurd (hbot hAB (hkl ▸ hl0) hk1) hne
  · exact Prod.ext (hpowB hki.1.2 hlj.1.2 (inv_injective hkl)) rfl
  · exact absurd (hbot hBC hk1 (hkl ▸ hl2)) hne
  · exact absurd (hbot hAC (hkl ▸ hl0) hk2) hne
  · exact absurd (hbot hBC (hkl ▸ hl1) hk2) hne
  · exact Prod.ext (hpowC hki.1.2 hlj.1.2 (inv_injective hkl)) rfl

theorem mem_exc_iff (x : modelBase S e) :
    x ∈ h.exc ↔ x = 1 ∨ ∃ k ∈ Finset.Ico 1 (2 ^ n), ∃ i : Fin 3, tripleElt h k i = x := by
  have hm : 0 < 2 ^ n := Nat.two_pow_pos n
  constructor
  · intro hx
    rcases hx with (hx | hx) | hx
    · rw [SetLike.mem_coe, mem_zpowers_iff_mem_range_orderOf, orderOf_mul' h] at hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_range] at hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · exact Or.inl (pow_zero _)
      · exact Or.inr ⟨j, Finset.mem_Ico.mpr ⟨hj0, hj⟩, 0, rfl⟩
    · rw [SetLike.mem_coe, mem_zpowers_iff_mem_range_orderOf, orderOf_left' h] at hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_range] at hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · exact Or.inl (pow_zero _)
      · refine Or.inr ⟨2 ^ n - j, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, 1, ?_⟩
        change (h.left ^ (2 ^ n - j))⁻¹ = h.left ^ j
        have h1 := pow_orderOf_eq_one h.left
        rw [orderOf_left' h] at h1
        rw [inv_eq_iff_mul_eq_one, ← pow_add, Nat.sub_add_cancel hj.le, h1]
    · rw [SetLike.mem_coe, mem_zpowers_iff_mem_range_orderOf, orderOf_right' h] at hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_range] at hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · exact Or.inl (pow_zero _)
      · refine Or.inr ⟨2 ^ n - j, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, 2, ?_⟩
        change (h.right ^ (2 ^ n - j))⁻¹ = h.right ^ j
        have h1 := pow_orderOf_eq_one h.right
        rw [orderOf_right' h] at h1
        rw [inv_eq_iff_mul_eq_one, ← pow_add, Nat.sub_add_cancel hj.le, h1]
  · rintro (rfl | ⟨k, -, i, rfl⟩)
    · exact Or.inr (Subgroup.one_mem _)
    · obtain ⟨h0, h1, h2⟩ := tripleElt_mem_zpowers h k
      fin_cases i
      · exact Or.inl (Or.inl h0)
      · exact Or.inl (Or.inr h1)
      · exact Or.inr h2

theorem sum_split_exc [Fintype (modelBase S e)] (F : modelBase S e → ℂ) :
    ∑ x : modelBase S e, F x = F 1 + ∑ k ∈ Finset.Ico 1 (2 ^ n),
      (F ((h.left * h.right) ^ k) + F (h.left ^ k)⁻¹ + F (h.right ^ k)⁻¹) +
      ∑ x ∈ Finset.univ.filter (fun x : modelBase S e => x ∉ h.exc), F x := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : modelBase S e => x ∈ h.exc)]
  congr 1
  set T := (Finset.Ico 1 (2 ^ n) ×ˢ (Finset.univ : Finset (Fin 3))).image
    (fun p : ℕ × Fin 3 => tripleElt h p.1 p.2) with hT
  have h1T : (1 : modelBase S e) ∉ T := by
    intro h1
    obtain ⟨⟨k, i⟩, hki, hk⟩ := Finset.mem_image.mp h1
    exact tripleElt_ne_one h (Finset.mem_product.mp hki).1 i hk
  have hfilter : Finset.univ.filter (fun x : modelBase S e => x ∈ h.exc) = insert 1 T := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, hT,
      Finset.mem_image, Finset.mem_product, Prod.exists]
    rw [mem_exc_iff h]
    constructor
    · rintro (rfl | ⟨k, hk, i, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨k, i, ⟨hk, trivial⟩, rfl⟩
    · rintro (rfl | ⟨k, i, ⟨hk, -⟩, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨k, hk, i, rfl⟩
  rw [hfilter, Finset.sum_insert h1T, hT, Finset.sum_image (by
    rw [Finset.coe_product]
    exact tripleElt_injOn h), Finset.sum_product]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fin.sum_univ_three]
  rfl

end CFSG.Wreathed.AdaptedBaseFusion
