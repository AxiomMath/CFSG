module

public import CFSG.LocalAnalysis.AGLEmbedding.OddCorePieces

public section

namespace CFSG.AGLEmbedding

open Subgroup

theorem fin_three_eq_or (i j : Fin 3) : j = i ∨ j = i + 1 ∨ j = i + 2 := by
  revert i j
  decide

theorem fin_three_rotate (i : Fin 3) : ∃ k : Fin 3, 1 - k = i ∧ 2 - k = i + 1 ∧ 0 - k = i + 2 := by
  revert i
  decide

section Planes

variable {A : Type*} [CommGroup A] (c : Fin 3 → A)

@[expose] def coordPlane (i : Fin 3) : Subgroup A :=
  closure {c (i + 1), c (i + 2)}

theorem mem_coordPlane_one (i : Fin 3) : c (i + 1) ∈ coordPlane c i :=
  subset_closure (Set.mem_insert _ _)

theorem mem_coordPlane_two (i : Fin 3) : c (i + 2) ∈ coordPlane c i :=
  subset_closure (Set.mem_insert_of_mem _ rfl)

theorem coordPlane_le_iff {i : Fin 3} {F : Subgroup A} :
    coordPlane c i ≤ F ↔ c (i + 1) ∈ F ∧ c (i + 2) ∈ F := by
  rw [coordPlane, closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  rfl

theorem coordPlane_sup_zpowers (hAc : closure (Set.range c) = ⊤) (i : Fin 3) :
    coordPlane c i ⊔ zpowers (c i) = ⊤ := by
  rw [eq_top_iff, ← hAc, closure_le]
  rintro _ ⟨j, rfl⟩
  rcases fin_three_eq_or i j with rfl | rfl | rfl
  · exact mem_sup_right (mem_zpowers _)
  · exact mem_sup_left (mem_coordPlane_one c _)
  · exact mem_sup_left (mem_coordPlane_two c _)

variable [Finite A]

omit [Finite A] in
theorem card_sup_le_mul [Finite A] (H K : Subgroup A) :
    Nat.card (H ⊔ K : Subgroup A) ≤ Nat.card H * Nat.card K := by
  have h := Set.natCard_mul_le (s := (H : Set A)) (t := (K : Set A))
  rw [← Subgroup.normal_mul] at h
  exact h

omit [Finite A] in
theorem card_zpowers_le_five (hA : ∀ a : A, a ^ 5 = 1) (a : A) : Nat.card (zpowers a) ≤ 5 := by
  rw [Nat.card_zpowers]
  exact orderOf_le_of_pow_eq_one (by norm_num) (hA a)

theorem card_coordPlane_le (hA : ∀ a : A, a ^ 5 = 1) (i : Fin 3) :
    Nat.card (coordPlane c i) ≤ 25 := by
  rw [coordPlane, Set.insert_eq, Subgroup.closure_union, ← zpowers_eq_closure,
    ← zpowers_eq_closure]
  exact (card_sup_le_mul _ _).trans
    (Nat.mul_le_mul (card_zpowers_le_five hA _) (card_zpowers_le_five hA _))

theorem card_coordPlane (hA : ∀ a : A, a ^ 5 = 1) (hAc : closure (Set.range c) = ⊤)
    (hAcard : Nat.card A = 5 ^ 3) (i : Fin 3) : Nat.card (coordPlane c i) = 25 := by
  have h1 := card_coordPlane_le c hA i
  have h2 : Nat.card A ≤ Nat.card (coordPlane c i) * 5 := by
    calc Nat.card A = Nat.card (⊤ : Subgroup A) := Subgroup.card_top.symm
      _ = Nat.card (coordPlane c i ⊔ zpowers (c i) : Subgroup A) := by
        rw [coordPlane_sup_zpowers c hAc]
      _ ≤ _ := (card_sup_le_mul _ _).trans (Nat.mul_le_mul_left _ (card_zpowers_le_five hA _))
  rw [hAcard] at h2
  omega

omit [Finite A] in
theorem card_eq_of_index_eq_five (hAcard : Nat.card A = 5 ^ 3) {F : Subgroup A}
    (hF : F.index = 5) : Nat.card F = 25 := by
  have h := F.card_mul_index
  rw [hF, hAcard] at h
  omega

theorem index_coordPlane (hA : ∀ a : A, a ^ 5 = 1) (hAc : closure (Set.range c) = ⊤)
    (hAcard : Nat.card A = 5 ^ 3) (i : Fin 3) : (coordPlane c i).index = 5 := by
  have h := (coordPlane c i).card_mul_index
  rw [card_coordPlane c hA hAc hAcard, hAcard] at h
  omega

theorem eq_coordPlane (hA : ∀ a : A, a ^ 5 = 1) (hAc : closure (Set.range c) = ⊤)
    (hAcard : Nat.card A = 5 ^ 3) {F : Subgroup A} (hF : F.index = 5) {i : Fin 3}
    (h1 : c (i + 1) ∈ F) (h2 : c (i + 2) ∈ F) : F = coordPlane c i := by
  refine (eq_of_le_of_card_ge ((coordPlane_le_iff c).mpr ⟨h1, h2⟩) ?_).symm
  rw [card_coordPlane c hA hAc hAcard, card_eq_of_index_eq_five hAcard hF]

theorem not_mem_coordPlane_self (hA : ∀ a : A, a ^ 5 = 1) (hAc : closure (Set.range c) = ⊤)
    (hAcard : Nat.card A = 5 ^ 3) (i : Fin 3) : c i ∉ coordPlane c i := fun h => by
  have htop := coordPlane_sup_zpowers c hAc i
  rw [sup_eq_left.mpr (zpowers_le.mpr h)] at htop
  have hi := index_coordPlane c hA hAc hAcard i
  rw [htop, index_top] at hi
  norm_num at hi

omit [Finite A] in
theorem mem_coordPlane_of_ne {i j : Fin 3} (hij : j ≠ i) : c j ∈ coordPlane c i := by
  rcases fin_three_eq_or i j with rfl | rfl | rfl
  · exact absurd rfl hij
  · exact mem_coordPlane_one c i
  · exact mem_coordPlane_two c i

theorem coordPlane_injective (hA : ∀ a : A, a ^ 5 = 1) (hAc : closure (Set.range c) = ⊤)
    (hAcard : Nat.card A = 5 ^ 3) : Function.Injective (coordPlane c) := by
  intro i j hij
  by_contra hne
  have h := mem_coordPlane_of_ne c (Ne.symm hne : j ≠ i)
  rw [hij] at h
  exact not_mem_coordPlane_self c hA hAc hAcard j h

theorem eq_coordPlane_or_exists_not_mem (hA : ∀ a : A, a ^ 5 = 1)
    (hAc : closure (Set.range c) = ⊤) (hAcard : Nat.card A = 5 ^ 3) {F : Subgroup A}
    (hF : F.index = 5) :
    (∃ i, F = coordPlane c i) ∨ ∃ i, c i ∉ F ∧ ¬ (c (i + 1) ∈ F ∧ c (i + 2) ∈ F) := by
  by_contra h
  push Not at h
  obtain ⟨hne, himp⟩ := h
  obtain ⟨i, hi⟩ : ∃ i, c i ∉ F := by
    by_contra h'
    push Not at h'
    have htop : F = ⊤ := by
      rw [eq_top_iff, ← hAc, closure_le]
      rintro _ ⟨j, rfl⟩
      exact h' j
    rw [htop, index_top] at hF
    norm_num at hF
  obtain ⟨h1, h2⟩ := himp i hi
  exact hne i (eq_coordPlane c hA hAc hAcard hF h1 h2)

section Cycle

open Fin.NatCast

variable {α : MulAut A} (hα : ∀ i, α (c i) = c (i + 1))
include hα

omit [Finite A] in
theorem pow_apply_of_cycle (k : ℕ) (j : Fin 3) : (α ^ k) (c j) = c (j + (k : Fin 3)) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, hα, Nat.cast_succ, add_assoc]

omit [Finite A] in
theorem mem_map_pow_iff_of_cycle (F : Subgroup A) (k : ℕ) (j : Fin 3) :
    c j ∈ F.map (α ^ k).toMonoidHom ↔ c (j - (k : Fin 3)) ∈ F := by
  rw [mem_map_equiv, show (α ^ k).symm (c j) = c (j - (k : Fin 3)) by
    rw [MulEquiv.symm_apply_eq, pow_apply_of_cycle c hα, sub_add_cancel]]

omit [Finite A] in
theorem map_coordPlane_of_cycle (i : Fin 3) :
    (coordPlane c i).map α.toMonoidHom = coordPlane c (i + 1) := by
  rw [coordPlane, MonoidHom.map_closure, Set.image_pair, coordPlane]
  simp only [MulEquiv.coe_toMonoidHom, hα]
  rw [add_right_comm i 2 1]

omit [Finite A] in
theorem map_pow_coordPlane_of_cycle (k : ℕ) (i : Fin 3) :
    (coordPlane c i).map (α ^ k).toMonoidHom = coordPlane c (i + (k : Fin 3)) := by
  induction k with
  | zero =>
    ext a
    simp
  | succ k ih =>
    rw [pow_succ', map_mul_toMonoidHom, ih, map_coordPlane_of_cycle c hα, Nat.cast_succ,
      add_assoc]

omit [Finite A] in
theorem exists_map_pow_coordPlane_of_cycle (i j : Fin 3) :
    ∃ k : ℕ, (coordPlane c i).map (α ^ k).toMonoidHom = coordPlane c j :=
  ⟨(j - i).val, by rw [map_pow_coordPlane_of_cycle c hα, Fin.cast_val_eq_self, add_sub_cancel]⟩

omit [Finite A] in
theorem exists_pow_not_mem_of_cycle {F : Subgroup A} {i : Fin 3} (hi : c i ∉ F)
    (hi' : ¬ (c (i + 1) ∈ F ∧ c (i + 2) ∈ F)) :
    ∃ k : ℕ, c 1 ∉ F.map (α ^ k).toMonoidHom ∧
      ¬ (c 2 ∈ F.map (α ^ k).toMonoidHom ∧ c 0 ∈ F.map (α ^ k).toMonoidHom) := by
  obtain ⟨k, h1, h2, h0⟩ := fin_three_rotate i
  refine ⟨k.val, ?_⟩
  simp only [mem_map_pow_iff_of_cycle c hα, Fin.cast_val_eq_self, h1, h2, h0]
  exact ⟨hi, hi'⟩

end Cycle

section Diag

omit [Finite A] in
theorem mulAut_ext_of_closure (hAc : closure (Set.range c) = ⊤) {f f' : MulAut A}
    (h : ∀ i, f (c i) = f' (c i)) : f = f' := by
  have hle : closure (Set.range c) ≤ MonoidHom.eqLocus f.toMonoidHom f'.toMonoidHom := by
    rw [closure_le]
    rintro _ ⟨i, rfl⟩
    exact h i
  rw [hAc] at hle
  exact MulEquiv.ext fun a => hle (mem_top a)

omit [Finite A] in
theorem pow_four_eq_inv (hA : ∀ a : A, a ^ 5 = 1) (a : A) : a ^ 4 = a⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hA])

omit [Finite A] in
theorem five_dvd_of_zpow_mem {F : Subgroup A} {a : A} (ha : a ^ 5 = 1) (haF : a ∉ F) {n : ℤ}
    (hn : a ^ n ∈ F) : (5 : ℤ) ∣ n := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hq : orderOf (QuotientGroup.mk' F a) = 5 := by
    apply orderOf_eq_prime
    · rw [← map_pow, ha, map_one]
    · rwa [Ne, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have h1 : QuotientGroup.mk' F a ^ n = 1 := by
    rw [← map_zpow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hn
  rw [← orderOf_dvd_iff_zpow_eq_one, hq] at h1
  exact_mod_cast h1

omit [Finite A] in
theorem injective_map_pow_of_map_sq_ne {g : MulAut A} (hg4 : g ^ 4 = 1) {F : Subgroup A}
    (hF : F.map (g ^ 2).toMonoidHom ≠ F) :
    Function.Injective fun j : Fin 4 => F.map (g ^ (j : ℕ)).toMonoidHom := by
  have hstab : ∀ k : ℕ, F.map (g ^ k).toMonoidHom = F → F.map (g ^ (k + k)).toMonoidHom = F :=
    fun k hk => by rw [pow_add, map_mul_toMonoidHom, hk, hk]
  have h6 : g ^ 6 = g ^ 2 := by rw [show 6 = 4 + 2 from rfl, pow_add, hg4, one_mul]
  have key : ∀ i j : ℕ, i < j → j < 4 →
      F.map (g ^ i).toMonoidHom ≠ F.map (g ^ j).toMonoidHom := by
    intro i j hij hj h
    have hj' : g ^ j = g ^ i * g ^ (j - i) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hj', map_mul_toMonoidHom] at h
    have hk : F.map (g ^ (j - i)).toMonoidHom = F :=
      (map_injective (g ^ i).injective h).symm
    obtain h1 | h2 | h3 : j - i = 1 ∨ j - i = 2 ∨ j - i = 3 := by omega
    · rw [h1] at hk
      exact hF (hstab 1 hk)
    · rw [h2] at hk
      exact hF hk
    · rw [h3] at hk
      have h33 := hstab 3 hk
      rw [show 3 + 3 = 6 from rfl, h6] at h33
      exact hF h33
  intro i j hij
  by_contra hne
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
  · exact key i j h j.2 hij
  · exact key j i h i.2 hij.symm

variable {g : MulAut A} (hg : g (c 0) = c 0 ^ 2 ∧ g (c 1) = c 1 ∧ g (c 2) = c 2 ^ 2)
include hg

omit [Finite A] in
theorem sq_apply_of_diag (hA : ∀ a : A, a ^ 5 = 1) :
    (g ^ 2) (c 0) = (c 0)⁻¹ ∧ (g ^ 2) (c 1) = c 1 ∧ (g ^ 2) (c 2) = (c 2)⁻¹ := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [sq, MulAut.mul_apply]
  · rw [hg.1, map_pow, hg.1, ← pow_mul]
    exact pow_four_eq_inv hA _
  · rw [hg.2.1, hg.2.1]
  · rw [hg.2.2, map_pow, hg.2.2, ← pow_mul]
    exact pow_four_eq_inv hA _

omit [Finite A] in
theorem pow_four_of_diag (hA : ∀ a : A, a ^ 5 = 1) (hAc : closure (Set.range c) = ⊤) :
    g ^ 4 = 1 := by
  have h2 := sq_apply_of_diag c hg hA
  refine mulAut_ext_of_closure c hAc fun i => ?_
  rw [show g ^ 4 = g ^ 2 * g ^ 2 by rw [← pow_add], MulAut.mul_apply, MulAut.one_apply]
  fin_cases i <;> simp [h2.1, h2.2.1, h2.2.2]

omit [Finite A] in
theorem sq_apply_of_mem_coordPlane_one (hA : ∀ a : A, a ^ 5 = 1) {b : A}
    (hb : b ∈ coordPlane c 1) : (g ^ 2) b = b⁻¹ := by
  have h2 := sq_apply_of_diag c hg hA
  have hle : coordPlane c 1 ≤ MonoidHom.eqLocus (g ^ 2).toMonoidHom (invMonoidHom : A →* A) :=
    (coordPlane_le_iff c).mpr ⟨h2.2.2, h2.1⟩
  exact hle hb

theorem map_sq_ne_of_diag (hA : ∀ a : A, a ^ 5 = 1) (hAc : closure (Set.range c) = ⊤)
    (hAcard : Nat.card A = 5 ^ 3) {F : Subgroup A} (hF : F.index = 5) (h1 : c 1 ∉ F)
    (h20 : ¬ (c 2 ∈ F ∧ c 0 ∈ F)) : F.map (g ^ 2).toMonoidHom ≠ F := by
  intro hmap
  have hle : F ≤ coordPlane c 1 := by
    intro a ha
    obtain ⟨b, hb, y, hy, rfl⟩ := mem_sup.mp (coordPlane_sup_zpowers c hAc 1 ▸ mem_top a)
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
    have hga : (g ^ 2) (b * c 1 ^ n) ∈ F := by
      rw [← hmap]
      exact mem_map_of_mem _ ha
    rw [map_mul, map_zpow, sq_apply_of_mem_coordPlane_one c hg hA hb,
      (sq_apply_of_diag c hg hA).2.1] at hga
    have h2n : c 1 ^ (2 * n) ∈ F := by
      have hmul := mul_mem ha hga
      rwa [mul_mul_mul_comm, mul_inv_cancel, one_mul, ← zpow_add, ← two_mul] at hmul
    obtain ⟨m, hm⟩ : (5 : ℤ) ∣ n := by
      have := five_dvd_of_zpow_mem (hA (c 1)) h1 h2n
      omega
    rw [hm, zpow_mul, zpow_ofNat, hA, one_zpow, mul_one]
    exact hb
  have heq : F = coordPlane c 1 := eq_of_le_of_card_ge hle (by
    rw [card_coordPlane c hA hAc hAcard, card_eq_of_index_eq_five hAcard hF])
  refine h20 ⟨?_, ?_⟩ <;> rw [heq]
  · exact mem_coordPlane_one c 1
  · exact mem_coordPlane_two c 1

theorem injective_map_pow_of_diag (hA : ∀ a : A, a ^ 5 = 1) (hAc : closure (Set.range c) = ⊤)
    (hAcard : Nat.card A = 5 ^ 3) {F : Subgroup A} (hF : F.index = 5) (h1 : c 1 ∉ F)
    (h20 : ¬ (c 2 ∈ F ∧ c 0 ∈ F)) :
    Function.Injective fun j : Fin 4 => F.map (g ^ (j : ℕ)).toMonoidHom :=
  injective_map_pow_of_map_sq_ne (pow_four_of_diag c hg hA hAc)
    (map_sq_ne_of_diag c hg hA hAc hAcard hF h1 h20)

theorem map_coordPlane_zero_of_diag : (coordPlane c 0).map g.toMonoidHom = coordPlane c 0 := by
  have hle : (coordPlane c 0).map g.toMonoidHom ≤ coordPlane c 0 := by
    rw [map_le_iff_le_comap, coordPlane_le_iff]
    refine ⟨?_, ?_⟩
    · change g (c 1) ∈ coordPlane c 0
      rw [hg.2.1]
      exact mem_coordPlane_one c 0
    · change g (c 2) ∈ coordPlane c 0
      rw [hg.2.2]
      exact pow_mem (mem_coordPlane_two c 0) 2
  exact eq_of_le_of_card_ge hle (card_map_of_injective g.injective).ge

end Diag

end Planes

end CFSG.AGLEmbedding
