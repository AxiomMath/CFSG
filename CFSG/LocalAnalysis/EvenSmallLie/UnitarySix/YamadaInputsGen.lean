module

public import CFSG.LieType.Chevalley.E6GraphLeviUnitary

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaInputs

open Matrix Subgroup CFSG.LieType.Chevalley.E6GraphLevi

section Field

variable {F : Type} [Field F]

theorem rev_ne_self_fin6 (i : Fin 6) : Fin.rev i ≠ i := by
  revert i
  decide

theorem sl6_ext {A B : SpecialLinearGroup (Fin 6) F}
    (h : (A : Matrix (Fin 6) (Fin 6) F) = B) : A = B :=
  Subtype.ext h

theorem transvection_congr_fin6 {i j k l : Fin 6} (hij : i ≠ j) (hkl : k ≠ l) (hik : i = k)
    (hjl : j = l) (c : F) :
    SpecialLinearGroup.transvection hij c = SpecialLinearGroup.transvection hkl c := by
  subst hik hjl
  rfl

theorem transvection_mul_comm_fin6 {i j k l : Fin 6} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) (a b : F) :
    SpecialLinearGroup.transvection hij a * SpecialLinearGroup.transvection hkl b =
      SpecialLinearGroup.transvection hkl b * SpecialLinearGroup.transvection hij a := by
  apply sl6_ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe, mul_add,
    add_mul, one_mul, mul_one, single_mul_single_of_ne _ _ _ _ hjk,
    single_mul_single_of_ne _ _ _ _ hli, add_zero]
  abel

theorem transvection_mul_mem_unitarySL (h2 : (2 : F) = 0) {σ : F →+* F}
    (hσσ : ∀ c, σ (σ c) = c) {i j : Fin 6} (hij : i ≠ j) (a : F) :
    SpecialLinearGroup.transvection hij a *
        SpecialLinearGroup.transvection (Fin.rev_injective.ne hij.symm) (σ a) ∈
      unitarySL σ := by
  rw [mem_unitarySL_iff_unitaryTwist, unitaryTwist, MonoidHom.comp_apply, map_mul, map_mul,
    map_transvection, map_transvection, graphSL_transvection h2, graphSL_transvection h2, hσσ,
    transvection_congr_fin6 _ hij (Fin.rev_rev i) (Fin.rev_rev j)]
  exact transvection_mul_comm_fin6 _ _ (rev_ne_self_fin6 i) (rev_ne_self_fin6 j).symm _ _

theorem coe_conj_transvection_fin6 (g : SpecialLinearGroup (Fin 6) F) {k l : Fin 6} (hkl : k ≠ l)
    (c : F) :
    ((g * SpecialLinearGroup.transvection hkl c * g⁻¹ : SpecialLinearGroup (Fin 6) F) :
        Matrix (Fin 6) (Fin 6) F) =
      1 + (g : Matrix (Fin 6) (Fin 6) F) * single k l c *
        ((g⁻¹ : SpecialLinearGroup (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    SpecialLinearGroup.transvection_coe, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

def genMat (i j : Fin 6) (x p q r : F) : Matrix (Fin 6) (Fin 6) F :=
  1 + single j (Fin.rev j) x + single i (Fin.rev j) p + single j (Fin.rev i) q +
    single i (Fin.rev i) r

theorem coe_conj_eq_genMat (h2 : (2 : F) = 0) {i j : Fin 6} (hij : i ≠ j) (hji : j ≠ Fin.rev i)
    (a b c : F) :
    ((SpecialLinearGroup.transvection hij a *
        SpecialLinearGroup.transvection (Fin.rev_injective.ne hij.symm) b *
        SpecialLinearGroup.transvection (rev_ne_self_fin6 j).symm c *
        (SpecialLinearGroup.transvection hij a *
          SpecialLinearGroup.transvection (Fin.rev_injective.ne hij.symm) b)⁻¹ :
          SpecialLinearGroup (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      genMat i j c (a * c) (c * b) (a * c * b) := by
  have hii : i ≠ Fin.rev i := (rev_ne_self_fin6 i).symm
  have hjj : j ≠ Fin.rev j := (rev_ne_self_fin6 j).symm
  have hij' : i ≠ Fin.rev j := fun h => hji (by rw [h, Fin.rev_rev])
  rw [coe_conj_transvection_fin6, _root_.mul_inv_rev, SpecialLinearGroup.transvection_inv,
    SpecialLinearGroup.transvection_inv, neg_eq_self_of_two h2, neg_eq_self_of_two h2,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp only [SpecialLinearGroup.transvection_coe, Matrix.mul_add, Matrix.add_mul, Matrix.one_mul,
    Matrix.mul_one, single_mul_single_same, single_mul_single_of_ne, hii.symm, hjj, hji.symm,
    hij'.symm, ne_eq, not_false_eq_true, add_zero]
  rw [genMat]
  abel

theorem genMat_mul_genMat {i j : Fin 6} (hji : j ≠ Fin.rev i) (x p q r x' p' q' r' : F) :
    genMat i j x p q r * genMat i j x' p' q' r' =
      genMat i j (x + x') (p + p') (q + q') (r + r') := by
  have hii : i ≠ Fin.rev i := (rev_ne_self_fin6 i).symm
  have hjj : j ≠ Fin.rev j := (rev_ne_self_fin6 j).symm
  have hij' : i ≠ Fin.rev j := fun h => hji (by rw [h, Fin.rev_rev])
  simp only [genMat, Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one,
    single_mul_single_of_ne, hii.symm, hjj.symm, hji.symm, hij'.symm, ne_eq,
    not_false_eq_true, add_zero, single_add]
  abel

theorem coe_transvection_eq_genMat (i j : Fin 6) (t : F) :
    ((SpecialLinearGroup.transvection (rev_ne_self_fin6 j).symm t : SpecialLinearGroup (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F) = genMat i j t 0 0 0 := by
  simp only [SpecialLinearGroup.transvection_coe, genMat, single_zero, add_zero]

theorem genMat_eq_transvection_left {i j : Fin 6} (hji : j ≠ Fin.rev i) {x p q r c : F}
    (hx : x = 0) (hp : p = 0) (hq : q = c) (hr : r = 0) :
    genMat i j x p q r =
      ((SpecialLinearGroup.transvection hji c : SpecialLinearGroup (Fin 6) F) :
        Matrix (Fin 6) (Fin 6) F) := by
  subst hx hp hq hr
  simp only [genMat, SpecialLinearGroup.transvection_coe, single_zero, add_zero]

theorem genMat_eq_transvection_right (i j : Fin 6) {x p q r c : F}
    (hx : x = 0) (hp : p = 0) (hq : q = 0) (hr : r = c) :
    genMat i j x p q r =
      ((SpecialLinearGroup.transvection (rev_ne_self_fin6 i).symm c :
        SpecialLinearGroup (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by
  subst hx hp hq hr
  simp only [genMat, SpecialLinearGroup.transvection_coe, single_zero, add_zero]

def genConj (σ : F →+* F) {i j : Fin 6} (hij : i ≠ j) (a t : F) :
    SpecialLinearGroup (Fin 6) F :=
  SpecialLinearGroup.transvection hij a *
      SpecialLinearGroup.transvection (Fin.rev_injective.ne hij.symm) (σ a) *
      SpecialLinearGroup.transvection (rev_ne_self_fin6 j).symm t *
      (SpecialLinearGroup.transvection hij a *
        SpecialLinearGroup.transvection (Fin.rev_injective.ne hij.symm) (σ a))⁻¹

theorem genConj_mem (h2 : (2 : F) = 0) {σ : F →+* F} (hσσ : ∀ c, σ (σ c) = c)
    {M : Subgroup (SpecialLinearGroup (Fin 6) F)} (hM : unitarySL σ ≤ M) {i j : Fin 6}
    (hij : i ≠ j) (hX : ∀ t, SpecialLinearGroup.transvection (rev_ne_self_fin6 j).symm t ∈ M)
    (a t : F) : genConj σ hij a t ∈ M :=
  M.mul_mem (M.mul_mem (hM (transvection_mul_mem_unitarySL h2 hσσ hij a)) (hX t))
    (M.inv_mem (hM (transvection_mul_mem_unitarySL h2 hσσ hij a)))

theorem coe_conjElt (h2 : (2 : F) = 0) {σ : F →+* F} (hσ : ∀ c, σ c = c ^ 2) {i j : Fin 6}
    (hij : i ≠ j) (hji : j ≠ Fin.rev i) (a t : F) :
    (genConj σ hij a t : Matrix (Fin 6) (Fin 6) F) =
      genMat i j t (a * t) (t * a ^ 2) (a * t * a ^ 2) := by
  rw [genConj, coe_conj_eq_genMat h2 hij hji, hσ]

theorem transvection_mem_of_diag (h2 : (2 : F) = 0) {σ : F →+* F} (hσ : ∀ c, σ c = c ^ 2)
    (hσσ : ∀ c, σ (σ c) = c) {ω : F} (hω : ω ^ 2 + ω + 1 = 0)
    {M : Subgroup (SpecialLinearGroup (Fin 6) F)} (hM : unitarySL σ ≤ M) {i j : Fin 6}
    (hij : i ≠ j) (hji : j ≠ Fin.rev i)
    (hX : ∀ t, SpecialLinearGroup.transvection (rev_ne_self_fin6 j).symm t ∈ M) (c : F) :
    SpecialLinearGroup.transvection hji c ∈ M ∧
      SpecialLinearGroup.transvection (rev_ne_self_fin6 i).symm c ∈ M := by
  have hg := genConj_mem h2 hσσ hM hij hX
  constructor
  · have e : SpecialLinearGroup.transvection hji c =
        genConj σ hij 1 c * genConj σ hij ω (c * ω) * genConj σ hij (ω ^ 2) (c * ω ^ 2) := by
      apply sl6_ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        coe_conjElt h2 hσ hij hji, coe_conjElt h2 hσ hij hji, coe_conjElt h2 hσ hij hji,
        genMat_mul_genMat hji, genMat_mul_genMat hji]
      refine (genMat_eq_transvection_left hji ?_ ?_ ?_ ?_).symm
      · linear_combination c * hω
      · linear_combination c * (ω ^ 2 - ω + 1) * hω
      · linear_combination c * (ω - 1) * (ω ^ 3 + 2) * hω + c * h2
      · linear_combination c * (ω ^ 2 - ω + 1) * (ω ^ 4 - ω ^ 2 + 1) * hω
    rw [e]
    exact M.mul_mem (M.mul_mem (hg _ _) (hg _ _)) (hg _ _)
  · have e : SpecialLinearGroup.transvection (rev_ne_self_fin6 i).symm c =
        genConj σ hij 1 c * genConj σ hij ω c * genConj σ hij (ω ^ 2) c *
          SpecialLinearGroup.transvection (rev_ne_self_fin6 j).symm c := by
      apply sl6_ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul, coe_conjElt h2 hσ hij hji, coe_conjElt h2 hσ hij hji,
        coe_conjElt h2 hσ hij hji, coe_transvection_eq_genMat i j, genMat_mul_genMat hji,
        genMat_mul_genMat hji, genMat_mul_genMat hji]
      refine (genMat_eq_transvection_right i j ?_ ?_ ?_ ?_).symm
      · linear_combination 2 * c * h2
      · linear_combination c * hω
      · linear_combination c * (ω ^ 2 - ω + 1) * hω
      · linear_combination c * (ω - 1) * (ω ^ 3 + 2) * hω + c * h2
    rw [e]
    exact M.mul_mem (M.mul_mem (M.mul_mem (hg _ _) (hg _ _)) (hg _ _)) (hX c)

theorem two_eq_zero_of_card_eq_four [Finite F] (hF : Nat.card F = 4) : (2 : F) = 0 := by
  have : Fintype F := Fintype.ofFinite F
  have h := FiniteField.cast_card_eq_zero F
  rw [← Nat.card_eq_fintype_card, hF] at h
  have h4 : (2 : F) * 2 = 0 := by
    rw [← h]
    norm_num
  exact mul_self_eq_zero.mp h4

theorem pow_four_of_card_eq_four [Finite F] (hF : Nat.card F = 4) (x : F) : x ^ 4 = x := by
  have : Fintype F := Fintype.ofFinite F
  have h := FiniteField.pow_card x
  rwa [← Nat.card_eq_fintype_card, hF] at h

theorem exists_sq_add_self_add_one_eq_zero_of_card_eq_four [Finite F] (hF : Nat.card F = 4) :
    ∃ ω : F, ω ^ 2 + ω + 1 = 0 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨ω, hω⟩ : ∃ ω : F, ω ∉ ({0, 1} : Finset F) := by
    by_contra h
    push Not at h
    have h1 := Finset.card_le_card (fun x (_ : x ∈ (Finset.univ : Finset F)) => h x)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF] at h1
    have h3 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hω
  refine ⟨ω, ?_⟩
  have h : ω * (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination pow_four_of_card_eq_four hF ω
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact absurd h hω.1
    · exact absurd (sub_eq_zero.mp h) hω.2
  · exact h

end Field

theorem closure_unitarySL_transvection_eq_top {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) (σ : F →+* F) (hσ : ∀ c, σ c = c ^ 2) :
    closure ((unitarySL σ : Set (SpecialLinearGroup (Fin 6) F)) ∪
      Set.range (fun c : F =>
        SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 5 by decide) c)) = ⊤ := by
  set M := closure ((unitarySL σ : Set (SpecialLinearGroup (Fin 6) F)) ∪
      Set.range (fun c : F =>
        SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 5 by decide) c)) with hMdef
  have h2 := two_eq_zero_of_card_eq_four hF
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    rw [hσ, hσ, ← pow_mul]
    exact pow_four_of_card_eq_four hF c
  obtain ⟨ω, hω⟩ := exists_sq_add_self_add_one_eq_zero_of_card_eq_four hF
  have hM : unitarySL σ ≤ M := fun g hg => subset_closure (Or.inl hg)
  have h05 : ∀ t, SpecialLinearGroup.transvection (rev_ne_self_fin6 0).symm t ∈ M := fun t =>
    subset_closure (Or.inr ⟨t, rfl⟩)
  have h14 : ∀ t, SpecialLinearGroup.transvection (rev_ne_self_fin6 1).symm t ∈ M := fun t =>
    (transvection_mem_of_diag h2 hσ hσσ hω hM (i := 1) (j := 0) (by decide) (by decide)
      h05 t).2
  have hdiag : ∀ k : Fin 6, ∀ t,
      SpecialLinearGroup.transvection (rev_ne_self_fin6 k).symm t ∈ M := by
    intro k t
    fin_cases k
    · exact h05 t
    · exact h14 t
    · exact (transvection_mem_of_diag h2 hσ hσσ hω hM (i := 2) (j := 0) (by decide)
        (by decide) h05 t).2
    · exact (transvection_mem_of_diag h2 hσ hσσ hω hM (i := 3) (j := 0) (by decide)
        (by decide) h05 t).2
    · exact (transvection_mem_of_diag h2 hσ hσσ hω hM (i := 4) (j := 0) (by decide)
        (by decide) h05 t).2
    · exact (transvection_mem_of_diag h2 hσ hσσ hω hM (i := 5) (j := 1) (by decide)
        (by decide) h14 t).2
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 6) (K := F),
    closure_le]
  rintro _ ⟨k, l, hkl, c, rfl⟩
  by_cases hl : l = Fin.rev k
  · subst hl
    exact hdiag k c
  · have h := (transvection_mem_of_diag h2 hσ hσσ hω hM (i := Fin.rev l) (j := k)
      (fun h => hl (by rw [← h, Fin.rev_rev])) (by rw [Fin.rev_rev]; exact hkl) (hdiag k) c).1
    rwa [transvection_congr_fin6 _ hkl rfl (Fin.rev_rev l)] at h

end CFSG.EvenSmallLie.UnitarySix.YamadaInputs
