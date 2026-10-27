module

public import CFSG.LieType.Steinberg.Adjoint.Unipotent
public import CFSG.LieType.Steinberg.PartBRankOne
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {i k : Fin τ.rank}

theorem ne_of_cartan_eq_neg_one (hk : τ.cartan i k = -1) : k ≠ i := by
  rintro rfl
  rw [τ.cartan_self] at hk
  omega

theorem single_ne_single_of_ne {k i : Fin τ.rank} (h : k ≠ i) :
    (Pi.single k 1 : Fin τ.rank → ℤ) ≠ Pi.single i 1 := fun h' => by
  have := congrFun h' k
  simp [h] at this

theorem single_ne_neg_single_of (k i : Fin τ.rank) :
    (Pi.single k 1 : Fin τ.rank → ℤ) ≠ -Pi.single i 1 := fun h' => by
  have := congrFun h' k
  by_cases hki : k = i
  · subst hki
    simp at this
  · simp [hki] at this

theorem not_isRoot_single_sub_single {k i : Fin τ.rank} (h : k ≠ i) :
    ¬IsRoot τ (Pi.single k 1 - Pi.single i 1) := by
  intro hr
  rcases hr.nonneg_or_nonpos with hs | hs
  · have := hs i
    simp [h.symm] at this
  · have := hs k
    simp [h] at this

theorem stringDown_single_eq_zero (hk : τ.cartan i k = -1) :
    stringDown τ i (Pi.single k 1) = 0 := by
  have hki := ne_of_cartan_eq_neg_one hk
  obtain ⟨-, h⟩ := isRoot_add_smul_single_iff (isRoot_single τ k) i
    (single_ne_single_of_ne hki) (single_ne_neg_single_of k i)
  have := (h (-1)).not.1 (by
    rw [neg_one_smul, ← sub_eq_add_neg]
    exact not_isRoot_single_sub_single hki)
  omega

theorem stringUp_single_eq_one (hk : τ.cartan i k = -1) :
    stringUp τ i (Pi.single k 1) = 1 := by
  have h := (root_string_reflection (isRoot_single τ k) i).1
  rw [stringDown_single_eq_zero hk] at h
  have hsum : ∑ j, τ.cartan i j * (Pi.single k 1 : Fin τ.rank → ℤ) j = τ.cartan i k := by
    simp [Pi.single_apply]
  rw [hsum, hk] at h
  omega

theorem isRoot_single_add_single (hk : τ.cartan i k = -1) :
    IsRoot τ (Pi.single k 1 + Pi.single i 1) := by
  have hki := ne_of_cartan_eq_neg_one hk
  obtain ⟨-, h⟩ := isRoot_add_smul_single_iff (isRoot_single τ k) i
    (single_ne_single_of_ne hki) (single_ne_neg_single_of k i)
  have := (h 1).2 ⟨by omega, by rw [stringUp_single_eq_one hk]; norm_num⟩
  rwa [one_smul] at this

theorem not_isRoot_single_add_two (hk : τ.cartan i k = -1) :
    ¬IsRoot τ (Pi.single k 1 + (2 : ℤ) • Pi.single i 1) := by
  have hki := ne_of_cartan_eq_neg_one hk
  obtain ⟨-, h⟩ := isRoot_add_smul_single_iff (isRoot_single τ k) i
    (single_ne_single_of_ne hki) (single_ne_neg_single_of k i)
  intro hr
  have := ((h 2).1 hr).2
  rw [stringUp_single_eq_one hk] at this
  norm_num at this

variable {K : Type} [Field K]

theorem xOp_bot (hk : τ.cartan i k = -1) (c : K) :
    xOp τ K i c (rootVec τ K (Pi.single k 1)) =
      rootVec τ K (Pi.single k 1) + c • rootVec τ K (Pi.single k 1 + Pi.single i 1) := by
  have hki := ne_of_cartan_eq_neg_one hk
  rw [xOp_eq_sum_xCoeff, LinearMap.sum_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, LinearMap.smul_apply,
    xCoeff_rootVec_of_ne i _ (isRoot_single τ k) (single_ne_single_of_ne hki)
      (single_ne_neg_single_of k i), stringDown_single_eq_zero hk]
  have h2 : rootVec τ K (Pi.single k 1 + ((2 : ℕ) : ℤ) • Pi.single i 1) = 0 :=
    rootVec_of_not_isRoot' (by exact_mod_cast not_isRoot_single_add_two hk)
  have h3 : rootVec τ K (Pi.single k 1 + ((3 : ℕ) : ℤ) • Pi.single i 1) = 0 := by
    refine rootVec_of_not_isRoot' fun hr => ?_
    obtain ⟨-, h⟩ := isRoot_add_smul_single_iff (isRoot_single τ k) i
      (single_ne_single_of_ne hki) (single_ne_neg_single_of k i)
    have := ((h 3).1 (by exact_mod_cast hr)).2
    rw [stringUp_single_eq_one hk] at this
    norm_num at this
  rw [h2, h3]
  simp

theorem isRoot_single_add_zsmul_iff (hk : τ.cartan i k = -1) (m : ℤ) :
    IsRoot τ (Pi.single k 1 + m • Pi.single i 1) ↔ 0 ≤ m ∧ m ≤ 1 := by
  have hki := ne_of_cartan_eq_neg_one hk
  obtain ⟨-, h⟩ := isRoot_add_smul_single_iff (isRoot_single τ k) i
    (single_ne_single_of_ne hki) (single_ne_neg_single_of k i)
  rw [h, stringDown_single_eq_zero hk, stringUp_single_eq_one hk]
  simp

theorem top_ne_single (hk : τ.cartan i k = -1) :
    (Pi.single k 1 + Pi.single i 1 : Fin τ.rank → ℤ) ≠ Pi.single i 1 := by
  intro h
  have := congrFun h k
  simp [ne_of_cartan_eq_neg_one hk] at this

theorem top_ne_neg_single (hk : τ.cartan i k = -1) :
    (Pi.single k 1 + Pi.single i 1 : Fin τ.rank → ℤ) ≠ -Pi.single i 1 := by
  intro h
  have := congrFun h k
  simp [ne_of_cartan_eq_neg_one hk] at this

theorem stringDown_top (hk : τ.cartan i k = -1) :
    stringDown τ i (Pi.single k 1 + Pi.single i 1) = 1 := by
  have hki := ne_of_cartan_eq_neg_one hk
  obtain ⟨-, -, htr⟩ := root_string_transport (isRoot_single τ k) i
    (single_ne_single_of_ne hki) (single_ne_neg_single_of k i)
  obtain ⟨-, -, -, -, hd⟩ := htr 1 (by omega) (by rw [stringUp_single_eq_one hk]; norm_num)
  rw [one_smul, stringDown_single_eq_zero hk] at hd
  omega

theorem stringUp_top (hk : τ.cartan i k = -1) :
    stringUp τ i (Pi.single k 1 + Pi.single i 1) = 0 := by
  have hki := ne_of_cartan_eq_neg_one hk
  obtain ⟨-, -, htr⟩ := root_string_transport (isRoot_single τ k) i
    (single_ne_single_of_ne hki) (single_ne_neg_single_of k i)
  obtain ⟨-, -, -, hu, -⟩ := htr 1 (by omega) (by rw [stringUp_single_eq_one hk]; norm_num)
  rw [one_smul, stringUp_single_eq_one hk] at hu
  omega

theorem rootVec_single_add_eq_zero (hk : τ.cartan i k = -1) {m : ℤ} (hm : ¬(0 ≤ m ∧ m ≤ 1)) :
    rootVec τ K (Pi.single k 1 + m • Pi.single i 1) = 0 :=
  rootVec_of_not_isRoot' ((isRoot_single_add_zsmul_iff hk m).not.2 hm)

theorem xOp_top (hk : τ.cartan i k = -1) (c : K) :
    xOp τ K i c (rootVec τ K (Pi.single k 1 + Pi.single i 1)) =
      rootVec τ K (Pi.single k 1 + Pi.single i 1) := by
  rw [xOp_eq_sum_xCoeff, LinearMap.sum_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, LinearMap.smul_apply,
    xCoeff_rootVec_of_ne i _ (isRoot_single_add_single hk) (top_ne_single hk)
      (top_ne_neg_single hk)]
  have h : ∀ n : ℕ, 1 ≤ n → rootVec τ K (Pi.single k 1 + Pi.single i 1 +
      ((n : ℕ) : ℤ) • Pi.single i 1) = 0 := by
    intro n hn
    rw [add_assoc, ← one_add_zsmul]
    exact rootVec_single_add_eq_zero hk (by omega)
  rw [h 1 le_rfl, h 2 (by norm_num), h 3 (by norm_num)]
  simp

theorem yOp_top (hk : τ.cartan i k = -1) (c : K) :
    yOp τ K i c (rootVec τ K (Pi.single k 1 + Pi.single i 1)) =
      rootVec τ K (Pi.single k 1 + Pi.single i 1) + c • rootVec τ K (Pi.single k 1) := by
  rw [yOp_eq_sum_yCoeff, LinearMap.sum_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, LinearMap.smul_apply,
    yCoeff_rootVec_of_ne i _ (isRoot_single_add_single hk) (top_ne_single hk)
      (top_ne_neg_single hk), stringUp_top hk]
  have h : ∀ n : ℕ, 2 ≤ n → rootVec τ K (Pi.single k 1 + Pi.single i 1 -
      ((n : ℕ) : ℤ) • Pi.single i 1) = 0 := by
    intro n hn
    rw [show (Pi.single k 1 + Pi.single i 1 - ((n : ℕ) : ℤ) • Pi.single i 1 : Fin τ.rank → ℤ) =
      Pi.single k 1 + (1 - ((n : ℕ) : ℤ)) • Pi.single i 1 by rw [sub_smul, one_smul]; abel]
    exact rootVec_single_add_eq_zero hk (by omega)
  have h1 : (Pi.single k 1 + Pi.single i 1 - ((1 : ℕ) : ℤ) • Pi.single i 1 :
      Fin τ.rank → ℤ) = Pi.single k 1 := by simp
  rw [h 2 le_rfl, h 3 (by norm_num), h1]
  simp

theorem yOp_bot (hk : τ.cartan i k = -1) (c : K) :
    yOp τ K i c (rootVec τ K (Pi.single k 1)) = rootVec τ K (Pi.single k 1) := by
  have hki := ne_of_cartan_eq_neg_one hk
  rw [yOp_eq_sum_yCoeff, LinearMap.sum_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, LinearMap.smul_apply,
    yCoeff_rootVec_of_ne i _ (isRoot_single τ k) (single_ne_single_of_ne hki)
      (single_ne_neg_single_of k i)]
  have h : ∀ n : ℕ, 1 ≤ n → rootVec τ K (Pi.single k 1 - ((n : ℕ) : ℤ) • Pi.single i 1) = 0 := by
    intro n hn
    rw [sub_eq_add_neg, ← neg_smul]
    exact rootVec_single_add_eq_zero hk (by omega)
  rw [h 1 le_rfl, h 2 (by norm_num), h 3 (by norm_num)]
  simp

section Plane

variable (hk : τ.cartan i k = -1)
include hk

@[expose] def topLabel : Label τ := Sum.inr ⟨_, isRoot_single_add_single hk⟩

omit hk in
@[expose] def botLabel (k : Fin τ.rank) : Label τ := Sum.inr ⟨Pi.single k 1, isRoot_single τ k⟩

theorem topLabel_ne_botLabel : topLabel hk ≠ botLabel k := by
  intro h
  simp only [topLabel, botLabel, Sum.inr.injEq, Subtype.mk.injEq] at h
  have := congrFun h i
  simp [ne_of_cartan_eq_neg_one hk |>.symm] at this

theorem rootVec_top : rootVec τ K (Pi.single k 1 + Pi.single i 1) =
    Finsupp.single (topLabel hk) 1 :=
  rootVec_of_isRoot' _

omit hk in
theorem rootVec_bot : rootVec τ K (Pi.single k 1) = Finsupp.single (botLabel k) 1 :=
  rootVec_of_isRoot' _

omit hk in
@[expose] def PresPlane (hk : τ.cartan i k = -1) (A : Module.End K (RootModule τ K)) : Prop :=
  ∃ a b c d : K,
    A (Finsupp.single (topLabel hk) 1) =
        a • Finsupp.single (topLabel hk) 1 + c • Finsupp.single (botLabel k) 1 ∧
      A (Finsupp.single (botLabel k) 1) =
        b • Finsupp.single (topLabel hk) 1 + d • Finsupp.single (botLabel k) 1

omit hk in
@[expose] def planeMat (hk : τ.cartan i k = -1) (A : Module.End K (RootModule τ K)) :
    Matrix (Fin 2) (Fin 2) K :=
  !![A (Finsupp.single (topLabel hk) 1) (topLabel hk),
    A (Finsupp.single (botLabel k) 1) (topLabel hk);
    A (Finsupp.single (topLabel hk) 1) (botLabel k),
    A (Finsupp.single (botLabel k) 1) (botLabel k)]

theorem planeMat_eq {A : Module.End K (RootModule τ K)} {a b c d : K}
    (h1 : A (Finsupp.single (topLabel hk) 1) =
      a • Finsupp.single (topLabel hk) 1 + c • Finsupp.single (botLabel k) 1)
    (h2 : A (Finsupp.single (botLabel k) 1) =
      b • Finsupp.single (topLabel hk) 1 + d • Finsupp.single (botLabel k) 1) :
    planeMat hk A = !![a, b; c, d] := by
  have hne := topLabel_ne_botLabel hk
  rw [planeMat, h1, h2]
  simp [hne, hne.symm]

theorem PresPlane.mul {A B : Module.End K (RootModule τ K)} (hA : PresPlane hk A)
    (hB : PresPlane hk B) :
    PresPlane hk (A * B) ∧ planeMat hk (A * B) = planeMat hk A * planeMat hk B := by
  obtain ⟨a, b, c, d, hA1, hA2⟩ := hA
  obtain ⟨a', b', c', d', hB1, hB2⟩ := hB
  have h1 : (A * B) (Finsupp.single (topLabel hk) 1) =
      (a * a' + b * c') • Finsupp.single (topLabel hk) 1 +
        (c * a' + d * c') • Finsupp.single (botLabel k) 1 := by
    rw [Module.End.mul_apply, hB1, map_add, map_smul, map_smul, hA1, hA2]
    module
  have h2 : (A * B) (Finsupp.single (botLabel k) 1) =
      (a * b' + b * d') • Finsupp.single (topLabel hk) 1 +
        (c * b' + d * d') • Finsupp.single (botLabel k) 1 := by
    rw [Module.End.mul_apply, hB2, map_add, map_smul, map_smul, hA1, hA2]
    module
  refine ⟨⟨_, _, _, _, h1, h2⟩, ?_⟩
  rw [planeMat_eq hk h1 h2, planeMat_eq hk hA1 hA2, planeMat_eq hk hB1 hB2]
  ext x y
  fin_cases x <;> fin_cases y <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem presPlane_one : PresPlane hk (1 : Module.End K (RootModule τ K)) :=
  ⟨1, 0, 0, 1, by simp, by simp⟩

theorem planeMat_one : planeMat hk (1 : Module.End K (RootModule τ K)) = 1 := by
  rw [planeMat_eq hk (a := 1) (b := 0) (c := 0) (d := 1) (by simp) (by simp)]
  ext x y
  fin_cases x <;> fin_cases y <;> rfl

theorem presPlane_xOp (c : K) : PresPlane hk (xOp τ K i c) :=
  ⟨1, c, 0, 1, by rw [← rootVec_top hk, xOp_top hk]; simp [rootVec_top hk],
    by rw [← rootVec_bot, xOp_bot hk, rootVec_top hk, rootVec_bot, one_smul, add_comm]⟩

theorem planeMat_xOp (c : K) : planeMat hk (xOp τ K i c) = !![1, c; 0, 1] :=
  planeMat_eq hk (by rw [← rootVec_top hk, xOp_top hk]; simp [rootVec_top hk])
    (by rw [← rootVec_bot, xOp_bot hk, rootVec_top hk, rootVec_bot, one_smul, add_comm])

theorem presPlane_yOp (c : K) : PresPlane hk (yOp τ K i c) :=
  ⟨1, 0, c, 1, by rw [← rootVec_top hk, yOp_top hk, rootVec_top hk, rootVec_bot]; simp,
    by rw [← rootVec_bot, yOp_bot hk]; simp [rootVec_bot]⟩

theorem planeMat_yOp (c : K) : planeMat hk (yOp τ K i c) = !![1, 0; c, 1] :=
  planeMat_eq hk (by rw [← rootVec_top hk, yOp_top hk, rootVec_top hk, rootVec_bot]; simp)
    (by rw [← rootVec_bot, yOp_bot hk]; simp [rootVec_bot])

end Plane

section Group

variable (F : RootOperatorFamily τ)

theorem xElt_mem (c : K) : F.eltElement (simpleRoot τ i) c ∈ rootGroup F K (Pi.single i 1) := by
  rw [rootGroup_of_isRoot (isRoot_single τ i)]
  exact F.eltElement_mem_rootSubgroup _ c

theorem yElt_mem (c : K) :
    F.eltElement (-simpleRoot τ i) c ∈ rootGroup F K (-Pi.single i 1) := by
  rw [rootGroup_of_isRoot (isRoot_neg_single τ i)]
  exact F.eltElement_mem_rootSubgroup _ c

theorem endHom_xElt (c : K) : endHom K (F.eltElement (simpleRoot τ i) c) = xOp τ K i c :=
  F.elt_simple i c

theorem endHom_yElt (c : K) : endHom K (F.eltElement (-simpleRoot τ i) c) = yOp τ K i c :=
  F.elt_neg_simple i c

theorem exists_of_mem_rootGroup_simple {g : adjointGroup τ K}
    (hg : g ∈ rootGroup F K (Pi.single i 1)) : ∃ c : K, g = F.eltElement (simpleRoot τ i) c :=
  exists_of_mem_rootGroup (isRoot_single τ i) hg

theorem exists_of_mem_rootGroup_neg_simple {g : adjointGroup τ K}
    (hg : g ∈ rootGroup F K (-Pi.single i 1)) : ∃ c : K, g = F.eltElement (-simpleRoot τ i) c :=
  exists_of_mem_rootGroup (isRoot_neg_single τ i) hg

theorem eltElement_neg (α : Root τ) (c : K) :
    (F.eltElement α c)⁻¹ = F.eltElement α (-c) := by
  rw [eq_comm, eq_inv_iff_mul_eq_one, ← F.eltElement_add, neg_add_cancel, F.eltElement_zero]

theorem xyx_eq_weylElt {t : K} (ht : t ≠ 0) :
    F.eltElement (simpleRoot τ i) t * F.eltElement (-simpleRoot τ i) (-t⁻¹) *
        F.eltElement (simpleRoot τ i) t =
      ⟨weylElt τ K i (Units.mk0 t ht), weylElt_mem_adjointGroup i _⟩ := by
  refine endHom_injective ?_
  rw [map_mul, map_mul, endHom_xElt, endHom_yElt, endHom_apply, coe_weylElt]
  simp

variable (hk : τ.cartan i k = -1)
include hk

@[expose] def planeStab : Subgroup (adjointGroup τ K) where
  carrier := {g | PresPlane hk (endHom K g) ∧ PresPlane hk (endHom K g⁻¹)}
  mul_mem' {g h} hg hh :=
    ⟨by rw [map_mul]; exact (hg.1.mul hk hh.1).1,
      by rw [mul_inv_rev, map_mul]; exact (hh.2.mul hk hg.2).1⟩
  one_mem' := ⟨by rw [map_one]; exact presPlane_one hk,
    by rw [inv_one, map_one]; exact presPlane_one hk⟩
  inv_mem' {g} hg := ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

theorem rootGroup_simple_le_planeStab :
    rootGroup F K (Pi.single i 1) ≤ planeStab (K := K) hk := by
  intro g hg
  obtain ⟨c, rfl⟩ := exists_of_mem_rootGroup_simple F hg
  refine ⟨?_, ?_⟩
  · rw [endHom_xElt]
    exact presPlane_xOp hk c
  · rw [eltElement_neg, endHom_xElt]
    exact presPlane_xOp hk (-c)

theorem rootGroup_neg_simple_le_planeStab :
    rootGroup F K (-Pi.single i 1) ≤ planeStab (K := K) hk := by
  intro g hg
  obtain ⟨c, rfl⟩ := exists_of_mem_rootGroup_neg_simple F hg
  refine ⟨?_, ?_⟩
  · rw [endHom_yElt]
    exact presPlane_yOp hk c
  · rw [eltElement_neg, endHom_yElt]
    exact presPlane_yOp hk (-c)

theorem rankOne_le_planeStab :
    CurtisTits.rankOne (rootGroup F K) i ≤ planeStab (K := K) hk :=
  sup_le (rootGroup_simple_le_planeStab F hk) (rootGroup_neg_simple_le_planeStab F hk)

theorem planeMat_mul {g h : adjointGroup τ K} (hg : g ∈ planeStab (K := K) hk)
    (hh : h ∈ planeStab (K := K) hk) :
    planeMat hk (endHom K (g * h)) = planeMat hk (endHom K g) * planeMat hk (endHom K h) := by
  rw [map_mul]
  exact (hg.1.mul hk hh.1).2

theorem det_planeMat {g : adjointGroup τ K} (hg : g ∈ CurtisTits.rankOne (rootGroup F K) i) :
    (planeMat hk (endHom K g)).det = 1 := by
  have hS : CurtisTits.rankOne (rootGroup F K) i = Subgroup.closure
      ((rootGroup F K (Pi.single i 1) : Set (adjointGroup τ K)) ∪ rootGroup F K (-Pi.single i 1)) :=
    Subgroup.sup_eq_closure _ _
  have hle := rankOne_le_planeStab F (K := K) hk
  rw [hS] at hg hle
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · obtain ⟨c, rfl⟩ := exists_of_mem_rootGroup_simple F hx
      rw [endHom_xElt, planeMat_xOp hk]
      simp [Matrix.det_fin_two]
    · obtain ⟨c, rfl⟩ := exists_of_mem_rootGroup_neg_simple F hx
      rw [endHom_yElt, planeMat_yOp hk]
      simp [Matrix.det_fin_two]
  | one => rw [map_one, planeMat_one hk, Matrix.det_one]
  | mul x y hx hy ihx ihy =>
    rw [planeMat_mul hk (hle hx) (hle hy), Matrix.det_mul, ihx, ihy, one_mul]
  | inv x hx ihx =>
    have h1 := planeMat_mul hk (hle hx) (hle (inv_mem hx))
    rw [mul_inv_cancel, map_one, planeMat_one hk] at h1
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_one, Matrix.det_mul, ihx, one_mul] at h2
    exact h2.symm

@[expose] def restrictHom :
    CurtisTits.rankOne (rootGroup F K) i →* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun g := ⟨planeMat hk (endHom K g), det_planeMat F hk g.2⟩
  map_one' := Subtype.ext (by
    change planeMat hk (endHom K 1) = 1
    rw [map_one, planeMat_one hk])
  map_mul' g h := Subtype.ext (by
    change planeMat hk (endHom K (g.1 * h.1)) = _
    rw [planeMat_mul hk (rankOne_le_planeStab F hk g.2) (rankOne_le_planeStab F hk h.2)]
    rfl)

omit hk in
@[expose] def rankOneRels (i : Fin τ.rank) :
    RankOneRels (CurtisTits.rankOne (rootGroup F K) i) K where
  x c := ⟨F.eltElement (simpleRoot τ i) c, Subgroup.mem_sup_left (xElt_mem F c)⟩
  y c := ⟨F.eltElement (-simpleRoot τ i) c, Subgroup.mem_sup_right (yElt_mem F c)⟩
  x_add a b := Subtype.ext (F.eltElement_add _ a b)
  y_add a b := Subtype.ext (F.eltElement_add _ a b)
  conj_x t ht a := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [xyx_eq_weylElt F ht]
    refine endHom_injective ?_
    rw [map_mul, map_mul, endHom_xElt, endHom_yElt, endHom_apply, endHom_apply]
    simp only [InvMemClass.coe_inv]
    rw [weylElt_mul_xOp_mul_inv]
    congr 1
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
    ring

omit hk in
theorem rankOneRels_x (i : Fin τ.rank) (c : K) :
    ((rankOneRels (K := K) F i).x c : adjointGroup τ K) = F.eltElement (simpleRoot τ i) c :=
  rfl

omit hk in
theorem rankOneRels_y (i : Fin τ.rank) (c : K) :
    ((rankOneRels (K := K) F i).y c : adjointGroup τ K) = F.eltElement (-simpleRoot τ i) c :=
  rfl

omit hk in
theorem rankOneRels_w_one (i : Fin τ.rank) :
    ((rankOneRels (K := K) F i).w 1 : adjointGroup τ K) =
      CFSG.LieType.Chevalley.weylElement τ K i := by
  rw [RankOneRels.w_def]
  simp only [Subgroup.coe_mul, rankOneRels_x, rankOneRels_y]
  have h := xyx_eq_weylElt F (i := i) (one_ne_zero (α := K))
  rw [h]
  refine Subtype.ext ?_
  change weylElt τ K i (Units.mk0 1 _) = weylElt τ K i 1
  rw [show Units.mk0 (1 : K) one_ne_zero = 1 from Units.ext (by simp)]

omit hk in
theorem rankOneRels_h (i : Fin τ.rank) {t : K} (ht : t ≠ 0) :
    ((rankOneRels (K := K) F i).h t : adjointGroup τ K) =
      torusElement τ K i (Units.mk0 t ht) := by
  rw [RankOneRels.h_def, RankOneRels.w_def]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, rankOneRels_x, rankOneRels_y]
  rw [xyx_eq_weylElt F ht, rankOneRels_w_one]
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [torusElement, CFSG.LieType.Chevalley.weylElement]
  simp only
  rw [torusElt, ← weylElt_inv]

omit hk in
theorem rankOneRels_h_mul (i : Fin τ.rank) (s t : K) (hs : s ≠ 0) (ht : t ≠ 0) :
    (rankOneRels (K := K) F i).h (s * t) =
      (rankOneRels (K := K) F i).h s * (rankOneRels (K := K) F i).h t := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, rankOneRels_h F i (mul_ne_zero hs ht), rankOneRels_h F i hs,
    rankOneRels_h F i ht]
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul]
  simp only [torusElement]
  rw [← torusElt_mul]
  congr 1
  exact Units.ext rfl

omit hk in
theorem rankOneRels_sub (i : Fin τ.rank) : (rankOneRels (K := K) F i).sub = ⊤ := by
  set R := rankOneRels (K := K) F i
  have hmap : CurtisTits.rankOne (rootGroup F K) i ≤
      R.sub.map (CurtisTits.rankOne (rootGroup F K) i).subtype := by
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · obtain ⟨c, rfl⟩ := exists_of_mem_rootGroup_simple F hg
      exact ⟨R.x c, R.x_mem_sub c, rfl⟩
    · obtain ⟨c, rfl⟩ := exists_of_mem_rootGroup_neg_simple F hg
      exact ⟨R.y c, R.y_mem_sub c, rfl⟩
  refine eq_top_iff.2 fun g _ => ?_
  obtain ⟨g', hg', he⟩ := hmap g.2
  rwa [show g' = g from Subtype.ext he] at hg'

theorem restrictHom_x (c : K) :
    restrictHom F hk ((rankOneRels (K := K) F i).x c) = sl2Upper c :=
  Subtype.ext (by
    change planeMat hk (endHom K (F.eltElement (simpleRoot τ i) c)) = _
    rw [endHom_xElt, planeMat_xOp hk]
    rfl)

theorem restrictHom_y (c : K) :
    restrictHom F hk ((rankOneRels (K := K) F i).y c) = sl2Lower c :=
  Subtype.ext (by
    change planeMat hk (endHom K (F.eltElement (-simpleRoot τ i) c)) = _
    rw [endHom_yElt, planeMat_yOp hk]
    rfl)

omit hk in
theorem mem_bruhat (g : CurtisTits.rankOne (rootGroup F K) i) :
    g ∈ (rankOneRels (K := K) F i).bruhat :=
  (rankOneRels F i).sub_subset_bruhat (rankOneRels_h_mul F i)
    (by rw [rankOneRels_sub F i]; trivial)

theorem restrictHom_injective : Function.Injective (restrictHom (K := K) F hk) := by
  refine (injective_iff_map_eq_one _).2 fun g hg => ?_
  exact (rankOneRels F i).eq_one_of_mem_bruhat (restrictHom F hk) (MonoidHom.id _)
    Function.injective_id (restrictHom_x F hk) (restrictHom_y F hk) (mem_bruhat F g) hg

end Group

theorem sl2_eq_upper_lower_upper (s : Matrix.SpecialLinearGroup (Fin 2) K)
    (h : (s : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) :
    s = sl2Upper (((s : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) / (s : Matrix (Fin 2) (Fin 2) K) 1 0) *
      sl2Lower ((s : Matrix (Fin 2) (Fin 2) K) 1 0) *
      sl2Upper (((s : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) / (s : Matrix (Fin 2) (Fin 2) K) 1 0) := by
  have hdet := s.2
  rw [Matrix.det_fin_two] at hdet
  ext x y
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Lower]
  fin_cases x <;> fin_cases y
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    linear_combination (-1 : K) * hdet
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring

theorem sl2_eq_prod (s : Matrix.SpecialLinearGroup (Fin 2) K) :
    ∃ e a b c : K, s = sl2Lower e * sl2Upper a * sl2Lower b * sl2Upper c := by
  have hlow0 : sl2Lower (0 : K) = 1 := by
    ext x y
    fin_cases x <;> fin_cases y <;> rfl
  by_cases h : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · set s' := sl2Lower (1 : K) * s with hs'_def
    have hdet := s.2
    rw [Matrix.det_fin_two, h, mul_zero, sub_zero] at hdet
    have h' : (s' : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
      simp only [s', Matrix.SpecialLinearGroup.coe_mul, coe_sl2Lower, Matrix.mul_apply,
        Fin.sum_univ_two]
      simp [h]
      exact left_ne_zero_of_mul_eq_one hdet
    have hs' := sl2_eq_upper_lower_upper s' h'
    refine ⟨-1, ((s' : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) / (s' : Matrix (Fin 2) (Fin 2) K) 1 0,
      (s' : Matrix (Fin 2) (Fin 2) K) 1 0,
      ((s' : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) / (s' : Matrix (Fin 2) (Fin 2) K) 1 0, ?_⟩
    rw [mul_assoc, mul_assoc, ← mul_assoc (sl2Upper _), ← hs', hs'_def, ← mul_assoc,
      show sl2Lower (-1 : K) * sl2Lower 1 = 1 by
        ext x y
        fin_cases x <;> fin_cases y <;> simp [Matrix.mul_apply, Fin.sum_univ_two, coe_sl2Lower],
      one_mul]
  · refine ⟨0, ((s : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) / (s : Matrix (Fin 2) (Fin 2) K) 1 0,
      (s : Matrix (Fin 2) (Fin 2) K) 1 0,
      ((s : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) / (s : Matrix (Fin 2) (Fin 2) K) 1 0, ?_⟩
    rw [hlow0, one_mul]
    exact sl2_eq_upper_lower_upper s h

section Group

variable (F : RootOperatorFamily τ) (hk : τ.cartan i k = -1)
include hk

theorem restrictHom_surjective : Function.Surjective (restrictHom (K := K) F hk) := by
  intro s
  obtain ⟨e, a, b, c, rfl⟩ := sl2_eq_prod s
  refine ⟨(rankOneRels (K := K) F i).y e * (rankOneRels (K := K) F i).x a *
    (rankOneRels (K := K) F i).y b * (rankOneRels (K := K) F i).x c, ?_⟩
  rw [map_mul, map_mul, map_mul, restrictHom_y, restrictHom_x, restrictHom_y, restrictHom_x]

@[expose] def restrictEquiv :
    CurtisTits.rankOne (rootGroup F K) i ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
  MulEquiv.ofBijective (restrictHom F hk) ⟨restrictHom_injective F hk, restrictHom_surjective F hk⟩

theorem restrictEquiv_symm_upper (c : K) :
    (restrictEquiv F hk).symm (sl2Upper c) = (rankOneRels (K := K) F i).x c := by
  rw [MulEquiv.symm_apply_eq]
  exact (restrictHom_x F hk c).symm

theorem restrictEquiv_symm_lower (c : K) :
    (restrictEquiv F hk).symm (sl2Lower c) = (rankOneRels (K := K) F i).y c := by
  rw [MulEquiv.symm_apply_eq]
  exact (restrictHom_y F hk c).symm

theorem exists_sl2_hom :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) K →* adjointGroup τ K, Function.Injective φ ∧
      (∀ c, φ (sl2Upper c) = F.eltElement (simpleRoot τ i) c) ∧
        ∀ c, φ (sl2Lower c) = F.eltElement (-simpleRoot τ i) c :=
  ⟨(CurtisTits.rankOne (rootGroup F K) i).subtype.comp (restrictEquiv F hk).symm.toMonoidHom,
    Subtype.val_injective.comp (restrictEquiv F hk).symm.injective,
    fun c => by simp [restrictEquiv_symm_upper F hk c, rankOneRels_x],
    fun c => by simp [restrictEquiv_symm_lower F hk c, rankOneRels_y]⟩

omit hk in
theorem rankOne_bruhat (i : Fin τ.rank) {g : adjointGroup τ K}
    (hg : g ∈ CurtisTits.rankOne (rootGroup F K) i) :
    (∃ h ∈ torus K i, ∃ u ∈ rootGroup F K (Pi.single i 1), g = h * u) ∨
      ∃ u ∈ rootGroup F K (Pi.single i 1), ∃ h ∈ torus K i,
        ∃ v ∈ rootGroup F K (Pi.single i 1),
          g = u * CFSG.LieType.Chevalley.weylElement τ K i * h * v := by
  set R := rankOneRels (K := K) F i
  have hx : ∀ c, ((R.x c : CurtisTits.rankOne (rootGroup F K) i) : adjointGroup τ K) ∈
      rootGroup F K (Pi.single i 1) := fun c => xElt_mem F c
  have hh : ∀ {t : K} (ht : t ≠ 0), ((R.h t : CurtisTits.rankOne (rootGroup F K) i) :
      adjointGroup τ K) ∈ torus K i := fun ht => by
    rw [rankOneRels_h F i ht]
    exact ⟨_, rfl⟩
  rcases mem_bruhat F ⟨g, hg⟩ with ⟨a, t, ht, he⟩ | ⟨a, b, t, ht, he⟩
  · left
    have e : R.x a * R.h t = R.h t * R.x ((t ^ 2)⁻¹ * a) := by
      rw [R.h_mul_x ht, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 ht), one_mul]
    rw [e] at he
    exact ⟨_, hh ht, _, hx ((t ^ 2)⁻¹ * a), congrArg Subtype.val he⟩
  · right
    have e : R.x a * R.w 1 * R.x b * R.h t = R.x a * R.w 1 * R.h t * R.x ((t ^ 2)⁻¹ * b) := by
      rw [mul_assoc _ (R.h t), R.h_mul_x ht, mul_inv_cancel_left₀ (pow_ne_zero 2 ht), ← mul_assoc]
    rw [e] at he
    refine ⟨_, hx a, _, hh ht, _, hx ((t ^ 2)⁻¹ * b), ?_⟩
    have := congrArg Subtype.val he
    simp only [Subgroup.coe_mul] at this
    rw [this, rankOneRels_w_one]

theorem eq_one_of_mem_normalizer {u : adjointGroup τ K}
    (hu : u ∈ rootGroup F K (Pi.single i 1))
    (hn : u ∈ Subgroup.normalizer (rootGroup F K (-Pi.single i 1) : Set (adjointGroup τ K))) :
    u = 1 := by
  set R := rankOneRels (K := K) F i
  obtain ⟨c, rfl⟩ := exists_of_mem_rootGroup_simple F hu
  have hy := (Subgroup.mem_normalizer_iff.1 hn (F.eltElement (-simpleRoot τ i) 1)).1 (yElt_mem F 1)
  obtain ⟨d, hd⟩ := exists_of_mem_rootGroup_neg_simple F hy
  have he : R.x c * R.y 1 * (R.x c)⁻¹ = R.y d := Subtype.ext hd
  have he' := congrArg (restrictHom F hk) he
  rw [map_mul, map_mul, map_inv, restrictHom_x, restrictHom_y, restrictHom_y] at he'
  have h00 := congrArg (fun s : Matrix.SpecialLinearGroup (Fin 2) K =>
    (s : Matrix (Fin 2) (Fin 2) K) 0 0) he'
  simp [Matrix.SpecialLinearGroup.coe_inv, coe_sl2Upper, coe_sl2Lower, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.adjugate_fin_two] at h00
  rw [h00, F.eltElement_zero]

end Group

end CFSG.LieType.Steinberg.Adjoint
