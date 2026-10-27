module

public import CFSG.LieType.Steinberg.Adjoint.RankOne

public noncomputable section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {i k : Fin τ.rank}

theorem ne_of_cartan_eq_neg_three (hk : τ.cartan i k = -3) : k ≠ i := by
  rintro rfl
  rw [τ.cartan_self] at hk
  omega

theorem stringDown_single_of_ne
    (hki : k ≠ i) : stringDown τ i (Pi.single k 1) = 0 := by
  obtain ⟨-, h⟩ := isRoot_add_smul_single_iff (isRoot_single τ k) i
    (single_ne_single_of_ne hki) (single_ne_neg_single_of k i)
  have := (h (-1)).not.1 (by
    rw [neg_one_smul, ← sub_eq_add_neg]
    exact not_isRoot_single_sub_single hki)
  omega

theorem stringUp_single_of_cartan_eq_neg_three
    (hk : τ.cartan i k = -3) :
    stringUp τ i (Pi.single k 1) = 3 := by
  have h := (root_string_reflection (isRoot_single τ k) i).1
  rw [stringDown_single_of_ne (ne_of_cartan_eq_neg_three hk)] at h
  have hsum : ∑ j, τ.cartan i j * (Pi.single k 1 : Fin τ.rank → ℤ) j = τ.cartan i k := by
    simp [Pi.single_apply]
  rw [hsum, hk] at h
  omega

variable (i k) in
@[expose] def strRoot (m : ℤ) : Fin τ.rank → ℤ :=
  Pi.single k 1 + m • Pi.single i 1

theorem isRoot_strRoot_iff
    (hk : τ.cartan i k = -3) (m : ℤ) :
    IsRoot τ (strRoot i k m) ↔ 0 ≤ m ∧ m ≤ 3 := by
  have hki := ne_of_cartan_eq_neg_three hk
  obtain ⟨-, h⟩ := isRoot_add_smul_single_iff (isRoot_single τ k) i
    (single_ne_single_of_ne hki) (single_ne_neg_single_of k i)
  rw [strRoot, h, stringDown_single_of_ne hki, stringUp_single_of_cartan_eq_neg_three hk]
  simp

theorem strRoot_spec
    (hk : τ.cartan i k = -3) {m : ℕ} (hm : m ≤ 3) :
    IsRoot τ (strRoot i k m) ∧ strRoot i k m ≠ Pi.single i 1 ∧
      strRoot i k m ≠ -Pi.single i 1 ∧ stringUp τ i (strRoot i k m) = 3 - m ∧
      stringDown τ i (strRoot i k m) = m := by
  have hki := ne_of_cartan_eq_neg_three hk
  obtain ⟨-, -, htr⟩ := root_string_transport (isRoot_single τ k) i
    (single_ne_single_of_ne hki) (single_ne_neg_single_of k i)
  rw [stringUp_single_of_cartan_eq_neg_three hk, stringDown_single_of_ne hki] at htr
  obtain ⟨hr, h1, h2, hu, hd⟩ := htr m (by omega) (by exact_mod_cast hm)
  unfold strRoot
  exact ⟨hr, h1, h2, by omega, by omega⟩

theorem rootVec_strRoot_eq_zero
    {R : Type*} [CommRing R] (hk : τ.cartan i k = -3) {m : ℤ}
    (hm : m < 0 ∨ 3 < m) : rootVec τ R (strRoot i k m) = 0 :=
  rootVec_of_not_isRoot' fun h => by
    have := (isRoot_strRoot_iff hk m).1 h
    omega

section Ops

variable {R : Type*} [CommRing R]

theorem xOp_strRoot
    (hk : τ.cartan i k = -3) {m : ℕ} (hm : m ≤ 3) (c : R) :
    xOp τ R i c (rootVec τ R (strRoot i k m)) =
      ∑ n ∈ Finset.range 4,
        (c ^ n * ((m + n).choose n : R)) • rootVec τ R (strRoot i k (m + n)) := by
  obtain ⟨hr, h1, h2, -, hd⟩ := strRoot_spec hk hm
  rw [xOp_eq_sum_xCoeff, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [LinearMap.smul_apply, xCoeff_rootVec_of_ne i n hr h1 h2, hd, smul_smul]
  congr 2
  simp only [strRoot, add_smul, add_assoc]

theorem yOp_strRoot
    (hk : τ.cartan i k = -3) {m : ℕ} (hm : m ≤ 3) (c : R) :
    yOp τ R i c (rootVec τ R (strRoot i k m)) =
      ∑ n ∈ Finset.range 4,
        (c ^ n * ((3 - m + n).choose n : R)) • rootVec τ R (strRoot i k (m - n)) := by
  obtain ⟨hr, h1, h2, hu, -⟩ := strRoot_spec hk hm
  rw [yOp_eq_sum_yCoeff, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [LinearMap.smul_apply, yCoeff_rootVec_of_ne i n hr h1 h2, hu, smul_smul]
  congr 2
  simp only [strRoot, sub_smul, add_sub_assoc]

end Ops

section MatOn

variable {R : Type*} [CommRing R] {n : ℕ}

variable (R) in
@[expose] def HasMatOn (lab : Fin n → Label τ) (A : Module.End R (RootModule τ R))
    (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ b, A (Finsupp.single (lab b) 1) = ∑ a, M a b • Finsupp.single (lab a) 1

variable {lab : Fin n → Label τ}

theorem HasMatOn.mul
    {A B : Module.End R (RootModule τ R)} {M N : Matrix (Fin n) (Fin n) R}
    (hA : HasMatOn R lab A M) (hB : HasMatOn R lab B N) : HasMatOn R lab (A * B) (M * N) := by
  intro b
  have hA' : ∀ c, A (Finsupp.single (lab c) 1) = ∑ a, M a c • Finsupp.single (lab a) 1 := hA
  rw [Module.End.mul_apply, hB b, map_sum]
  simp only [map_smul, hA', Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by rw [mul_comm]

theorem hasMatOn_one : HasMatOn R lab 1 1 := by
  intro b
  simp [Matrix.one_apply]

theorem HasMatOn.apply (hlab : Function.Injective lab) {A : Module.End R (RootModule τ R)}
    {M : Matrix (Fin n) (Fin n) R} (h : HasMatOn R lab A M) (a b : Fin n) :
    A (Finsupp.single (lab b) 1) (lab a) = M a b := by
  rw [h b, Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply, hlab.eq_iff]

end MatOn

section Sym3

variable {R : Type*} [CommRing R]

@[expose] def sym3Fun (g : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 4) (Fin 4) R :=
  !![g 1 1 ^ 3, 3 * g 1 0 * g 1 1 ^ 2, 3 * g 1 0 ^ 2 * g 1 1, g 1 0 ^ 3;
    g 0 1 * g 1 1 ^ 2, g 0 0 * g 1 1 ^ 2 + 2 * g 0 1 * g 1 0 * g 1 1,
      2 * g 0 0 * g 1 0 * g 1 1 + g 0 1 * g 1 0 ^ 2, g 0 0 * g 1 0 ^ 2;
    g 0 1 ^ 2 * g 1 1, 2 * g 0 0 * g 0 1 * g 1 1 + g 0 1 ^ 2 * g 1 0,
      g 0 0 ^ 2 * g 1 1 + 2 * g 0 0 * g 0 1 * g 1 0, g 0 0 ^ 2 * g 1 0;
    g 0 1 ^ 3, 3 * g 0 0 * g 0 1 ^ 2, 3 * g 0 0 ^ 2 * g 0 1, g 0 0 ^ 3]

variable (R) in
@[expose] def sym3 : Matrix (Fin 2) (Fin 2) R →* Matrix (Fin 4) (Fin 4) R where
  toFun := sym3Fun
  map_one' := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [sym3Fun]
  map_mul' g h := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [sym3Fun, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four] <;> ring

theorem sym3_apply (g : Matrix (Fin 2) (Fin 2) R) : sym3 R g = sym3Fun g := rfl

theorem sym3_upper (c : R) :
    sym3 R !![1, c; 0, 1] =
      !![1, 0, 0, 0; c, 1, 0, 0; c ^ 2, 2 * c, 1, 0; c ^ 3, 3 * c ^ 2, 3 * c, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [sym3_apply, sym3Fun]

theorem sym3_lower (c : R) :
    sym3 R !![1, 0; c, 1] =
      !![1, 3 * c, 3 * c ^ 2, c ^ 3; 0, 1, 2 * c, c ^ 2; 0, 0, 1, c; 0, 0, 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [sym3_apply, sym3Fun]

variable {K : Type} [Field K]

theorem eq_one_of_sym3_eq_one {g : Matrix.SpecialLinearGroup (Fin 2) K}
    (h : sym3 K (g : Matrix (Fin 2) (Fin 2) K) = 1) : g = 1 := by
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  have e30 := congrFun (congrFun h 3) 0
  have e03 := congrFun (congrFun h 0) 3
  have e11 := congrFun (congrFun h 1) 1
  have e22 := congrFun (congrFun h 2) 2
  simp [sym3_apply, sym3Fun] at e30 e03 e11 e22
  rw [e30, e03, mul_zero, sub_zero] at hdet
  rw [e30, e03] at e11 e22
  simp only [mul_zero, zero_mul, add_zero] at e11 e22
  have h00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    linear_combination e22 - (g : Matrix (Fin 2) (Fin 2) K) 0 0 * hdet
  have h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    linear_combination e11 - (g : Matrix (Fin 2) (Fin 2) K) 1 1 * hdet
  ext a b
  fin_cases a <;> fin_cases b <;> simp [h00, h11, e30, e03]

variable (K) in
@[expose] def sym3SL : Matrix.SpecialLinearGroup (Fin 2) K →* (Matrix (Fin 4) (Fin 4) K)ˣ :=
  ((sym3 K).comp Matrix.SpecialLinearGroup.coeMonoidHom).toHomUnits

theorem coe_sym3SL (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((sym3SL K g : (Matrix (Fin 4) (Fin 4) K)ˣ) : Matrix (Fin 4) (Fin 4) K) =
      sym3 K (g : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem sym3SL_injective : Function.Injective (sym3SL K) :=
  (injective_iff_map_eq_one _).2 fun g hg =>
    eq_one_of_sym3_eq_one (by rw [← coe_sym3SL, hg, Units.val_one])

end Sym3

section String

variable (hk : τ.cartan i k = -3)
include hk

@[expose] def strLabel
    (m : Fin 4) : Label τ :=
  Sum.inr ⟨strRoot i k (m : ℕ), (strRoot_spec hk (Nat.lt_succ_iff.1 m.2)).1⟩

theorem strLabel_injective :
    Function.Injective (strLabel hk) := by
  intro a b h
  simp only [strLabel, Sum.inr.injEq, Subtype.mk.injEq] at h
  have := congrFun h i
  simp [strRoot, ne_of_cartan_eq_neg_three hk] at this
  exact Fin.ext this

theorem rootVec_strRoot
    {R : Type*} [CommRing R] (m : Fin 4) :
    rootVec τ R (strRoot i k (m : ℕ)) = Finsupp.single (strLabel hk m) 1 :=
  rootVec_of_isRoot' _

variable {R : Type*} [CommRing R]

theorem hasMatOn_xOp
    (c : R) :
    HasMatOn R (strLabel hk) (xOp τ R i c) (sym3 R !![1, c; 0, 1]) := by
  intro b
  simp only [← rootVec_strRoot hk]
  rw [xOp_strRoot hk (by omega : (b : ℕ) ≤ 3), Fin.sum_univ_four, sym3_upper]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  fin_cases b <;> simp [rootVec_strRoot_eq_zero hk] <;> module

theorem hasMatOn_yOp
    (c : R) :
    HasMatOn R (strLabel hk) (yOp τ R i c) (sym3 R !![1, 0; c, 1]) := by
  intro b
  simp only [← rootVec_strRoot hk]
  rw [yOp_strRoot hk (by omega : (b : ℕ) ≤ 3), Fin.sum_univ_four, sym3_lower]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  fin_cases b <;> simp [rootVec_strRoot_eq_zero hk] <;> module

end String

section RankOneHom

variable
    (F : RootOperatorFamily τ) {K : Type} [Field K]
  (ψ : CurtisTits.rankOne (rootGroup F K) i →* Matrix.SpecialLinearGroup (Fin 2) K)
  (hx : ∀ c, ψ ((rankOneRels (K := K) F i).x c) = sl2Upper c)
  (hy : ∀ c, ψ ((rankOneRels (K := K) F i).y c) = sl2Lower c)
include hx hy

theorem rankOne_injective_of_hom :
    Function.Injective ψ := by
  refine (injective_iff_map_eq_one _).2 fun g hg => ?_
  exact (rankOneRels F i).eq_one_of_mem_bruhat ψ (MonoidHom.id _) Function.injective_id hx hy
    (mem_bruhat F g) hg

theorem rankOne_surjective_of_hom :
    Function.Surjective ψ := by
  intro s
  obtain ⟨e, a, b, c, rfl⟩ := sl2_eq_prod s
  refine ⟨(rankOneRels (K := K) F i).y e * (rankOneRels (K := K) F i).x a *
    (rankOneRels (K := K) F i).y b * (rankOneRels (K := K) F i).x c, ?_⟩
  rw [map_mul, map_mul, map_mul, hy, hx, hy, hx]

theorem exists_sl2_hom_of_rankOne_hom :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) K →* adjointGroup τ K, Function.Injective φ ∧
      (∀ c, φ (sl2Upper c) = F.eltElement (simpleRoot τ i) c) ∧
        ∀ c, φ (sl2Lower c) = F.eltElement (-simpleRoot τ i) c := by
  set e := MulEquiv.ofBijective ψ
    ⟨rankOne_injective_of_hom F ψ hx hy, rankOne_surjective_of_hom F ψ hx hy⟩
  have hex : ∀ c, e.symm (sl2Upper c) = (rankOneRels (K := K) F i).x c := fun c => by
    rw [MulEquiv.symm_apply_eq]
    exact (hx c).symm
  have hey : ∀ c, e.symm (sl2Lower c) = (rankOneRels (K := K) F i).y c := fun c => by
    rw [MulEquiv.symm_apply_eq]
    exact (hy c).symm
  exact ⟨(CurtisTits.rankOne (rootGroup F K) i).subtype.comp e.symm.toMonoidHom,
    Subtype.val_injective.comp e.symm.injective,
    fun c => by simp [hex c, rankOneRels_x], fun c => by simp [hey c, rankOneRels_y]⟩

theorem eq_one_of_mem_normalizer_of_rankOne_hom
    {u : adjointGroup τ K}
    (hu : u ∈ rootGroup F K (Pi.single i 1))
    (hn : u ∈ Subgroup.normalizer (rootGroup F K (-Pi.single i 1) : Set (adjointGroup τ K))) :
    u = 1 := by
  set R := rankOneRels (K := K) F i
  obtain ⟨c, rfl⟩ := exists_of_mem_rootGroup_simple F hu
  have hy1 :=
    (Subgroup.mem_normalizer_iff.1 hn (F.eltElement (-simpleRoot τ i) 1)).1 (yElt_mem F 1)
  obtain ⟨d, hd⟩ := exists_of_mem_rootGroup_neg_simple F hy1
  have he : R.x c * R.y 1 * (R.x c)⁻¹ = R.y d := Subtype.ext hd
  have he' := congrArg ψ he
  rw [map_mul, map_mul, map_inv, hx, hy, hy] at he'
  have h00 := congrArg (fun s : Matrix.SpecialLinearGroup (Fin 2) K =>
    (s : Matrix (Fin 2) (Fin 2) K) 0 0) he'
  simp [Matrix.SpecialLinearGroup.coe_inv, coe_sl2Upper, coe_sl2Lower, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.adjugate_fin_two] at h00
  rw [h00, F.eltElement_zero]

end RankOneHom

section Group

variable
    (F : RootOperatorFamily τ) {K : Type} [Field K] (hk : τ.cartan i k = -3)
include hk

@[expose] def strStab :
    Subgroup (adjointGroup τ K) where
  carrier := {g | (∃ M, HasMatOn K (strLabel hk) (endHom K g) M) ∧
    ∃ M, HasMatOn K (strLabel hk) (endHom K g⁻¹) M}
  mul_mem' {g h} hg hh := by
    obtain ⟨⟨M, hM⟩, M', hM'⟩ := hg
    obtain ⟨⟨N, hN⟩, N', hN'⟩ := hh
    exact ⟨⟨M * N, by rw [map_mul]; exact hM.mul hN⟩,
      ⟨N' * M', by rw [mul_inv_rev, map_mul]; exact hN'.mul hM'⟩⟩
  one_mem' := ⟨⟨1, by rw [map_one]; exact hasMatOn_one⟩,
    ⟨1, by rw [inv_one, map_one]; exact hasMatOn_one⟩⟩
  inv_mem' {g} hg := ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

@[expose] def strMat
    (A : Module.End K (RootModule τ K)) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun a b => A (Finsupp.single (strLabel hk b) 1) (strLabel hk a)

theorem strMat_eq
    {A : Module.End K (RootModule τ K)} {M : Matrix (Fin 4) (Fin 4) K}
    (h : HasMatOn K (strLabel hk) A M) : strMat hk A = M := by
  ext a b
  exact h.apply (strLabel_injective hk) a b

theorem rootGroup_simple_le_strStab :
    rootGroup F K (Pi.single i 1) ≤ strStab (K := K) hk := by
  intro g hg
  obtain ⟨c, rfl⟩ := exists_of_mem_rootGroup_simple F hg
  refine ⟨⟨sym3 K !![1, c; 0, 1], ?_⟩, ⟨sym3 K !![1, -c; 0, 1], ?_⟩⟩
  · rw [endHom_xElt]
    exact hasMatOn_xOp hk c
  · rw [eltElement_neg, endHom_xElt]
    exact hasMatOn_xOp hk (-c)

theorem rootGroup_neg_simple_le_strStab :
    rootGroup F K (-Pi.single i 1) ≤ strStab (K := K) hk := by
  intro g hg
  obtain ⟨c, rfl⟩ := exists_of_mem_rootGroup_neg_simple F hg
  refine ⟨⟨sym3 K !![1, 0; c, 1], ?_⟩, ⟨sym3 K !![1, 0; -c, 1], ?_⟩⟩
  · rw [endHom_yElt]
    exact hasMatOn_yOp hk c
  · rw [eltElement_neg, endHom_yElt]
    exact hasMatOn_yOp hk (-c)

theorem rankOne_le_strStab :
    CurtisTits.rankOne (rootGroup F K) i ≤ strStab (K := K) hk :=
  sup_le (rootGroup_simple_le_strStab F hk) (rootGroup_neg_simple_le_strStab F hk)

theorem strMat_mul
    {g h : adjointGroup τ K} (hg : g ∈ strStab (K := K) hk)
    (hh : h ∈ strStab (K := K) hk) :
    strMat hk (endHom K (g * h)) = strMat hk (endHom K g) * strMat hk (endHom K h) := by
  obtain ⟨⟨M, hM⟩, -⟩ := hg
  obtain ⟨⟨N, hN⟩, -⟩ := hh
  rw [map_mul, strMat_eq hk (hM.mul hN), strMat_eq hk hM, strMat_eq hk hN]

@[expose] def strRestrict
    : CurtisTits.rankOne (rootGroup F K) i →* Matrix (Fin 4) (Fin 4) K where
  toFun g := strMat hk (endHom K g)
  map_one' := by
    change strMat hk (endHom K 1) = 1
    rw [map_one, strMat_eq hk hasMatOn_one]
  map_mul' g h := strMat_mul hk (rankOne_le_strStab F hk g.2) (rankOne_le_strStab F hk h.2)

theorem strRestrict_x
    (c : K) :
    strRestrict F hk ((rankOneRels (K := K) F i).x c) =
      sym3 K (sl2Upper c : Matrix.SpecialLinearGroup (Fin 2) K) := by
  change strMat hk (endHom K (F.eltElement (simpleRoot τ i) c)) = _
  rw [endHom_xElt, strMat_eq hk (hasMatOn_xOp hk c), coe_sl2Upper]

theorem strRestrict_y
    (c : K) :
    strRestrict F hk ((rankOneRels (K := K) F i).y c) =
      sym3 K (sl2Lower c : Matrix.SpecialLinearGroup (Fin 2) K) := by
  change strMat hk (endHom K (F.eltElement (-simpleRoot τ i) c)) = _
  rw [endHom_yElt, strMat_eq hk (hasMatOn_yOp hk c), coe_sl2Lower]

theorem strRestrict_mem_range
    (g : CurtisTits.rankOne (rootGroup F K) i) :
    (strRestrict F hk).toHomUnits g ∈ (sym3SL K).range := by
  have hg : g ∈ (rankOneRels (K := K) F i).sub := by
    rw [rankOneRels_sub F i]
    trivial
  unfold RankOneRels.sub at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact ⟨sl2Upper c, Units.ext (by rw [coe_sym3SL, MonoidHom.coe_toHomUnits, strRestrict_x])⟩
    · exact ⟨sl2Lower c, Units.ext (by rw [coe_sym3SL, MonoidHom.coe_toHomUnits, strRestrict_y])⟩
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

@[expose] def strRestrictHom :
    CurtisTits.rankOne (rootGroup F K) i →* Matrix.SpecialLinearGroup (Fin 2) K :=
  (MonoidHom.ofInjective sym3SL_injective).symm.toMonoidHom.comp
    ((strRestrict F hk).toHomUnits.codRestrict _ (strRestrict_mem_range F hk))

theorem strRestrictHom_x
    (c : K) :
    strRestrictHom F hk ((rankOneRels (K := K) F i).x c) = sl2Upper c := by
  rw [strRestrictHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq]
  refine Subtype.ext (Units.ext ?_)
  rw [MonoidHom.ofInjective_apply, coe_sym3SL]
  exact strRestrict_x F hk c

theorem strRestrictHom_y
    (c : K) :
    strRestrictHom F hk ((rankOneRels (K := K) F i).y c) = sl2Lower c := by
  rw [strRestrictHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq]
  refine Subtype.ext (Units.ext ?_)
  rw [MonoidHom.ofInjective_apply, coe_sym3SL]
  exact strRestrict_y F hk c

@[expose] def strRestrictEquiv :
    CurtisTits.rankOne (rootGroup F K) i ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
  MulEquiv.ofBijective (strRestrictHom F hk)
    ⟨rankOne_injective_of_hom F _ (strRestrictHom_x F hk) (strRestrictHom_y F hk),
      rankOne_surjective_of_hom F _ (strRestrictHom_x F hk) (strRestrictHom_y F hk)⟩

theorem exists_sl2_hom_of_cartan_eq_neg_three :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) K →* adjointGroup τ K, Function.Injective φ ∧
      (∀ c, φ (sl2Upper c) = F.eltElement (simpleRoot τ i) c) ∧
        ∀ c, φ (sl2Lower c) = F.eltElement (-simpleRoot τ i) c :=
  exists_sl2_hom_of_rankOne_hom F _ (strRestrictHom_x F hk) (strRestrictHom_y F hk)

theorem eq_one_of_mem_normalizer_of_cartan_eq_neg_three
    {u : adjointGroup τ K}
    (hu : u ∈ rootGroup F K (Pi.single i 1))
    (hn : u ∈ Subgroup.normalizer (rootGroup F K (-Pi.single i 1) : Set (adjointGroup τ K))) :
    u = 1 :=
  eq_one_of_mem_normalizer_of_rankOne_hom F _ (strRestrictHom_x F hk) (strRestrictHom_y F hk)
    hu hn

end Group

end CFSG.LieType.Steinberg.Adjoint
