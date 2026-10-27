module

public import CFSG.Blueprint.ChevalleyStrings
public import CFSG.LieType.RootSystem.Parabolic
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin
public import Certificates.Certificate113
public import Certificates.Certificate114

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.RootSystem

theorem cartanE_eq (r : ℕ) : Tag.cartanE r = CartanMatrix.E r := by
  ext i j
  simp only [Tag.cartanE, CartanMatrix.E, Matrix.of_apply]
  by_cases hij : i = j
  · simp [hij]
  · have : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp only [hij, ite_false]
    congr 1
    apply propext
    omega

theorem isFiniteType_cartan : ∀ τ : Tag, TauCeti.IsFiniteType τ.cartan
  | .G2 => by
    have h : Tag.cartan .G2 = CartanMatrix.G₂.transpose := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [h, ← TauCeti.DynkinType.cartanMatrix_G2]
    exact TauCeti.DynkinType.isFiniteType_cartanMatrix_G2
  | .F4 => by
    have h : Tag.cartan .F4 = CartanMatrix.F₄.transpose := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [h, ← TauCeti.DynkinType.cartanMatrix_F4]
    exact TauCeti.DynkinType.isFiniteType_cartanMatrix_F4.transpose
  | .D4 => by
    have h : Tag.cartan .D4 =
        (CartanMatrix.D 4).submatrix (Equiv.swap (1 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 2) := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [h]
    exact (TauCeti.isFiniteType_cartanMatrix_D 4).submatrix (Equiv.swap _ _).injective
  | .E6 => by
    change TauCeti.IsFiniteType (Tag.cartanE 6)
    rw [cartanE_eq, ← TauCeti.DynkinType.cartanMatrix_E6]
    exact TauCeti.DynkinType.isFiniteType_cartanMatrix_E6
  | .E7 => by
    change TauCeti.IsFiniteType (Tag.cartanE 7)
    rw [cartanE_eq, ← TauCeti.DynkinType.cartanMatrix_E7]
    exact TauCeti.DynkinType.isFiniteType_cartanMatrix_E7
  | .E8 => by
    change TauCeti.IsFiniteType (Tag.cartanE 8)
    rw [cartanE_eq, ← TauCeti.DynkinType.cartanMatrix_E8]
    exact TauCeti.DynkinType.isFiniteType_cartanMatrix_E8

theorem reflection_cartan (τ : Tag) (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    reflection τ.cartan i v = reflect τ i v := by
  rw [reflection_apply]
  rfl

abbrev WeylGroup (τ : Tag) : Type :=
  (coxeterMatrix (isFiniteType_cartan τ)).Group

abbrev coxeterSystem (τ : Tag) :
    CoxeterSystem (coxeterMatrix (isFiniteType_cartan τ)) (WeylGroup τ) :=
  (coxeterMatrix (isFiniteType_cartan τ)).toCoxeterSystem

abbrev simple (τ : Tag) (i : Fin τ.rank) : WeylGroup τ :=
  (coxeterSystem τ).simple i

variable {τ : Tag}

instance instDistribMulActionWeylGroup : DistribMulAction (WeylGroup τ) (Fin τ.rank → ℤ) :=
  DistribMulAction.compHom _ (weylAction (isFiniteType_cartan τ))

theorem smul_def (w : WeylGroup τ) (v : Fin τ.rank → ℤ) :
    w • v = weylAction (isFiniteType_cartan τ) w v :=
  rfl

@[simp] theorem simple_smul (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    simple τ i • v = reflect τ i v := by
  rw [smul_def, weylAction_simple, reflection_cartan]

theorem ext_single {w w' : WeylGroup τ}
    (h : ∀ i, w • (Pi.single i 1 : Fin τ.rank → ℤ) = w' • (Pi.single i 1 : Fin τ.rank → ℤ)) :
    w = w' := by
  refine weylAction_injective (isFiniteType_cartan τ) (LinearMap.pi_ext fun i x => ?_)
  rw [← mul_one x, ← smul_eq_mul, Pi.single_smul, map_smul, map_smul]
  exact congrArg (x • ·) (h i)

instance instFaithfulSMulWeylGroup : FaithfulSMul (WeylGroup τ) (Fin τ.rank → ℤ) :=
  ⟨fun h => ext_single fun _ => h _⟩

instance instFiniteWeylGroup : Finite (WeylGroup τ) :=
  finite_group (isFiniteType_cartan τ)

theorem isRoot_iff_exists_smul_single {v : Fin τ.rank → ℤ} :
    IsRoot τ v ↔ ∃ (w : WeylGroup τ) (j : Fin τ.rank), w • Pi.single j 1 = v := by
  constructor
  · intro h
    induction h with
    | basis j => exact ⟨1, j, one_smul _ _⟩
    | reflect i _ ih =>
      obtain ⟨w, j, rfl⟩ := ih
      exact ⟨simple τ i * w, j, by rw [mul_smul, simple_smul]⟩
  · rintro ⟨w, j, rfl⟩
    induction w using (coxeterSystem τ).simple_induction_left with
    | one => rw [one_smul]; exact .basis j
    | mul_simple_left w i ih => rw [mul_smul, simple_smul]; exact .reflect i ih

theorem isRoot_iff_mem_roots {v : Fin τ.rank → ℤ} :
    IsRoot τ v ↔ v ∈ roots (isFiniteType_cartan τ) ∅ := by
  rw [isRoot_iff_exists_smul_single]
  constructor
  · rintro ⟨w, j, rfl⟩
    exact Or.inl ⟨w, j, rfl⟩
  · rintro (⟨w, j, rfl⟩ | ⟨w, j, hj, -⟩)
    · exact ⟨w, j, rfl⟩
    · exact absurd hj (Set.notMem_empty j)

theorem IsRoot.smul {v : Fin τ.rank → ℤ} (hv : IsRoot τ v) (w : WeylGroup τ) :
    IsRoot τ (w • v) := by
  obtain ⟨w', j, rfl⟩ := isRoot_iff_exists_smul_single.1 hv
  exact isRoot_iff_exists_smul_single.2 ⟨w * w', j, mul_smul _ _ _⟩

theorem isRoot_smul_iff (w : WeylGroup τ) {v : Fin τ.rank → ℤ} : IsRoot τ (w • v) ↔ IsRoot τ v :=
  ⟨fun h => by simpa using IsRoot.smul h w⁻¹, fun h => IsRoot.smul h w⟩

theorem IsRoot.neg {v : Fin τ.rank → ℤ} (hv : IsRoot τ v) : IsRoot τ (-v) := by
  obtain ⟨w, j, rfl⟩ := isRoot_iff_exists_smul_single.1 hv
  rw [← smul_neg, ← reflect_single_self, ← simple_smul, ← mul_smul]
  exact isRoot_iff_exists_smul_single.2 ⟨_, j, rfl⟩

theorem isRoot_neg_iff {v : Fin τ.rank → ℤ} : IsRoot τ (-v) ↔ IsRoot τ v :=
  ⟨fun h => by simpa using IsRoot.neg h, IsRoot.neg⟩

instance instMulActionWeylGroupRoot :
    MulAction (WeylGroup τ) {v : Fin τ.rank → ℤ // IsRoot τ v} where
  smul w α := ⟨w • α.1, IsRoot.smul α.2 w⟩
  one_smul α := Subtype.ext (one_smul _ α.1)
  mul_smul w w' α := Subtype.ext (mul_smul w w' α.1)

@[simp] theorem coe_smul_root (w : WeylGroup τ) (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) :
    ((w • α : {v : Fin τ.rank → ℤ // IsRoot τ v}) : Fin τ.rank → ℤ) = w • (α : Fin τ.rank → ℤ) :=
  rfl

instance instInvolutiveNegRoot : InvolutiveNeg {v : Fin τ.rank → ℤ // IsRoot τ v} where
  neg α := ⟨-α.1, IsRoot.neg α.2⟩
  neg_neg α := Subtype.ext (neg_neg α.1)

@[simp] theorem coe_neg_root (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) :
    ((-α : {v : Fin τ.rank → ℤ // IsRoot τ v}) : Fin τ.rank → ℤ) = -(α : Fin τ.rank → ℤ) :=
  rfl

theorem smul_neg_root (w : WeylGroup τ) (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) :
    w • (-α) = -(w • α) :=
  Subtype.ext (smul_neg w α.1)

@[simp] theorem height_neg (v : Fin τ.rank → ℤ) : height (-v) = -height v := by
  simp [height, Finset.sum_neg_distrib]

@[simp] theorem height_single (i : Fin τ.rank) : height (Pi.single i 1 : Fin τ.rank → ℤ) = 1 := by
  simp [height]

theorem IsRoot.height_pos_iff {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    0 < height α ↔ ∀ j, 0 ≤ α j := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases hα.nonneg_or_nonpos with hs | hs
    · exact hs
    · exact absurd h (not_lt.2 (Finset.sum_nonpos fun j _ => hs j))
  · exact lt_of_le_of_ne (Finset.sum_nonneg fun j _ => h j) hα.height_ne_zero.symm

theorem IsRoot.height_neg_iff {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    height α < 0 ↔ ∀ j, α j ≤ 0 := by
  have h := IsRoot.height_pos_iff (IsRoot.neg hα)
  simp only [height_neg, Left.neg_pos_iff, Pi.neg_apply, Left.nonneg_neg_iff] at h
  exact h

theorem IsRoot.height_pos_or_neg {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    0 < height α ∨ height α < 0 :=
  hα.height_ne_zero.lt_or_gt.symm

theorem reflect_apply_of_ne (i : Fin τ.rank) {j : Fin τ.rank} (h : j ≠ i) (v : Fin τ.rank → ℤ) :
    reflect τ i v j = v j := by
  rw [← reflection_cartan]
  exact reflection_apply_of_ne _ h v

theorem height_reflect_pos {i : Fin τ.rank} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hpos : 0 < height α) (hne : α ≠ Pi.single i 1) : 0 < height (reflect τ i α) := by
  have hnn := (IsRoot.height_pos_iff hα).1 hpos
  obtain ⟨j, hji, hj⟩ : ∃ j, j ≠ i ∧ 0 < α j := by
    by_contra! h
    have hα' : α = α i • Pi.single i 1 := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj, le_antisymm (h j hj) (hnn j)]
    have hroot : IsRoot τ (α i • Pi.single i 1) := by
      rw [← hα']
      exact hα
    rcases (isRoot_smul_single_iff i (α i)).1 hroot with h1 | h1
    · exact hne (by rw [hα', h1, one_smul])
    · have := hnn i
      omega
  have hr := (isRoot_reflect_iff i).2 hα
  rcases hr.nonneg_or_nonpos with h | h
  · exact (IsRoot.height_pos_iff hr).2 h
  · have := h j
    rw [reflect_apply_of_ne i hji] at this
    omega

theorem reflect_ne_single {i : Fin τ.rank} {α : Fin τ.rank → ℤ} (hpos : 0 < height α) :
    reflect τ i α ≠ Pi.single i 1 := by
  intro h
  have : α = -Pi.single i 1 := by rw [← reflect_reflect τ i α, h, reflect_single_self]
  rw [this, height_neg, height_single] at hpos
  omega

theorem bijOn_reflect (i : Fin τ.rank) :
    Set.BijOn (reflect τ i) {α | IsRoot τ α ∧ 0 < height α ∧ α ≠ Pi.single i 1}
      {α | IsRoot τ α ∧ 0 < height α ∧ α ≠ Pi.single i 1} := by
  have hmaps : Set.MapsTo (reflect τ i) {α | IsRoot τ α ∧ 0 < height α ∧ α ≠ Pi.single i 1}
      {α | IsRoot τ α ∧ 0 < height α ∧ α ≠ Pi.single i 1} := fun α ⟨hα, hpos, hne⟩ =>
    ⟨(isRoot_reflect_iff i).2 hα, height_reflect_pos hα hpos hne, reflect_ne_single hpos⟩
  exact Set.InvOn.bijOn ⟨fun α _ => reflect_reflect τ i α, fun α _ => reflect_reflect τ i α⟩
    hmaps hmaps

theorem height_smul_single_pos_or_neg (w : WeylGroup τ) (i : Fin τ.rank) :
    0 < height (w • (Pi.single i 1 : Fin τ.rank → ℤ)) ∨
      height (w • (Pi.single i 1 : Fin τ.rank → ℤ)) < 0 :=
  IsRoot.height_pos_or_neg (IsRoot.smul (isRoot_single τ i) w)

theorem eq_one_of_forall_nonneg {w : WeylGroup τ}
    (h : ∀ i, 0 ≤ w • (Pi.single i 1 : Fin τ.rank → ℤ)) : w = 1 := by
  by_contra hw
  obtain ⟨i, hi⟩ := (coxeterSystem τ).exists_rightDescent_of_ne_one hw
  exact weylAction_single_ne_zero _ w i
    (le_antisymm ((isRightDescent_iff _ w i).1 hi) (h i))

theorem eq_one_of_forall_height_pos {w : WeylGroup τ}
    (h : ∀ i, 0 < height (w • (Pi.single i 1 : Fin τ.rank → ℤ))) : w = 1 :=
  eq_one_of_forall_nonneg fun i =>
    (IsRoot.height_pos_iff (IsRoot.smul (isRoot_single τ i) w)).1 (h i)

theorem exists_height_neg_of_ne_one {w : WeylGroup τ} (hw : w ≠ 1) :
    ∃ i, height (w • (Pi.single i 1 : Fin τ.rank → ℤ)) < 0 := by
  by_contra! h
  exact hw (eq_one_of_forall_height_pos fun i =>
    lt_of_le_of_ne (h i) (IsRoot.smul (isRoot_single τ i) w).height_ne_zero.symm)

end CFSG.LieType.Chevalley
