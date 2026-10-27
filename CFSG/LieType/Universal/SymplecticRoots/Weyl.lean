module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Weyl
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.TorusGeneration
import all TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection
import all TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Weyl
import all TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Diagonal.Basic

public section

namespace CFSG.LieType.Universal.Symplectic

open Matrix TauCeti TauCeti.GLSymplecticFin

section General

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {A : Type*} [CommRing A]

theorem transvectionWeylElement_apply {i j : κ} (hij : i ≠ j) (p q : κ) :
    ((transvectionWeylElement (A := A) hij : GL κ A) : Matrix κ κ A) p q =
      if p = Equiv.swap i j q then (if q = i then -1 else 1) else 0 := by
  rw [TauCeti.coe_transvectionWeylElement_apply]
  simp only [Matrix.one_apply, Equiv.swap_apply_def]
  split_ifs <;> grind

theorem transvectionWeylElement_conj {i j : κ} (hij : i ≠ j) {a b : κ} (hab : a ≠ b) (c : A) :
    transvectionWeylElement hij * transvectionUnit hab c * transvectionWeylElement hij.symm =
      transvectionUnit ((Equiv.swap i j).injective.ne hab)
        ((if a = i then -1 else 1) * (if b = i then -1 else 1) * c) := by
  rw [← transvectionWeylElement_inv hij, mul_inv_eq_iff_eq_mul]
  apply Units.ext
  ext p q
  simp only [Units.val_mul, coe_transvectionUnit]
  by_cases hq : q = b
  · subst hq
    rw [Matrix.mul_transvection_apply_same]
    by_cases hp : p = Equiv.swap i j a
    · subst hp
      rw [Matrix.transvection_mul_apply_same, transvectionWeylElement_apply hij,
        transvectionWeylElement_apply hij, transvectionWeylElement_apply hij]
      simp only [Equiv.apply_eq_iff_eq, hab, ite_false, ite_true]
      split_ifs <;> ring
    · rw [Matrix.transvection_mul_apply_of_ne (ha := hp), transvectionWeylElement_apply hij p a]
      simp [hp]
  · rw [Matrix.mul_transvection_apply_of_ne (hb := hq)]
    by_cases hp : p = Equiv.swap i j a
    · subst hp
      rw [Matrix.transvection_mul_apply_same,
        transvectionWeylElement_apply hij (Equiv.swap i j b) q]
      simp [Ne.symm hq]
    · rw [Matrix.transvection_mul_apply_of_ne (ha := hp)]

theorem transvectionUnit_congr {a b a' b' : κ} (h : a ≠ b) (h' : a' ≠ b') (ha : a = a')
    (hb : b = b') {c c' : A} (hc : c = c') : transvectionUnit h c = transvectionUnit h' c' := by
  subst ha hb hc
  rfl

end General

section Symplectic

variable {R : Type*} [CommRing R] {m : ℕ}

local notation "ι" => (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m))

private theorem conj_mul {G : Type*} [Group G] (g x y : G) :
    g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by
  group

private theorem conj_mul_mul {G : Type*} [Group G] (g x y z : G) :
    g * (x * y * z) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) * (g * z * g⁻¹) := by
  group

private theorem swap_inl_inl_inl (i j x : Fin m) :
    Equiv.swap (ι (.inl i)) (ι (.inl j)) (ι (.inl x)) = ι (.inl (Equiv.swap i j x)) := by
  rw [← finSumFinEquiv.injective.map_swap, ← Sum.inl_injective.map_swap]

private theorem swap_inr_inr_inr (i j x : Fin m) :
    Equiv.swap (ι (.inr i)) (ι (.inr j)) (ι (.inr x)) = ι (.inr (Equiv.swap i j x)) := by
  rw [← finSumFinEquiv.injective.map_swap, ← Sum.inr_injective.map_swap]

private theorem swap_inl_inl_inr (i j x : Fin m) :
    Equiv.swap (ι (.inl i)) (ι (.inl j)) (ι (.inr x)) = ι (.inr x) :=
  Equiv.swap_apply_of_ne_of_ne (finSumFinEquiv_inr_ne_inl x i) (finSumFinEquiv_inr_ne_inl x j)

private theorem swap_inr_inr_inl (i j x : Fin m) :
    Equiv.swap (ι (.inr i)) (ι (.inr j)) (ι (.inl x)) = ι (.inl x) :=
  Equiv.swap_apply_of_ne_of_ne (finSumFinEquiv_inl_ne_inr x i) (finSumFinEquiv_inl_ne_inr x j)

private theorem swap_inl_inr_inl_of_ne {k x : Fin m} (h : x ≠ k) :
    Equiv.swap (ι (.inl k)) (ι (.inr k)) (ι (.inl x)) = ι (.inl x) :=
  Equiv.swap_apply_of_ne_of_ne (differenceShortRoot_first_indices_ne h)
    (finSumFinEquiv_inl_ne_inr x k)

private theorem swap_inl_inr_inr_of_ne {k x : Fin m} (h : x ≠ k) :
    Equiv.swap (ι (.inl k)) (ι (.inr k)) (ι (.inr x)) = ι (.inr x) :=
  Equiv.swap_apply_of_ne_of_ne (finSumFinEquiv_inr_ne_inl x k)
    (differenceShortRoot_second_indices_ne h.symm)

theorem shortWeyl_conj_transvectionUnit {i j : Fin m} (hij : i ≠ j)
    {p q : Fin m ⊕ Fin m} (hpq : ι p ≠ ι q) {p' q' : Fin m ⊕ Fin m} (hpq' : ι p' ≠ ι q')
    (hp : Sum.map (Equiv.swap i j) (Equiv.swap i j) p = p')
    (hq : Sum.map (Equiv.swap i j) (Equiv.swap i j) q = q') (c : R) :
    ((differenceShortRootWeylElement hij : GLSymplecticFin m R) : GL (Fin (m + m)) R) *
        transvectionUnit hpq c *
        ((differenceShortRootWeylElement hij : GLSymplecticFin m R) : GL (Fin (m + m)) R)⁻¹ =
      transvectionUnit hpq'
        ((if Sum.elim id id p = i then -1 else 1) * (if Sum.elim id id q = i then -1 else 1) *
          c) := by
  subst hp hq
  rw [coe_differenceShortRootWeylElement, _root_.mul_inv_rev, inv_inv,
    transvectionWeylElement_inv,
    transvectionWeylElement_inv (differenceShortRoot_first_indices_ne hij)]
  have e : ∀ (a b x c d : GL (Fin (m + m)) R), a * b * x * (c * d) = a * (b * x * c) * d := by
    intros; group
  rw [e, transvectionWeylElement_conj, transvectionWeylElement_conj]
  apply transvectionUnit_congr
  · rcases p with x | x <;>
      simp only [Sum.map_inl, Sum.map_inr, swap_inl_inl_inl, swap_inr_inr_inr, swap_inl_inl_inr,
        swap_inr_inr_inl]
  · rcases q with x | x <;>
      simp only [Sum.map_inl, Sum.map_inr, swap_inl_inl_inl, swap_inr_inr_inr, swap_inl_inl_inr,
        swap_inr_inr_inl]
  · rcases p with x | x <;> rcases q with y | y <;>
      simp only [swap_inr_inr_inr, swap_inr_inr_inl, Sum.elim_inl, Sum.elim_inr, id_eq,
        EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_false,
        one_mul, mul_one] <;>
      by_cases hx : x = i <;> by_cases hy : y = i <;> simp [hx, hy]

theorem shortWeyl_conj_positiveLong {i j : Fin m} (hij : i ≠ j) (a : Fin m) (c : R) :
    differenceShortRootWeylElement hij * positiveLongRootTransvectionUnit a c *
        (differenceShortRootWeylElement hij)⁻¹ =
      positiveLongRootTransvectionUnit (Equiv.swap i j a) c := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_positiveLongRootTransvectionUnit,
    coe_positiveLongRootTransvectionUnit, shortWeyl_conj_transvectionUnit hij _
      (finSumFinEquiv_inl_ne_inr _ _) (Sum.map_inl _ _ _) (Sum.map_inr _ _ _)]
  congr 1
  simp only [Sum.elim_inl, Sum.elim_inr, id_eq]
  by_cases ha : a = i <;> simp [ha]

theorem shortWeyl_conj_negativeLong {i j : Fin m} (hij : i ≠ j) (a : Fin m) (c : R) :
    differenceShortRootWeylElement hij * negativeLongRootTransvectionUnit a c *
        (differenceShortRootWeylElement hij)⁻¹ =
      negativeLongRootTransvectionUnit (Equiv.swap i j a) c := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_negativeLongRootTransvectionUnit,
    coe_negativeLongRootTransvectionUnit, shortWeyl_conj_transvectionUnit hij _
      (finSumFinEquiv_inr_ne_inl _ _) (Sum.map_inr _ _ _) (Sum.map_inl _ _ _)]
  congr 1
  simp only [Sum.elim_inl, Sum.elim_inr, id_eq]
  by_cases ha : a = i <;> simp [ha]

theorem shortWeyl_conj_difference {i j : Fin m} (hij : i ≠ j) {a b : Fin m} (hab : a ≠ b)
    (c : R) :
    differenceShortRootWeylElement hij * differenceShortRootUnit hab c *
        (differenceShortRootWeylElement hij)⁻¹ =
      differenceShortRootUnit ((Equiv.swap i j).injective.ne hab)
        ((if a = i then -1 else 1) * (if b = i then -1 else 1) * c) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_differenceShortRootUnit,
    coe_differenceShortRootUnit, conj_mul,
    shortWeyl_conj_transvectionUnit hij _
      (differenceShortRoot_first_indices_ne ((Equiv.swap i j).injective.ne hab))
      (Sum.map_inl _ _ _) (Sum.map_inl _ _ _),
    shortWeyl_conj_transvectionUnit hij _
      (differenceShortRoot_second_indices_ne ((Equiv.swap i j).injective.ne hab))
      (Sum.map_inr _ _ _) (Sum.map_inr _ _ _)]
  simp only [Sum.elim_inl, Sum.elim_inr, id_eq]
  congr 2
  by_cases ha : a = i <;> by_cases hb : b = i <;> simp [ha, hb]

theorem shortWeyl_conj_positiveSum {i j : Fin m} (hij : i ≠ j) {a b : Fin m} (hab : a ≠ b)
    (c : R) :
    differenceShortRootWeylElement hij * positiveSumShortRootUnit hab c *
        (differenceShortRootWeylElement hij)⁻¹ =
      positiveSumShortRootUnit ((Equiv.swap i j).injective.ne hab)
        ((if a = i then -1 else 1) * (if b = i then -1 else 1) * c) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_positiveSumShortRootUnit,
    coe_positiveSumShortRootUnit, conj_mul,
    shortWeyl_conj_transvectionUnit hij _ (finSumFinEquiv_inl_ne_inr _ _)
      (Sum.map_inl _ _ _) (Sum.map_inr _ _ _),
    shortWeyl_conj_transvectionUnit hij _ (finSumFinEquiv_inl_ne_inr _ _)
      (Sum.map_inl _ _ _) (Sum.map_inr _ _ _)]
  simp only [Sum.elim_inl, Sum.elim_inr, id_eq]
  congr 2
  by_cases ha : a = i <;> by_cases hb : b = i <;> simp [ha, hb, mul_comm]

theorem shortWeyl_conj_negativeSum {i j : Fin m} (hij : i ≠ j) {a b : Fin m} (hab : a ≠ b)
    (c : R) :
    differenceShortRootWeylElement hij * negativeSumShortRootUnit hab c *
        (differenceShortRootWeylElement hij)⁻¹ =
      negativeSumShortRootUnit ((Equiv.swap i j).injective.ne hab)
        ((if a = i then -1 else 1) * (if b = i then -1 else 1) * c) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_negativeSumShortRootUnit,
    coe_negativeSumShortRootUnit, conj_mul,
    shortWeyl_conj_transvectionUnit hij _ (finSumFinEquiv_inr_ne_inl _ _)
      (Sum.map_inr _ _ _) (Sum.map_inl _ _ _),
    shortWeyl_conj_transvectionUnit hij _ (finSumFinEquiv_inr_ne_inl _ _)
      (Sum.map_inr _ _ _) (Sum.map_inl _ _ _)]
  simp only [Sum.elim_inl, Sum.elim_inr, id_eq]
  congr 2
  by_cases ha : a = i <;> by_cases hb : b = i <;> simp [ha, hb, mul_comm]

theorem longWeyl_conj_transvectionUnit (k : Fin m) {p q : Fin m ⊕ Fin m} (hpq : ι p ≠ ι q)
    {p' q' : Fin m ⊕ Fin m} (hpq' : ι p' ≠ ι q')
    (hp : Equiv.swap (ι (.inl k)) (ι (.inr k)) (ι p) = ι p')
    (hq : Equiv.swap (ι (.inl k)) (ι (.inr k)) (ι q) = ι q') (c : R) :
    ((positiveLongRootWeylElement k : GLSymplecticFin m R) : GL (Fin (m + m)) R) *
        transvectionUnit hpq c *
        ((positiveLongRootWeylElement k : GLSymplecticFin m R) : GL (Fin (m + m)) R)⁻¹ =
      transvectionUnit hpq'
        ((if p = .inl k then -1 else 1) * (if q = .inl k then -1 else 1) * c) := by
  rw [coe_positiveLongRootWeylElement, transvectionWeylElement_inv, transvectionWeylElement_conj]
  apply transvectionUnit_congr _ _ hp hq
  simp only [EmbeddingLike.apply_eq_iff_eq]

theorem longWeyl_conj_positiveLong_of_ne {k a : Fin m} (ha : a ≠ k) (c : R) :
    positiveLongRootWeylElement k * positiveLongRootTransvectionUnit a c *
        (positiveLongRootWeylElement k)⁻¹ = positiveLongRootTransvectionUnit a c := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_positiveLongRootTransvectionUnit,
    longWeyl_conj_transvectionUnit k _ (finSumFinEquiv_inl_ne_inr a a)
      (swap_inl_inr_inl_of_ne ha) (swap_inl_inr_inr_of_ne ha)]
  congr 1
  simp [ha]

theorem longWeyl_conj_negativeLong_of_ne {k a : Fin m} (ha : a ≠ k) (c : R) :
    positiveLongRootWeylElement k * negativeLongRootTransvectionUnit a c *
        (positiveLongRootWeylElement k)⁻¹ = negativeLongRootTransvectionUnit a c := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_negativeLongRootTransvectionUnit,
    longWeyl_conj_transvectionUnit k _ (finSumFinEquiv_inr_ne_inl a a)
      (swap_inl_inr_inr_of_ne ha) (swap_inl_inr_inl_of_ne ha)]
  congr 1
  simp [ha]

theorem longWeyl_conj_difference_of_ne {k a b : Fin m} (hab : a ≠ b) (ha : a ≠ k) (hb : b ≠ k)
    (c : R) :
    positiveLongRootWeylElement k * differenceShortRootUnit hab c *
        (positiveLongRootWeylElement k)⁻¹ = differenceShortRootUnit hab c := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_differenceShortRootUnit, conj_mul,
    longWeyl_conj_transvectionUnit k _ (differenceShortRoot_first_indices_ne hab)
      (swap_inl_inr_inl_of_ne ha) (swap_inl_inr_inl_of_ne hb),
    longWeyl_conj_transvectionUnit k _ (differenceShortRoot_second_indices_ne hab)
      (swap_inl_inr_inr_of_ne hb) (swap_inl_inr_inr_of_ne ha)]
  congr 2 <;> simp [ha, hb]

theorem longWeyl_conj_difference_left {k b : Fin m} (hkb : k ≠ b) (c : R) :
    positiveLongRootWeylElement k * differenceShortRootUnit hkb c *
        (positiveLongRootWeylElement k)⁻¹ = negativeSumShortRootUnit hkb (-c) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_differenceShortRootUnit,
    coe_negativeSumShortRootUnit, conj_mul,
    longWeyl_conj_transvectionUnit k _ (finSumFinEquiv_inr_ne_inl k b)
      (Equiv.swap_apply_left _ _) (swap_inl_inr_inl_of_ne hkb.symm),
    longWeyl_conj_transvectionUnit k _ (finSumFinEquiv_inr_ne_inl b k)
      (swap_inl_inr_inr_of_ne hkb.symm) (Equiv.swap_apply_right _ _)]
  congr 2 <;> simp [hkb.symm]

theorem longWeyl_conj_difference_right {a k : Fin m} (hak : a ≠ k) (c : R) :
    positiveLongRootWeylElement k * differenceShortRootUnit hak c *
        (positiveLongRootWeylElement k)⁻¹ = positiveSumShortRootUnit hak (-c) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_differenceShortRootUnit,
    coe_positiveSumShortRootUnit, conj_mul,
    longWeyl_conj_transvectionUnit k _ (finSumFinEquiv_inl_ne_inr a k)
      (swap_inl_inr_inl_of_ne hak) (Equiv.swap_apply_left _ _),
    longWeyl_conj_transvectionUnit k _ (finSumFinEquiv_inl_ne_inr k a)
      (Equiv.swap_apply_right _ _) (swap_inl_inr_inr_of_ne hak)]
  congr 2 <;> simp [hak]

theorem longWeyl_conj_positiveSum_of_ne {k a b : Fin m} (hab : a ≠ b) (ha : a ≠ k) (hb : b ≠ k)
    (c : R) :
    positiveLongRootWeylElement k * positiveSumShortRootUnit hab c *
        (positiveLongRootWeylElement k)⁻¹ = positiveSumShortRootUnit hab c := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_positiveSumShortRootUnit, conj_mul,
    longWeyl_conj_transvectionUnit k _ (finSumFinEquiv_inl_ne_inr a b)
      (swap_inl_inr_inl_of_ne ha) (swap_inl_inr_inr_of_ne hb),
    longWeyl_conj_transvectionUnit k _ (finSumFinEquiv_inl_ne_inr b a)
      (swap_inl_inr_inl_of_ne hb) (swap_inl_inr_inr_of_ne ha)]
  congr 2 <;> simp [ha, hb]

theorem longWeyl_conj_positiveSum_right {a k : Fin m} (hak : a ≠ k) (c : R) :
    positiveLongRootWeylElement k * positiveSumShortRootUnit hak c *
        (positiveLongRootWeylElement k)⁻¹ = differenceShortRootUnit hak c := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_positiveSumShortRootUnit,
    coe_differenceShortRootUnit, conj_mul,
    longWeyl_conj_transvectionUnit k _ (differenceShortRoot_first_indices_ne hak)
      (swap_inl_inr_inl_of_ne hak) (Equiv.swap_apply_right _ _),
    longWeyl_conj_transvectionUnit k _ (differenceShortRoot_second_indices_ne hak)
      (Equiv.swap_apply_left _ _) (swap_inl_inr_inr_of_ne hak)]
  congr 2 <;> simp [hak]

theorem longWeyl_conj_negativeSum_of_ne {k a b : Fin m} (hab : a ≠ b) (ha : a ≠ k) (hb : b ≠ k)
    (c : R) :
    positiveLongRootWeylElement k * negativeSumShortRootUnit hab c *
        (positiveLongRootWeylElement k)⁻¹ = negativeSumShortRootUnit hab c := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_negativeSumShortRootUnit, conj_mul,
    longWeyl_conj_transvectionUnit k _ (finSumFinEquiv_inr_ne_inl a b)
      (swap_inl_inr_inr_of_ne ha) (swap_inl_inr_inl_of_ne hb),
    longWeyl_conj_transvectionUnit k _ (finSumFinEquiv_inr_ne_inl b a)
      (swap_inl_inr_inr_of_ne hb) (swap_inl_inr_inl_of_ne ha)]
  congr 2 <;> simp [ha, hb]

theorem longWeyl_conj_negativeSum_right {a k : Fin m} (hak : a ≠ k) (c : R) :
    positiveLongRootWeylElement k * negativeSumShortRootUnit hak c *
        (positiveLongRootWeylElement k)⁻¹ = differenceShortRootUnit hak.symm c := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_negativeSumShortRootUnit,
    coe_differenceShortRootUnit, conj_mul,
    longWeyl_conj_transvectionUnit k _ (differenceShortRoot_second_indices_ne hak.symm)
      (swap_inl_inr_inr_of_ne hak) (Equiv.swap_apply_left _ _),
    longWeyl_conj_transvectionUnit k _ (differenceShortRoot_first_indices_ne hak.symm)
      (Equiv.swap_apply_right _ _) (swap_inl_inr_inl_of_ne hak),
    (commute_transvectionUnit _ _ (finSumFinEquiv_inr_ne_inl k k)
      (finSumFinEquiv_inl_ne_inr a a) _ _).eq]
  congr 2 <;> simp [hak]

private theorem shortWeyl_def {i j : Fin m} (hij : i ≠ j) :
    differenceShortRootWeylElement (R := R) hij =
      differenceShortRootUnit hij 1 * differenceShortRootUnit hij.symm (-1) *
        differenceShortRootUnit hij 1 :=
  rfl

private theorem longWeyl_def (i : Fin m) :
    positiveLongRootWeylElement (R := R) i =
      positiveLongRootTransvectionUnit i 1 * negativeLongRootTransvectionUnit i (-1) *
        positiveLongRootTransvectionUnit i 1 :=
  rfl

private theorem differenceShortRootUnit_congr' {a b a' b' : Fin m} (h : a ≠ b) (h' : a' ≠ b')
    (ha : a = a') (hb : b = b') {c c' : R} (hc : c = c') :
    differenceShortRootUnit h c = differenceShortRootUnit h' c' := by
  subst ha hb hc
  rfl

private theorem shortWeyl_conj_shortWeyl {i j k : Fin m} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) :
    differenceShortRootWeylElement (R := R) hij * differenceShortRootWeylElement hjk *
      (differenceShortRootWeylElement hij)⁻¹ = differenceShortRootWeylElement hik := by
  rw [shortWeyl_def hjk, conj_mul_mul]
  simp only [shortWeyl_conj_difference]
  rw [shortWeyl_def hik]
  have hi := Equiv.swap_apply_right i j
  have hk := Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm
  congr 1
  · congr 1
    · exact differenceShortRootUnit_congr' _ _ hi hk (by simp [hij.symm, hik.symm])
    · exact differenceShortRootUnit_congr' _ _ hk hi (by simp [hij.symm, hik.symm])
  · exact differenceShortRootUnit_congr' _ _ hi hk (by simp [hij.symm, hik.symm])

private theorem shortWeyl_conj_shortWeyl' {i j k : Fin m} (hij : i ≠ j) (hkj : k ≠ j)
    (hik : i ≠ k) :
    differenceShortRootWeylElement (R := R) hkj * differenceShortRootWeylElement hij *
      (differenceShortRootWeylElement hkj)⁻¹ = differenceShortRootWeylElement hik := by
  rw [shortWeyl_def hij, conj_mul_mul]
  simp only [shortWeyl_conj_difference]
  rw [shortWeyl_def hik]
  have hi := Equiv.swap_apply_of_ne_of_ne hik hij
  have hk := Equiv.swap_apply_right k j
  congr 1
  · congr 1
    · exact differenceShortRootUnit_congr' _ _ hi hk (by simp [hik, hkj.symm])
    · exact differenceShortRootUnit_congr' _ _ hk hi (by simp [hik, hkj.symm])
  · exact differenceShortRootUnit_congr' _ _ hi hk (by simp [hik, hkj.symm])

theorem shortWeyl_braid {i j k : Fin m} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    differenceShortRootWeylElement (R := R) hij * differenceShortRootWeylElement hjk *
        differenceShortRootWeylElement hij =
      differenceShortRootWeylElement hjk * differenceShortRootWeylElement hij *
        differenceShortRootWeylElement hjk := by
  have h1 := shortWeyl_conj_shortWeyl (R := R) hij hjk hik
  have h2 := shortWeyl_conj_shortWeyl' (R := R) hij hjk.symm hik
  rw [← differenceShortRootWeylElement_inv hjk] at h2
  calc differenceShortRootWeylElement (R := R) hij * differenceShortRootWeylElement hjk *
        differenceShortRootWeylElement hij
      = differenceShortRootWeylElement hjk *
          ((differenceShortRootWeylElement hjk)⁻¹ * differenceShortRootWeylElement hij *
            ((differenceShortRootWeylElement hjk)⁻¹)⁻¹) * differenceShortRootWeylElement hij := by
        group
    _ = differenceShortRootWeylElement hjk *
          (differenceShortRootWeylElement hij * differenceShortRootWeylElement hjk *
            (differenceShortRootWeylElement hij)⁻¹) * differenceShortRootWeylElement hij := by
        rw [h1, h2]
    _ = differenceShortRootWeylElement hjk * differenceShortRootWeylElement hij *
          differenceShortRootWeylElement hjk := by
        group

theorem shortWeyl_comm {i j k l : Fin m} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) :
    differenceShortRootWeylElement (R := R) hij * differenceShortRootWeylElement hkl =
      differenceShortRootWeylElement hkl * differenceShortRootWeylElement hij := by
  rw [← mul_inv_eq_iff_eq_mul, shortWeyl_def hkl, conj_mul_mul]
  simp only [shortWeyl_conj_difference]
  have hk := Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm
  have hl := Equiv.swap_apply_of_ne_of_ne hil.symm hjl.symm
  congr 1
  · congr 1
    · exact differenceShortRootUnit_congr' _ _ hk hl (by simp [hik.symm, hil.symm])
    · exact differenceShortRootUnit_congr' _ _ hl hk (by simp [hik.symm, hil.symm])
  · exact differenceShortRootUnit_congr' _ _ hk hl (by simp [hik.symm, hil.symm])

theorem shortWeyl_comm_longWeyl {i j k : Fin m} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    differenceShortRootWeylElement (R := R) hij * positiveLongRootWeylElement k =
      positiveLongRootWeylElement k * differenceShortRootWeylElement hij := by
  rw [← mul_inv_eq_iff_eq_mul, longWeyl_def k, conj_mul_mul]
  simp only [shortWeyl_conj_positiveLong, shortWeyl_conj_negativeLong,
    Equiv.swap_apply_of_ne_of_ne hki hkj]

private theorem longWeyl_comm {i j : Fin m} (hij : i ≠ j) :
    positiveLongRootWeylElement (R := R) i * positiveLongRootWeylElement j =
      positiveLongRootWeylElement j * positiveLongRootWeylElement i := by
  rw [← mul_inv_eq_iff_eq_mul, longWeyl_def j, conj_mul_mul]
  simp only [longWeyl_conj_positiveLong_of_ne hij.symm, longWeyl_conj_negativeLong_of_ne hij.symm]

private theorem shortWeyl_conj_longWeyl {i j : Fin m} (hij : i ≠ j) :
    differenceShortRootWeylElement (R := R) hij * positiveLongRootWeylElement j *
      (differenceShortRootWeylElement hij)⁻¹ = positiveLongRootWeylElement i := by
  rw [longWeyl_def j, conj_mul_mul]
  simp only [shortWeyl_conj_positiveLong, shortWeyl_conj_negativeLong, Equiv.swap_apply_right]
  rw [longWeyl_def]

private theorem shortWeyl_conj_longWeyl' {i j : Fin m} (hij : i ≠ j) :
    differenceShortRootWeylElement (R := R) hij * positiveLongRootWeylElement i *
      (differenceShortRootWeylElement hij)⁻¹ = positiveLongRootWeylElement j := by
  rw [longWeyl_def i, conj_mul_mul]
  simp only [shortWeyl_conj_positiveLong, shortWeyl_conj_negativeLong, Equiv.swap_apply_left]
  rw [longWeyl_def]

theorem shortWeyl_longWeyl_braid {i j : Fin m} (hij : i ≠ j) :
    differenceShortRootWeylElement (R := R) hij * positiveLongRootWeylElement j *
        differenceShortRootWeylElement hij * positiveLongRootWeylElement j =
      positiveLongRootWeylElement j * differenceShortRootWeylElement hij *
        positiveLongRootWeylElement j * differenceShortRootWeylElement hij := by
  have e1 := shortWeyl_conj_longWeyl (R := R) hij
  have e2 := shortWeyl_conj_longWeyl' (R := R) hij
  have h3 := longWeyl_comm (R := R) hij
  rw [mul_inv_eq_iff_eq_mul] at e1 e2
  set u := differenceShortRootWeylElement (R := R) hij
  set v := positiveLongRootWeylElement (R := R) j
  set v' := positiveLongRootWeylElement (R := R) i
  calc u * v * u * v = (u * v) * (u * v) := by group
    _ = (v' * u) * (v' * u) := by rw [e1]
    _ = v' * (u * v') * u := by group
    _ = v' * (v * u) * u := by rw [e2]
    _ = (v' * v) * u * u := by group
    _ = (v * v') * u * u := by rw [h3]
    _ = v * (v' * u) * u := by group
    _ = v * (u * v) * u := by rw [e1]
    _ = v * u * v * u := by group

private theorem diagonal_eq_leviHom (t : Fin m → Rˣ) : diagonal t = leviHom (diagGL t) :=
  rfl

theorem differenceShortRootUnit_inv {i j : Fin m} (hij : i ≠ j) (c : R) :
    (differenceShortRootUnit hij c)⁻¹ = differenceShortRootUnit hij (-c) := by
  simpa only [differenceShortRootHom_apply, toAdd_ofAdd, toAdd_inv] using
    (map_inv (differenceShortRootHom (R := R) hij) (Multiplicative.ofAdd c)).symm

theorem diagonal_twoPoint_eq {i j : Fin m} (hij : i ≠ j) (a : Rˣ) :
    diagonal (fun x => if x = i then a else if x = j then a⁻¹ else 1) =
      differenceShortRootUnit hij (a : R) * differenceShortRootUnit hij.symm (-((a⁻¹ : Rˣ) : R)) *
        differenceShortRootUnit hij (a : R) * differenceShortRootUnit hij (-1) *
        differenceShortRootUnit hij.symm 1 * differenceShortRootUnit hij (-1) := by
  have h : (diagGL fun x => if x = i then a else if x = j then a⁻¹ else 1 : GL (Fin m) R) =
      Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.diag2nUnit hij a) := by
    apply Units.ext
    rw [diagGL_coe, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.diag2nUnit_coe]
    congr 1
    funext x
    split_ifs <;> rfl
  rw [diagonal_eq_leviHom, h, Matrix.SpecialLinearGroup.diag2nUnit_decompose]
  simp only [map_mul, leviHom_transvection]

theorem diagonal_mulSingle_eq (i : Fin m) (a : Rˣ) :
    diagonal (Pi.mulSingle i a) =
      positiveLongRootTransvectionUnit i (a : R) *
        negativeLongRootTransvectionUnit i (-((a⁻¹ : Rˣ) : R)) *
        positiveLongRootTransvectionUnit i (a : R) *
        positiveLongRootTransvectionUnit i (-1) *
        negativeLongRootTransvectionUnit i 1 *
        positiveLongRootTransvectionUnit i (-1) := by
  rw [diagonal_eq_leviHom, leviHom_diagGL_mulSingle]

theorem shortWeyl_sq {i j : Fin m} (hij : i ≠ j) :
    differenceShortRootWeylElement (R := R) hij ^ 2 =
      (diagonal fun x => if x = i then (-1 : Rˣ) else if x = j then (-1)⁻¹ else 1)⁻¹ := by
  rw [diagonal_twoPoint_eq hij, shortWeyl_def]
  simp only [_root_.mul_inv_rev, differenceShortRootUnit_inv, inv_neg, inv_one, Units.val_neg,
    Units.val_one, neg_neg, pow_two, mul_assoc]

theorem longWeyl_sq (i : Fin m) :
    positiveLongRootWeylElement (R := R) i ^ 2 = (diagonal (Pi.mulSingle i (-1 : Rˣ)))⁻¹ := by
  rw [diagonal_mulSingle_eq, longWeyl_def]
  simp only [_root_.mul_inv_rev, positiveLongRootTransvectionUnit_inv,
    negativeLongRootTransvectionUnit_inv, inv_neg, inv_one, Units.val_neg, Units.val_one,
    neg_neg, pow_two, mul_assoc]

end Symplectic

end CFSG.LieType.Universal.Symplectic
