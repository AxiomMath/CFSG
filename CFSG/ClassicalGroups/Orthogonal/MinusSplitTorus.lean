module

public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194OmegaTorus
public import CFSG.ClassicalGroups.Orthogonal.Models
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalOrthogonalBlocks
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalGroups.Orthogonal.Matrix

public section

namespace CFSG.ClassicalGroups.Orthogonal

open Matrix QuadraticMap CFSG.Open
open CFSG.ComponentClassification.UnbalancingLocal.OrthogonalBlocks
open CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven
open CFSG.LieType.Universal.Spin
open scoped commutatorElement

variable {K : Type} [Field K] {b c : K}

@[expose] def minusFlip (m : ℕ) (i : Fin m) : Equiv.Perm (Fin m ⊕ Fin m ⊕ Fin 2) :=
  Equiv.swap (Sum.inl i) (Sum.inr (Sum.inl i))

theorem minusFlip_inv (m : ℕ) (i : Fin m) : (minusFlip m i)⁻¹ = minusFlip m i :=
  Equiv.symm_swap _ _

theorem minusFlip_mul_self (m : ℕ) (i : Fin m) : minusFlip m i * minusFlip m i = 1 := by
  ext j
  simp [Equiv.Perm.mul_apply, minusFlip, Equiv.swap_apply_self]

@[simp]
theorem minusFlip_apply_inl {m : ℕ} (i : Fin m) :
    minusFlip m i (Sum.inl i) = Sum.inr (Sum.inl i) :=
  Equiv.swap_apply_left _ _

@[simp]
theorem minusFlip_apply_inr {m : ℕ} (i : Fin m) :
    minusFlip m i (Sum.inr (Sum.inl i)) = Sum.inl i :=
  Equiv.swap_apply_right _ _

theorem minusFlip_apply_inl_of_ne {m : ℕ} {i j : Fin m} (h : j ≠ i) :
    minusFlip m i (Sum.inl j) = Sum.inl j :=
  Equiv.swap_apply_of_ne_of_ne (by simpa using h) (by simp)

theorem minusFlip_apply_inr_of_ne {m : ℕ} {i j : Fin m} (h : j ≠ i) :
    minusFlip m i (Sum.inr (Sum.inl j)) = Sum.inr (Sum.inl j) :=
  Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using h)

@[simp]
theorem minusFlip_apply_inr_inr {m : ℕ} (i : Fin m) (k : Fin 2) :
    minusFlip m i (Sum.inr (Sum.inr k)) = Sum.inr (Sum.inr k) :=
  Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)

theorem permGL_minusFlip_mul_self {m : ℕ} (i : Fin m) :
    permGL (K := K) (minusFlip m i) * permGL (K := K) (minusFlip m i) = 1 := by
  rw [← map_mul, minusFlip_mul_self, map_one]

theorem minusFlipVec_ne_zero {n : ℕ} (i : Fin (n - 1)) :
    Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr (Sum.inl i)) 1 ≠
      (0 : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) := by
  intro h
  have := congrFun h (Sum.inl i)
  simp [Pi.add_apply, Pi.single_apply] at this

theorem quadMinus_minusFlipVec {n : ℕ} (i : Fin (n - 1)) :
    quadMinus n K b c (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr (Sum.inl i)) 1) = 1 := by
  have h := QuadraticMap.map_add (quadMinus n K b c)
    (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inr (Sum.inl i)) 1)
  rw [h, quadMinus_single_inl, quadMinus_single_inr, polar_single_inl_quadMinus, zero_add,
    zero_add]
  simp

theorem toLinEquiv_permGL_minusFlip [CharP K 2] {n : ℕ} (i : Fin (n - 1)) :
    toLinEquiv (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K (permGL (K := K) (minusFlip (n - 1) i)) =
      reflect (quadMinus n K b c)
        (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr (Sum.inl i)) 1) := by
  set e : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K :=
    Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr (Sum.inl i)) 1 with he
  have hQe : quadMinus n K b c e = 1 := by
    rw [he]; exact quadMinus_minusFlipVec i
  have hpolar : ∀ v, polar (quadMinus n K b c) e v = v (Sum.inl i) + v (Sum.inr (Sum.inl i)) := by
    intro v
    rw [he, QuadraticMap.polar_add_left, polar_single_inl_quadMinus, polar_single_inr_quadMinus,
      add_comm]
  have hchar1 : ∀ u v : K, u + (u + v) = v := fun u v => by
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hchar2 : ∀ u v : K, v + (u + v) = u := fun u v => by
    rw [add_comm v (u + v), add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hR : ∀ x : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K,
      reflect (quadMinus n K b c) e x = x + (x (Sum.inl i) + x (Sum.inr (Sum.inl i))) • e := by
    intro x
    rw [reflect_apply (by rw [hQe]; exact one_ne_zero), hpolar, hQe, div_one,
      CharTwo.sub_eq_add]
  have hcomp : ∀ x : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K,
      x ∘ ⇑(minusFlip (n - 1) i) =
        x + (x (Sum.inl i) + x (Sum.inr (Sum.inl i))) • e := by
    intro x
    funext j
    rcases j with j | j | j
    · by_cases hj : j = i
      · subst hj
        simp [Function.comp_apply, Pi.add_apply, Pi.smul_apply, he, Pi.single_apply,
          smul_eq_mul, hchar1]
      · simp [Function.comp_apply, minusFlip_apply_inl_of_ne hj, Pi.add_apply, Pi.smul_apply,
          he, Pi.single_apply, smul_eq_mul, hj]
    · by_cases hj : j = i
      · subst hj
        simp [Function.comp_apply, Pi.add_apply, Pi.smul_apply, he, Pi.single_apply,
          smul_eq_mul, hchar2]
      · simp [Function.comp_apply, minusFlip_apply_inr_of_ne hj, Pi.add_apply, Pi.smul_apply,
          he, Pi.single_apply, smul_eq_mul, hj]
    · fin_cases j <;>
        simp [Function.comp_apply, Pi.add_apply, Pi.smul_apply, he, Pi.single_apply,
          smul_eq_mul]
  apply LinearEquiv.ext
  intro v
  rw [toLinEquiv_apply, mulVec_permGL, minusFlip_inv, hcomp v, hR v]

theorem swapMinus_isometry {n : ℕ} (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    StatedQuadMinus n K b c (v ∘ ⇑(swapMinusPerm (n - 1))) = StatedQuadMinus n K b c v := by
  have h1 : ∀ j, (v ∘ ⇑(swapMinusPerm (n - 1))) (Sum.inl j) *
      (v ∘ ⇑(swapMinusPerm (n - 1))) (Sum.inr (Sum.inl j)) =
      v (Sum.inl j) * v (Sum.inr (Sum.inl j)) := by
    intro j
    simp only [Function.comp_apply, swapMinusPerm, swapMinus]
    exact mul_comm _ _
  have h2 : (v ∘ ⇑(swapMinusPerm (n - 1))) (Sum.inr (Sum.inr 0)) = v (Sum.inr (Sum.inr 0)) := by
    simp [Function.comp_apply, swapMinusPerm, swapMinus]
  have h3 : (v ∘ ⇑(swapMinusPerm (n - 1))) (Sum.inr (Sum.inr 1)) = v (Sum.inr (Sum.inr 1)) := by
    simp [Function.comp_apply, swapMinusPerm, swapMinus]
  simp only [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore]
  rw [Finset.sum_congr rfl (fun j _ => h1 j), h2, h3]

theorem torusEntMinus_isometry {n : ℕ} (d : Fin (n - 1) → Kˣ)
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    StatedQuadMinus n K b c
        (fun j => ((torusEntMinus (n - 1) K d j : Kˣ) : K) * v j) =
      StatedQuadMinus n K b c v := by
  have h1 : ∀ j, ((torusEntMinus (n - 1) K d (Sum.inl j) : Kˣ) : K) * v (Sum.inl j) *
      (((torusEntMinus (n - 1) K d (Sum.inr (Sum.inl j)) : Kˣ) : K) *
        v (Sum.inr (Sum.inl j))) = v (Sum.inl j) * v (Sum.inr (Sum.inl j)) := by
    intro j
    simp only [torusEntMinus, MonoidHom.coe_mk, OneHom.coe_mk, Sum.elim_inl, Sum.elim_inr]
    linear_combination (v (Sum.inl j) * v (Sum.inr (Sum.inl j))) * (d j).mul_inv
  have h2 : ((torusEntMinus (n - 1) K d (Sum.inr (Sum.inr 0)) : Kˣ) : K) *
      v (Sum.inr (Sum.inr 0)) = v (Sum.inr (Sum.inr 0)) := by
    simp [torusEntMinus]
  have h3 : ((torusEntMinus (n - 1) K d (Sum.inr (Sum.inr 1)) : Kˣ) : K) *
      v (Sum.inr (Sum.inr 1)) = v (Sum.inr (Sum.inr 1)) := by
    simp [torusEntMinus]
  simp only [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore]
  rw [Finset.sum_congr rfl (fun j _ => h1 j), h2, h3]

theorem torusEntMinus_comp_swap (m : ℕ) (d : Fin m → Kˣ) :
    torusEntMinus m K d ∘ ⇑(swapMinusPerm m) = (torusEntMinus m K d)⁻¹ := by
  funext j
  rcases j with j | j | j <;> simp [torusEntMinus, swapMinusPerm, swapMinus]

@[expose] noncomputable def minusDiagGL {n : ℕ} {r : ℕ} (hr : Odd r) (d : Fin (n - 1) → Kˣ)
    (hd : ∀ j, d j ^ r = 1) : StatedOmega (StatedQuadMinus n K b c) :=
  ⟨diagGL (torusEntMinus (n - 1) K d),
    diagGL_mem_statedOmega (Q := StatedQuadMinus n K b c) swapMinus_isometry hr
      (by
        intro j
        rcases j with j | j | j
        · simpa [torusEntMinus] using hd j
        · simp only [torusEntMinus, MonoidHom.coe_mk, OneHom.coe_mk, Sum.elim_inr,
            Sum.elim_inl]
          rw [inv_pow, hd j, inv_one]
        · simp [torusEntMinus])
      (torusEntMinus_isometry (n := n) (b := b) (c := c) d)
      (fun j => congrFun (torusEntMinus_comp_swap (n - 1) d) j)⟩

@[simp]
theorem coe_minusDiagGL {n : ℕ} {r : ℕ} (hr : Odd r) (d : Fin (n - 1) → Kˣ)
    (hd : ∀ j, d j ^ r = 1) :
    ((minusDiagGL (b := b) (c := c) hr d hd : StatedOmega (StatedQuadMinus n K b c)) :
        GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) = diagGL (torusEntMinus (n - 1) K d) :=
  rfl

theorem orderOf_minusDiagGL_mulSingle {n : ℕ} {r : ℕ} (hr : Odd r) (t : Kˣ) (i : Fin (n - 1))
    (hd : ∀ j, (Pi.mulSingle i t : Fin (n - 1) → Kˣ) j ^ r = 1) :
    orderOf (minusDiagGL (b := b) (c := c) hr (Pi.mulSingle i t) hd) = orderOf t := by
  have hinjGL : Function.Injective (Subgroup.subtype (StatedOmega (StatedQuadMinus n K b c))) :=
    Subtype.coe_injective
  have hinjDiag : Function.Injective (diagGL (K := K) (ι := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)) :=
    fun x y hxy => by
      funext j
      apply Units.ext
      have h := congrArg (fun g : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K =>
        (g : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
          (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) j j) hxy
      simpa [coe_diagGL] using h
  have hinjT : Function.Injective (torusEntMinus (n - 1) K : (Fin (n - 1) → Kˣ) →*
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → Kˣ)) := fun x y hxy => by
    funext j
    have h := congrFun hxy (Sum.inl j)
    simpa [torusEntMinus] using h
  rw [← orderOf_injective (Subgroup.subtype (StatedOmega (StatedQuadMinus n K b c))) hinjGL]
  change orderOf (diagGL (torusEntMinus (n - 1) K (Pi.mulSingle i t))) = orderOf t
  rw [orderOf_injective (diagGL (K := K) (ι := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)) hinjDiag
    (torusEntMinus (n - 1) K (Pi.mulSingle i t))]
  rw [orderOf_injective (torusEntMinus (n - 1) K) hinjT (Pi.mulSingle i t)]
  exact orderOf_piMulSingle (M := fun _ : Fin (n - 1) => Kˣ) i t

theorem commute_minusDiagGL {n : ℕ} {r : ℕ} (hr : Odd r) (d d' : Fin (n - 1) → Kˣ)
    (hd : ∀ j, d j ^ r = 1) (hd' : ∀ j, d' j ^ r = 1) :
    Commute (minusDiagGL (b := b) (c := c) hr d hd)
      (minusDiagGL (b := b) (c := c) hr d' hd') := by
  show minusDiagGL (b := b) (c := c) hr d hd * minusDiagGL (b := b) (c := c) hr d' hd' =
    minusDiagGL (b := b) (c := c) hr d' hd' * minusDiagGL (b := b) (c := c) hr d hd
  apply Subtype.ext
  simp only [Subgroup.coe_mul, coe_minusDiagGL, ← map_mul, mul_comm]

theorem permGL_flip_mul_diagGL_mul_inv {m : ℕ} (i k : Fin m)
    (e : Fin m ⊕ Fin m ⊕ Fin 2 → Kˣ) :
    permGL (K := K) (minusFlip m i) * permGL (K := K) (minusFlip m k) * diagGL e *
        (permGL (K := K) (minusFlip m i) * permGL (K := K) (minusFlip m k))⁻¹
      = diagGL (fun j => e (minusFlip m k (minusFlip m i j))) := by
  have hinv : (permGL (K := K) (minusFlip m i) * permGL (K := K) (minusFlip m k))⁻¹ =
      permGL (K := K) (minusFlip m k) * permGL (K := K) (minusFlip m i) := by
    rw [_root_.mul_inv_rev, ← map_inv, ← map_inv, minusFlip_inv, minusFlip_inv]
  have h1 : permGL (K := K) (minusFlip m k) * diagGL e * permGL (K := K) (minusFlip m k) =
      diagGL (fun j => e (minusFlip m k j)) := by
    rw [permGL_mul_diagGL, minusFlip_inv]
    simp only [mul_assoc]
    rw [permGL_minusFlip_mul_self, mul_one]
  have h2 : permGL (K := K) (minusFlip m i) * diagGL (fun j => e (minusFlip m k j)) =
      diagGL (fun j => e (minusFlip m k (minusFlip m i j))) *
        permGL (K := K) (minusFlip m i) := by
    rw [permGL_mul_diagGL, minusFlip_inv]
  have h3 : permGL (K := K) (minusFlip m i) * permGL (K := K) (minusFlip m k) * diagGL e *
        (permGL (K := K) (minusFlip m k) * permGL (K := K) (minusFlip m i)) =
      permGL (K := K) (minusFlip m i) *
        (permGL (K := K) (minusFlip m k) * diagGL e * permGL (K := K) (minusFlip m k)) *
        permGL (K := K) (minusFlip m i) := by
    simp only [mul_assoc]
  rw [hinv, h3, h1, h2]
  simp only [mul_assoc, permGL_minusFlip_mul_self, mul_one]

theorem permGL_flip_mul_mem_statedOmega [CharP K 2] [Finite K] {n : ℕ}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {i k : Fin (n - 1)} (hik : i ≠ k) :
    permGL (K := K) (minusFlip (n - 1) i) * permGL (K := K) (minusFlip (n - 1) k) ∈
      StatedOmega (StatedQuadMinus n K b c) := by
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite (n := n) (K := K) hirr
  have hH := minusPair_orth (K := K) (b := b) (c := c) (n := n) hik
  obtain ⟨g, hg, hgv⟩ := exists_mem_elementaryGroup_apply_eq hQ hH
    (minusFlipVec_ne_zero (K := K) k) (minusFlipVec_ne_zero (K := K) i)
    (by rw [quadMinus_minusFlipVec, quadMinus_minusFlipVec])
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c) :=
    elementaryGroup_le_orthogonalGroup _ hg
  rw [statedOmega_eq_comap (coe_quadMinus n K b c), Subgroup.mem_comap,
    MulEquiv.coe_toMonoidHom, map_mul, toLinEquiv_permGL_minusFlip,
    toLinEquiv_permGL_minusFlip]
  have heq : reflect (quadMinus n K b c)
        (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr (Sum.inl i)) 1) *
      reflect (quadMinus n K b c)
        (Pi.single (Sum.inl k) 1 + Pi.single (Sum.inr (Sum.inl k)) 1) =
      ⁅g, reflect (quadMinus n K b c)
        (Pi.single (Sum.inl k) 1 + Pi.single (Sum.inr (Sum.inl k)) 1)⁆ := by
    rw [commutatorElement_def, reflect_conj hgO, hgv, reflect_inv]
  rw [heq]
  exact Subgroup.commutator_mem_commutator hgO (reflect_mem_orthogonalGroup _ _)

@[expose] noncomputable def minusPairFlip [CharP K 2] [Finite K] {n : ℕ}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i k : Fin (n - 1)) (hik : i ≠ k) :
    StatedOmega (StatedQuadMinus n K b c) :=
  ⟨permGL (K := K) (minusFlip (n - 1) i) * permGL (K := K) (minusFlip (n - 1) k),
    permGL_flip_mul_mem_statedOmega hirr hik⟩

@[simp]
theorem coe_minusPairFlip [CharP K 2] [Finite K] {n : ℕ}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i k : Fin (n - 1)) (hik : i ≠ k) :
    ((minusPairFlip (b := b) (c := c) hirr i k hik : StatedOmega (StatedQuadMinus n K b c)) :
        GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) =
      permGL (K := K) (minusFlip (n - 1) i) * permGL (K := K) (minusFlip (n - 1) k) :=
  rfl

theorem minusPairFlip_conj_inv [CharP K 2] [Finite K] {n : ℕ}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {r : ℕ} (hr : Odd r) (d : Fin (n - 1) → Kˣ)
    (hd : ∀ j, d j ^ r = 1) {i k : Fin (n - 1)} (hik : i ≠ k)
    (hdσ : ∀ j, torusEntMinus (n - 1) K d (minusFlip (n - 1) k (minusFlip (n - 1) i j)) =
      (torusEntMinus (n - 1) K d j)⁻¹) :
    minusPairFlip (b := b) (c := c) hirr i k hik *
        minusDiagGL (b := b) (c := c) hr d hd *
        (minusPairFlip (b := b) (c := c) hirr i k hik)⁻¹ =
      (minusDiagGL (b := b) (c := c) hr d hd)⁻¹ := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_minusPairFlip, coe_minusDiagGL]
  rw [permGL_flip_mul_diagGL_mul_inv, ← map_inv]
  congr 1
  funext j
  rw [hdσ j, Pi.inv_apply]

theorem minusPairFlip_conj_eq [CharP K 2] [Finite K] {n : ℕ}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {r : ℕ} (hr : Odd r) (d : Fin (n - 1) → Kˣ)
    (hd : ∀ j, d j ^ r = 1) {i k : Fin (n - 1)} (hik : i ≠ k)
    (hdσ : ∀ j, torusEntMinus (n - 1) K d (minusFlip (n - 1) k (minusFlip (n - 1) i j)) =
      torusEntMinus (n - 1) K d j) :
    minusPairFlip (b := b) (c := c) hirr i k hik *
        minusDiagGL (b := b) (c := c) hr d hd *
        (minusPairFlip (b := b) (c := c) hirr i k hik)⁻¹ =
      minusDiagGL (b := b) (c := c) hr d hd := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_minusPairFlip, coe_minusDiagGL]
  rw [permGL_flip_mul_diagGL_mul_inv]
  congr 1
  funext j
  rw [hdσ j]

theorem torusEntMinus_comp_minusFlip_inv {m : ℕ} {d : Fin m → Kˣ} {i k : Fin m} (hik : i ≠ k)
    (h : ∀ j : Fin m, j ≠ i → j ≠ k → d j = 1) :
    torusEntMinus m K d ∘ ⇑(minusFlip m k) ∘ ⇑(minusFlip m i) = (torusEntMinus m K d)⁻¹ := by
  funext x
  rcases x with j | j | u
  · by_cases hji : j = i
    · subst hji
      rw [Function.comp_apply, Function.comp_apply, minusFlip_apply_inl,
        minusFlip_apply_inr_of_ne hik]
      simp [torusEntMinus]
    · by_cases hjk : j = k
      · subst hjk
        rw [Function.comp_apply, Function.comp_apply, minusFlip_apply_inl_of_ne hji,
          minusFlip_apply_inl]
        simp [torusEntMinus]
      · have hd : d j = 1 := h j hji hjk
        rw [Function.comp_apply, Function.comp_apply, minusFlip_apply_inl_of_ne hji,
          minusFlip_apply_inl_of_ne hjk]
        simp [torusEntMinus, hd]
  · by_cases hji : j = i
    · subst hji
      rw [Function.comp_apply, Function.comp_apply, minusFlip_apply_inr,
        minusFlip_apply_inl_of_ne hik]
      simp [torusEntMinus]
    · by_cases hjk : j = k
      · subst hjk
        rw [Function.comp_apply, Function.comp_apply, minusFlip_apply_inr_of_ne hji,
          minusFlip_apply_inr]
        simp [torusEntMinus]
      · have hd : d j = 1 := h j hji hjk
        rw [Function.comp_apply, Function.comp_apply, minusFlip_apply_inr_of_ne hji,
          minusFlip_apply_inr_of_ne hjk]
        simp [torusEntMinus, hd]
  · rw [Function.comp_apply, Function.comp_apply, minusFlip_apply_inr_inr,
      minusFlip_apply_inr_inr]
    simp [torusEntMinus]

theorem torusEntMinus_comp_minusFlip_eq {m : ℕ} {d : Fin m → Kˣ} {i k : Fin m} (hik : i ≠ k)
    (hi : d i = 1) (hk : d k = 1) :
    torusEntMinus m K d ∘ ⇑(minusFlip m k) ∘ ⇑(minusFlip m i) = torusEntMinus m K d := by
  funext x
  rcases x with j | j | u
  · by_cases hji : j = i
    · subst hji
      rw [Function.comp_apply, Function.comp_apply, minusFlip_apply_inl,
        minusFlip_apply_inr_of_ne hik]
      simp [torusEntMinus, hi]
    · by_cases hjk : j = k
      · subst hjk
        rw [Function.comp_apply, Function.comp_apply, minusFlip_apply_inl_of_ne hji,
          minusFlip_apply_inl]
        simp [torusEntMinus, hk]
      · rw [Function.comp_apply, Function.comp_apply, minusFlip_apply_inl_of_ne hji,
          minusFlip_apply_inl_of_ne hjk]
  · by_cases hji : j = i
    · subst hji
      rw [Function.comp_apply, Function.comp_apply, minusFlip_apply_inr,
        minusFlip_apply_inl_of_ne hik]
      simp [torusEntMinus, hi]
    · by_cases hjk : j = k
      · subst hjk
        rw [Function.comp_apply, Function.comp_apply, minusFlip_apply_inr_of_ne hji,
          minusFlip_apply_inr]
        simp [torusEntMinus, hk]
      · rw [Function.comp_apply, Function.comp_apply, minusFlip_apply_inr_of_ne hji,
          minusFlip_apply_inr_of_ne hjk]
  · rw [Function.comp_apply, Function.comp_apply, minusFlip_apply_inr_inr,
      minusFlip_apply_inr_inr]

end CFSG.ClassicalGroups.Orthogonal
