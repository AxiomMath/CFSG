module

public import CFSG.ClassicalInvolution.WeakCT.Torus
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg.Sp (blockMat blockMat_injective blockMat_mul)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.ClassicalInvolution.WeakCT (torusHom diagTorus2 mem_diagTorus2_iff coe_torusHom)
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] {n : ℕ} {i j : Fin n}

@[expose] def planeTorusDiag (i j : Fin n) (a b : Kˣ) : Fin n ⊕ Fin n → K := fun x =>
  if x = Sum.inl i then (a : K) else if x = Sum.inr i then ((a⁻¹ : Kˣ) : K)
  else if x = Sum.inl j then (b : K) else if x = Sum.inr j then ((b⁻¹ : Kˣ) : K) else 1

@[expose] noncomputable def planeTorusElt (K : Type) [Field K] (i j : Fin n) (a b : Kˣ) :
    StatedSp n K :=
  longBlock K n i (torusHom K a) * longBlock K n j (torusHom K b)

theorem blockMat_torusDiag (k : Fin n) (a : Kˣ) :
    blockMat (Sum.inl k) (Sum.inr k) !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)] =
      Matrix.diagonal (fun x : Fin n ⊕ Fin n =>
        if x = Sum.inl k then (a : K) else if x = Sum.inr k then ((a⁻¹ : Kˣ) : K) else 1) := by
  have hpq : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k := Sum.inl_ne_inr
  ext r t
  simp only [blockMat, Matrix.of_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hr1 : r = Sum.inl k
  · subst hr1
    by_cases ht1 : t = Sum.inl k
    · subst ht1; simp
    · by_cases ht2 : t = Sum.inr k
      · subst ht2; simp [hpq]
      · simp [ht1, ht2, Ne.symm ht1]
  · by_cases hr2 : r = Sum.inr k
    · subst hr2
      by_cases ht1 : t = Sum.inl k
      · subst ht1; simp [hpq.symm]
      · by_cases ht2 : t = Sum.inr k
        · subst ht2; simp [hpq.symm]
        · simp [ht1, ht2, hpq.symm, Ne.symm ht2]
    · simp [hr1, hr2]


theorem mat_planeTorusElt (hij : i ≠ j) (a b : Kˣ) :
    mat n K (planeTorusElt K i j a b) = Matrix.diagonal (planeTorusDiag i j a b) := by
  rw [planeTorusElt, map_mul, mat_longBlock, mat_longBlock, coe_torusHom, coe_torusHom,
    blockMat_torusDiag, blockMat_torusDiag, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  have h1 : (Sum.inl i : Fin n ⊕ Fin n) ≠ Sum.inl j := fun h => hij (Sum.inl_injective h)
  have h2 : (Sum.inl i : Fin n ⊕ Fin n) ≠ Sum.inr j := Sum.inl_ne_inr
  have h3 : (Sum.inr i : Fin n ⊕ Fin n) ≠ Sum.inl j := Sum.inr_ne_inl
  have h4 : (Sum.inr i : Fin n ⊕ Fin n) ≠ Sum.inr j := fun h => hij (Sum.inr_injective h)
  simp only [planeTorusDiag]
  by_cases hx1 : x = Sum.inl i
  · subst hx1; simp [h1, h2]
  · by_cases hx2 : x = Sum.inr i
    · subst hx2; simp [h3, h4]
    · by_cases hx3 : x = Sum.inl j
      · subst hx3; simp [hx1, hx2]
      · by_cases hx4 : x = Sum.inr j
        · subst hx4; simp [hx1, hx2]
        · simp [hx1, hx2, hx3, hx4]


theorem commute_planeTorusElt_iff (hij : i ≠ j) (a b : Kˣ) (g : StatedSp n K) :
    Commute g (planeTorusElt K i j a b) ↔
      ∀ r t, mat n K g r t * planeTorusDiag i j a b t =
        planeTorusDiag i j a b r * mat n K g r t := by
  constructor
  · intro h r t
    have := congrFun (congrFun (congrArg (mat n K) h.eq) r) t
    rwa [map_mul, map_mul, mat_planeTorusElt hij, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  · intro h
    show g * planeTorusElt K i j a b = planeTorusElt K i j a b * g
    refine mat_injective ?_
    rw [map_mul, map_mul, mat_planeTorusElt hij]
    ext r t
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    exact h r t


theorem gram_mul_apply (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (r t : Fin n ⊕ Fin n) :
    (gram K n * M) r t = sgn K r * M (par r) t := by
  simp only [Matrix.mul_apply, gram_apply]
  rw [Finset.sum_eq_single (par r)]
  · simp
  · intro d _ hd
    rw [ite_eq_right_iff.mpr (fun h => absurd h hd), zero_mul]
  · simp

theorem mat_inv_eq (g : StatedSp n K) :
    mat n K g⁻¹ = -(gram K n * (mat n K g)ᵀ * gram K n) := by
  have h1 : mat n K g * mat n K g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h2 : (-(gram K n * (mat n K g)ᵀ * gram K n)) * mat n K g = 1 := by
    calc (-(gram K n * (mat n K g)ᵀ * gram K n)) * mat n K g
        = -(gram K n * ((mat n K g)ᵀ * gram K n * mat n K g)) := by
          simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = 1 := by rw [mat_transpose_mul_gram_mul, gram_mul_gram, neg_neg]
  exact (left_inv_eq_right_inv h2 h1).symm

theorem mat_inv_apply (g : StatedSp n K) (r t : Fin n ⊕ Fin n) :
    mat n K g⁻¹ r t = sgn K r * sgn K t * mat n K g (par t) (par r) := by
  rw [mat_inv_eq, Matrix.neg_apply, Matrix.mul_assoc, gram_mul_apply, transpose_mul_gram_apply]
  rcases t with t | t <;> simp [sgn, par]


section Levi

theorem planeTorusDiag_inl_same (a : Kˣ) (x : Fin n) :
    planeTorusDiag i j a a (Sum.inl x) = if x = i ∨ x = j then (a : K) else 1 := by
  simp only [planeTorusDiag, Sum.inl.injEq, reduceCtorEq, ite_false]
  by_cases h1 : x = i
  · simp [h1]
  · by_cases h2 : x = j
    · simp [h2]
    · simp [h1, h2]

theorem planeTorusDiag_inr_same (a : Kˣ) (x : Fin n) :
    planeTorusDiag i j a a (Sum.inr x) = if x = i ∨ x = j then ((a⁻¹ : Kˣ) : K) else 1 := by
  simp only [planeTorusDiag, Sum.inr.injEq, reduceCtorEq, ite_false]
  by_cases h1 : x = i
  · simp [h1]
  · by_cases h2 : x = j
    · simp [h2]
    · simp [h1, h2]

variable {a : Kˣ}

@[expose] noncomputable def leviCent (K : Type) [Field K] (i j : Fin n) (a : Kˣ) :
    Subgroup (StatedSp n K) :=
  suppGroup (coords i ∪ coords j) ⊓ Subgroup.centralizer {planeTorusElt K i j a a}

theorem mem_leviCent {g : StatedSp n K} :
    g ∈ leviCent K i j a ↔ g ∈ suppGroup (coords i ∪ coords j) ∧
      Commute g (planeTorusElt K i j a a) := by
  simp only [leviCent, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
    forall_eq]
  exact Iff.rfl.and ⟨fun h => (h).symm, fun h => h.symm⟩

theorem leviCent_inl_inr (hij : i ≠ j) (ha : (a : K) ≠ ((a⁻¹ : Kˣ) : K)) {g : StatedSp n K}
    (hg : g ∈ leviCent K i j a) (x y : Fin n) : mat n K g (Sum.inl x) (Sum.inr y) = 0 := by
  obtain ⟨hs, hc⟩ := mem_leviCent.1 hg
  by_cases h : (x = i ∨ x = j) ∧ (y = i ∨ y = j)
  · have := (commute_planeTorusElt_iff hij a a g).1 hc (Sum.inl x) (Sum.inr y)
    rw [planeTorusDiag_inr_same, planeTorusDiag_inl_same, ite_eq_left h.2, ite_eq_left h.1] at this
    have h' : mat n K g (Sum.inl x) (Sum.inr y) * (((a⁻¹ : Kˣ) : K) - a) = 0 := by
      linear_combination this
    exact (mul_eq_zero.1 h').resolve_right (sub_ne_zero.2 (Ne.symm ha))
  · rw [hs (Sum.inl x) (Sum.inr y)
      (fun h' => h ⟨inl_mem_union_iff.1 h'.1, inr_mem_union_iff.1 h'.2⟩)]
    exact Matrix.one_apply_ne Sum.inl_ne_inr

theorem leviCent_inr_inl (hij : i ≠ j) (ha : (a : K) ≠ ((a⁻¹ : Kˣ) : K)) {g : StatedSp n K}
    (hg : g ∈ leviCent K i j a) (x y : Fin n) : mat n K g (Sum.inr x) (Sum.inl y) = 0 := by
  obtain ⟨hs, hc⟩ := mem_leviCent.1 hg
  by_cases h : (x = i ∨ x = j) ∧ (y = i ∨ y = j)
  · have := (commute_planeTorusElt_iff hij a a g).1 hc (Sum.inr x) (Sum.inl y)
    rw [planeTorusDiag_inr_same, planeTorusDiag_inl_same, ite_eq_left h.2, ite_eq_left h.1] at this
    have h' : mat n K g (Sum.inr x) (Sum.inl y) * (a - ((a⁻¹ : Kˣ) : K)) = 0 := by
      linear_combination this
    exact (mul_eq_zero.1 h').resolve_right (sub_ne_zero.2 ha)
  · rw [hs (Sum.inr x) (Sum.inl y)
      (fun h' => h ⟨inr_mem_union_iff.1 h'.1, inl_mem_union_iff.1 h'.2⟩)]
    exact Matrix.one_apply_ne Sum.inr_ne_inl

@[expose] noncomputable def leviBlkL (g : StatedSp n K) : Matrix (Fin n) (Fin n) K :=
  (mat n K g).toBlocks₁₁

@[expose] noncomputable def leviBlkR (g : StatedSp n K) : Matrix (Fin n) (Fin n) K :=
  (mat n K g).toBlocks₂₂

theorem mat_eq_fromBlocks (hij : i ≠ j) (ha : (a : K) ≠ ((a⁻¹ : Kˣ) : K)) {g : StatedSp n K}
    (hg : g ∈ leviCent K i j a) : mat n K g = fromBlocks (leviBlkL g) 0 0 (leviBlkR g) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (mat n K g)]
  have h12 : (mat n K g).toBlocks₁₂ = 0 := by
    ext x y
    exact leviCent_inl_inr hij ha hg x y
  have h21 : (mat n K g).toBlocks₂₁ = 0 := by
    ext x y
    exact leviCent_inr_inl hij ha hg x y
  rw [h12, h21]
  rfl

theorem leviBlkL_one : leviBlkL (1 : StatedSp n K) = 1 := by
  rw [leviBlkL, map_one]
  ext x y
  simp [Matrix.toBlocks₁₁, Matrix.one_apply]

theorem leviBlkL_mul (hij : i ≠ j) (ha : (a : K) ≠ ((a⁻¹ : Kˣ) : K)) {g h : StatedSp n K}
    (hg : g ∈ leviCent K i j a) (hh : h ∈ leviCent K i j a) :
    leviBlkL (g * h) = leviBlkL g * leviBlkL h := by
  have := mat_eq_fromBlocks hij ha hg
  have h2 := mat_eq_fromBlocks hij ha hh
  rw [leviBlkL, map_mul, this, h2, Matrix.fromBlocks_multiply]
  simp [Matrix.toBlocks_fromBlocks₁₁, leviBlkL]

theorem leviBlkL_inv_eq (g : StatedSp n K) : leviBlkL g⁻¹ = (leviBlkR g)ᵀ := by
  ext x y
  simp [leviBlkL, leviBlkR, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, mat_inv_apply]

@[expose] noncomputable def leviBlk2 (i j : Fin n) (g : StatedSp n K) : Matrix (Fin 2) (Fin 2) K :=
  !![mat n K g (Sum.inl i) (Sum.inl i), mat n K g (Sum.inl i) (Sum.inl j);
    mat n K g (Sum.inl j) (Sum.inl i), mat n K g (Sum.inl j) (Sum.inl j)]

theorem leviBlkL_eq_blockMat (hij : i ≠ j) {g : StatedSp n K}
    (hg : g ∈ suppGroup (coords i ∪ coords j)) : leviBlkL g = blockMat i j (leviBlk2 i j g) := by
  ext x y
  by_cases h : (x = i ∨ x = j) ∧ (y = i ∨ y = j)
  · have hji : j ≠ i := hij.symm
    rcases h with ⟨hx | hx, hy | hy⟩ <;> subst hx <;> subst hy <;>
      simp [leviBlkL, leviBlk2, blockMat, Matrix.toBlocks₁₁, hji]
  · rw [blockMat_apply_of_not hij _ h]
    simp only [leviBlkL, Matrix.toBlocks₁₁, Matrix.of_apply]
    rw [hg (Sum.inl x) (Sum.inl y)
      (fun h' => h ⟨inl_mem_union_iff.1 h'.1, inl_mem_union_iff.1 h'.2⟩)]
    simp [Matrix.one_apply]

theorem commute_shortBlock_planeTorusElt (hij : i ≠ j) (a : Kˣ) (A : SL(2, K)) :
    Commute (shortBlock K hij A) (planeTorusElt K i j a a) := by
  refine (commute_planeTorusElt_iff hij a a _).2 fun r t => ?_
  rw [mat_shortBlock]
  rcases r with r | r <;> rcases t with t | t
  · rw [Matrix.fromBlocks_apply₁₁]
    by_cases h : (r = i ∨ r = j) ∧ (t = i ∨ t = j)
    · rw [planeTorusDiag_inl_same, planeTorusDiag_inl_same, ite_eq_left h.1, ite_eq_left h.2,
        mul_comm]
    · rw [blockMat_apply_of_not hij _ h, Matrix.one_apply]
      by_cases hrt : r = t
      · subst hrt; simp [mul_comm]
      · simp [hrt]
  · simp [Matrix.fromBlocks_apply₁₂]
  · simp [Matrix.fromBlocks_apply₂₁]
  · rw [Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply]
    by_cases h : (t = i ∨ t = j) ∧ (r = i ∨ r = j)
    · rw [planeTorusDiag_inr_same, planeTorusDiag_inr_same, ite_eq_left h.1, ite_eq_left h.2,
        mul_comm]
    · rw [blockMat_apply_of_not hij _ h, Matrix.one_apply]
      by_cases hrt : t = r
      · subst hrt; simp [mul_comm]
      · simp [hrt]

theorem shortBlock_mem_leviCent (hij : i ≠ j) (a : Kˣ) (A : SL(2, K)) :
    shortBlock K hij A ∈ leviCent K i j a :=
  mem_leviCent.2 ⟨isSupp_shortBlock hij A, commute_shortBlock_planeTorusElt hij a A⟩

theorem leviBlk2_shortBlock (hij : i ≠ j) (A : SL(2, K)) :
    leviBlk2 i j (shortBlock K hij A) = A := by
  have h := leviBlkL_eq_blockMat hij (isSupp_shortBlock hij A)
  have h' : leviBlkL (shortBlock K hij A) = blockMat i j (A : Matrix (Fin 2) (Fin 2) K) := by
    rw [leviBlkL, mat_shortBlock, Matrix.toBlocks_fromBlocks₁₁]
  exact blockMat_injective hij (h.symm.trans h')

theorem leviBlk2_mul (hij : i ≠ j) (ha : (a : K) ≠ ((a⁻¹ : Kˣ) : K)) {g h : StatedSp n K}
    (hg : g ∈ leviCent K i j a) (hh : h ∈ leviCent K i j a) :
    leviBlk2 i j (g * h) = leviBlk2 i j g * leviBlk2 i j h := by
  have e1 := leviBlkL_eq_blockMat hij (mem_leviCent.1 (mul_mem hg hh)).1
  have e2 := leviBlkL_eq_blockMat hij (mem_leviCent.1 hg).1
  have e3 := leviBlkL_eq_blockMat hij (mem_leviCent.1 hh).1
  rw [leviBlkL_mul hij ha hg hh, e2, e3, ← blockMat_mul hij] at e1
  exact (blockMat_injective hij e1).symm

theorem leviBlk2_one (hij : i ≠ j) : leviBlk2 i j (1 : StatedSp n K) = 1 := by
  have hji : j ≠ i := hij.symm
  ext x y
  fin_cases x <;> fin_cases y <;> simp [leviBlk2, hij, hji]

theorem leviBlk2_inv (hij : i ≠ j) (ha : (a : K) ≠ ((a⁻¹ : Kˣ) : K)) {g : StatedSp n K}
    (hg : g ∈ leviCent K i j a) : leviBlk2 i j g⁻¹ = (leviBlk2 i j g)⁻¹ := by
  have h1 : leviBlk2 i j g * leviBlk2 i j g⁻¹ = 1 := by
    rw [← leviBlk2_mul hij ha hg (inv_mem hg), mul_inv_cancel, leviBlk2_one hij]
  exact (Matrix.inv_eq_right_inv h1).symm

theorem det_leviBlk2_commutator (hij : i ≠ j) (ha : (a : K) ≠ ((a⁻¹ : Kˣ) : K)) {g h : StatedSp n K}
    (hg : g ∈ leviCent K i j a) (hh : h ∈ leviCent K i j a) :
    (leviBlk2 i j ⁅g, h⁆).det = 1 := by
  have hc : ⁅g, h⁆ = g * h * g⁻¹ * h⁻¹ := commutatorElement_def g h
  have hd : ∀ x ∈ leviCent K i j a, (leviBlk2 i j x).det * (leviBlk2 i j x⁻¹).det = 1 :=
    fun x hx => by
    rw [← Matrix.det_mul, ← leviBlk2_mul hij ha hx (inv_mem hx), mul_inv_cancel, leviBlk2_one hij,
      Matrix.det_one]
  rw [hc, leviBlk2_mul hij ha (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh),
    leviBlk2_mul hij ha (mul_mem hg hh) (inv_mem hg), leviBlk2_mul hij ha hg hh]
  simp only [Matrix.det_mul]
  calc _ = ((leviBlk2 i j g).det * (leviBlk2 i j g⁻¹).det) *
        ((leviBlk2 i j h).det * (leviBlk2 i j h⁻¹).det) := by ring
    _ = 1 := by rw [hd g hg, hd h hh, one_mul]

theorem mem_range_shortBlock_of_det (hij : i ≠ j) (ha : (a : K) ≠ ((a⁻¹ : Kˣ) : K))
    {g : StatedSp n K} (hg : g ∈ leviCent K i j a) (hdet : (leviBlk2 i j g).det = 1) :
    g ∈ (shortBlock K hij).range := by
  refine ⟨mkSL (leviBlk2 i j g) hdet, ?_⟩
  set s := shortBlock K hij (mkSL (leviBlk2 i j g) hdet) with hs
  have hsC : s ∈ leviCent K i j a := shortBlock_mem_leviCent hij a _
  have hbl : leviBlkL s = leviBlkL g := by
    rw [leviBlkL_eq_blockMat hij (mem_leviCent.1 hsC).1,
      leviBlkL_eq_blockMat hij (mem_leviCent.1 hg).1,
      hs, leviBlk2_shortBlock hij, coe_mkSL]
  have hR : ∀ x ∈ leviCent K i j a, leviBlkR x = ((leviBlkL x)⁻¹)ᵀ := fun x hx => by
    have h1 : leviBlkL x * leviBlkL x⁻¹ = 1 := by
      rw [← leviBlkL_mul hij ha hx (inv_mem hx), mul_inv_cancel, leviBlkL_one]
    have h2 : (leviBlkL x)⁻¹ = leviBlkL x⁻¹ := Matrix.inv_eq_right_inv h1
    rw [h2, leviBlkL_inv_eq, Matrix.transpose_transpose]
  apply mat_injective
  rw [mat_eq_fromBlocks hij ha hsC, mat_eq_fromBlocks hij ha hg, hbl, hR s hsC, hR g hg, hbl]

theorem commutator_leviCent_le (hij : i ≠ j) (ha : (a : K) ≠ ((a⁻¹ : Kˣ) : K)) :
    ⁅leviCent K i j a, leviCent K i j a⁆ ≤ (shortBlock K hij).range := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  have hc : ⁅g, h⁆ ∈ leviCent K i j a := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  exact mem_range_shortBlock_of_det hij ha hc (det_leviBlk2_commutator hij ha hg hh)

theorem sq_ne_one_of_ne_inv_unit (ha : (a : K) ≠ ((a⁻¹ : Kˣ) : K)) : (a : K) ^ 2 ≠ 1 := by
  intro h
  apply ha
  have h1 : (a : K) * (a : K) = 1 := by rw [← sq]; exact h
  rw [Units.val_inv_eq_inv_val]
  exact (eq_inv_of_mul_eq_one_left h1)

theorem range_shortBlock_le_commutator (hij : i ≠ j) (ha : (a : K) ≠ ((a⁻¹ : Kˣ) : K)) :
    (shortBlock K hij).range ≤ ⁅leviCent K i j a, leviCent K i j a⁆ := by
  have hperf : commutator SL(2, K) = ⊤ := Matrix.SL2.commutator_eq_top a.ne_zero
    (sq_ne_one_of_ne_inv_unit ha)
  have hle : (shortBlock K hij).range ≤ leviCent K i j a := by
    rintro _ ⟨A, rfl⟩
    exact shortBlock_mem_leviCent hij a A
  rw [MonoidHom.range_eq_map, ← hperf]
  rw [commutator_def, Subgroup.map_commutator]
  refine Subgroup.commutator_mono ?_ ?_ <;> rw [← MonoidHom.range_eq_map] <;> exact hle

theorem commutator_leviCent (hij : i ≠ j) (ha : (a : K) ≠ ((a⁻¹ : Kˣ) : K)) :
    ⁅leviCent K i j a, leviCent K i j a⁆ = (shortBlock K hij).range :=
  le_antisymm (commutator_leviCent_le hij ha) (range_shortBlock_le_commutator hij ha)

end Levi

section General

theorem planeTorusDiag_inl_i (a b : Kˣ) : planeTorusDiag i j a b (Sum.inl i) = (a : K) := by
  simp [planeTorusDiag]

theorem planeTorusDiag_inr_i (a b : Kˣ) :
    planeTorusDiag i j a b (Sum.inr i) = ((a⁻¹ : Kˣ) : K) := by
  simp [planeTorusDiag]

theorem planeTorusDiag_inl_j (hij : i ≠ j) (a b : Kˣ) :
    planeTorusDiag i j a b (Sum.inl j) = (b : K) := by
  simp [planeTorusDiag, hij.symm]

theorem planeTorusDiag_inr_j (hij : i ≠ j) (a b : Kˣ) :
    planeTorusDiag i j a b (Sum.inr j) = ((b⁻¹ : Kˣ) : K) := by
  simp [planeTorusDiag, hij.symm]

theorem planeTorusDiag_of_not_mem (a b : Kˣ) {r : Fin n ⊕ Fin n}
    (h : r ∉ coords i ∪ coords j) : planeTorusDiag i j a b r = 1 := by
  have h1 : r ≠ Sum.inl i := fun e => h (Or.inl (e ▸ inl_mem_coords i))
  have h2 : r ≠ Sum.inr i := fun e => h (Or.inl (e ▸ inr_mem_coords i))
  have h3 : r ≠ Sum.inl j := fun e => h (Or.inr (e ▸ inl_mem_coords j))
  have h4 : r ≠ Sum.inr j := fun e => h (Or.inr (e ▸ inr_mem_coords j))
  simp [planeTorusDiag, h1, h2, h3, h4]

theorem planeTorusDiag_ne_of_cross (hij : i ≠ j) {a b : Kˣ} (hab : a ≠ b) (hab' : a ≠ b⁻¹)
    {r t : Fin n ⊕ Fin n} (hr : r ∈ coords i) (ht : t ∈ coords j) :
    planeTorusDiag i j a b r ≠ planeTorusDiag i j a b t := by
  have e1 : (a : K) ≠ (b : K) := fun h => hab (Units.ext h)
  have e2 : (a : K) ≠ ((b⁻¹ : Kˣ) : K) := fun h => hab' (Units.ext h)
  have e3 : ((a⁻¹ : Kˣ) : K) ≠ (b : K) := fun h => hab' (by
    have : a⁻¹ = b := Units.ext h
    rw [← this, inv_inv])
  have e4 : ((a⁻¹ : Kˣ) : K) ≠ ((b⁻¹ : Kˣ) : K) := fun h => hab (by
    have : a⁻¹ = b⁻¹ := Units.ext h
    exact inv_injective this)
  rcases mem_coords.1 hr with rfl | rfl <;> rcases mem_coords.1 ht with rfl | rfl
  · rw [planeTorusDiag_inl_i, planeTorusDiag_inl_j hij]; exact e1
  · rw [planeTorusDiag_inl_i, planeTorusDiag_inr_j hij]; exact e2
  · rw [planeTorusDiag_inr_i, planeTorusDiag_inl_j hij]; exact e3
  · rw [planeTorusDiag_inr_i, planeTorusDiag_inr_j hij]; exact e4

theorem commute_longInv_iff (k : Fin n) (g : StatedSp n K) :
    Commute g (longInv K n k) ↔ ∀ r t, mat n K g r t * (if t ∈ coords k then (-1 : K) else 1) =
      (if r ∈ coords k then (-1 : K) else 1) * mat n K g r t := by
  constructor
  · intro h r t
    have := congrFun (congrFun (congrArg (mat n K) h.eq) r) t
    rwa [map_mul, map_mul, mat_longInv, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  · intro h
    show g * longInv K n k = longInv K n k * g
    refine mat_injective ?_
    rw [map_mul, map_mul, mat_longInv]
    ext r t
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    exact h r t

theorem planeTorusCent_le_centralizer_longInv (hij : i ≠ j) {a b : Kˣ} (hab : a ≠ b)
    (hab' : a ≠ b⁻¹) :
    suppGroup (coords i ∪ coords j) ⊓ Subgroup.centralizer {planeTorusElt K i j a b} ≤
      Subgroup.centralizer {longInv K n i} := by
  intro g hg'
  obtain ⟨hg, hc⟩ := Subgroup.mem_inf.1 hg'
  rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
  have hcg : Commute g (planeTorusElt K i j a b) := hc
  have hd := (commute_planeTorusElt_iff hij a b g).1 hcg
  refine ((commute_longInv_iff i g).2 fun r t => ?_).eq
  by_cases hr : r ∈ coords i <;> by_cases ht : t ∈ coords i
  · simp [hr, ht, mul_comm]
  · have h0 : mat n K g r t = 0 := by
      by_cases hj : t ∈ coords j
      · have := hd r t
        have hne := planeTorusDiag_ne_of_cross hij hab hab' hr hj
        have h' : mat n K g r t * (planeTorusDiag i j a b t - planeTorusDiag i j a b r) = 0 := by
          linear_combination this
        exact (mul_eq_zero.1 h').resolve_right (sub_ne_zero.2 (Ne.symm hne))
      · rw [hg r t (fun h' => by
          rcases h'.2 with h2 | h2
          · exact ht h2
          · exact hj h2)]
        exact Matrix.one_apply_ne (fun e => ht (e ▸ hr))
    simp [hr, ht, h0]
  · have h0 : mat n K g r t = 0 := by
      by_cases hj : r ∈ coords j
      · have := hd r t
        have hne := planeTorusDiag_ne_of_cross hij hab hab' ht hj
        have h' : mat n K g r t * (planeTorusDiag i j a b t - planeTorusDiag i j a b r) = 0 := by
          linear_combination this
        exact (mul_eq_zero.1 h').resolve_right (sub_ne_zero.2 hne)
      · rw [hg r t (fun h' => by
          rcases h'.1 with h2 | h2
          · exact hr h2
          · exact hj h2)]
        exact Matrix.one_apply_ne (fun e => hr (e ▸ ht))
    simp [hr, ht, h0]
  · simp [hr, ht, mul_comm]

theorem planeTorusDiag_eq_of_sq (a : Kˣ) (ha : (a : K) = ((a⁻¹ : Kˣ) : K)) {r : Fin n ⊕ Fin n}
    (hr : r ∈ coords i ∪ coords j) : planeTorusDiag i j a a r = (a : K) := by
  rcases r with k | k
  · rw [planeTorusDiag_inl_same, ite_eq_left (inl_mem_union_iff.1 hr)]
  · rw [planeTorusDiag_inr_same, ite_eq_left (inr_mem_union_iff.1 hr), ← ha]

theorem suppGroup_le_centralizer_planeTorusElt (hij : i ≠ j) (a : Kˣ)
    (ha : (a : K) = ((a⁻¹ : Kˣ) : K)) :
    suppGroup (coords i ∪ coords j) ≤ Subgroup.centralizer {planeTorusElt K i j a a} := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  refine ((commute_planeTorusElt_iff hij a a g).2 fun r t => ?_).eq
  by_cases h : r ∈ coords i ∪ coords j ∧ t ∈ coords i ∪ coords j
  · rw [planeTorusDiag_eq_of_sq a ha h.1, planeTorusDiag_eq_of_sq a ha h.2, mul_comm]
  · rw [hg r t h, Matrix.one_apply]
    by_cases hrt : r = t
    · subst hrt; simp [mul_comm]
    · simp [hrt]

end General

section Neg

variable (K) in
@[expose] def weylMat : SL(2, K) := mkSL !![0, 1; -1, 0] (by simp [Matrix.det_fin_two])

theorem weylMat_mul_torusHom (a : Kˣ) : weylMat K * torusHom K a = torusHom K a⁻¹ * weylMat K := by
  refine Subtype.ext ?_
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [weylMat, coe_torusHom, Matrix.mul_apply, Fin.sum_univ_two]

variable (K n) in
@[expose] noncomputable def planeWeyl (k : Fin n) : StatedSp n K := longBlock K n k (weylMat K)

theorem commute_longBlock_longBlock (hij : i ≠ j) (A B : SL(2, K)) :
    Commute (longBlock K n i A) (longBlock K n j B) :=
  commute_longRootSp2 hij ⟨A, rfl⟩ ⟨B, rfl⟩

theorem planeWeyl_mul_planeTorusElt (hij : i ≠ j) (a b : Kˣ) :
    planeWeyl K n j * planeTorusElt K i j a b = planeTorusElt K i j a b⁻¹ * planeWeyl K n j := by
  simp only [planeWeyl, planeTorusElt]
  calc longBlock K n j (weylMat K) *
        (longBlock K n i (torusHom K a) * longBlock K n j (torusHom K b))
      = (longBlock K n j (weylMat K) * longBlock K n i (torusHom K a)) *
          longBlock K n j (torusHom K b) := by rw [mul_assoc]
    _ = (longBlock K n i (torusHom K a) * longBlock K n j (weylMat K)) *
          longBlock K n j (torusHom K b) := by
        rw [(commute_longBlock_longBlock hij (torusHom K a) (weylMat K)).eq.symm]
    _ = longBlock K n i (torusHom K a) * longBlock K n j (weylMat K * torusHom K b) := by
        rw [mul_assoc, map_mul]
    _ = longBlock K n i (torusHom K a) * longBlock K n j (torusHom K b⁻¹ * weylMat K) := by
        rw [weylMat_mul_torusHom]
    _ = longBlock K n i (torusHom K a) * longBlock K n j (torusHom K b⁻¹) *
          longBlock K n j (weylMat K) := by rw [map_mul, mul_assoc]

theorem map_conj_inf_centralizer {G : Type*} [Group G] (M : Subgroup G) {w : G} (hw : w ∈ M)
    (d : G) : (M ⊓ Subgroup.centralizer {d}).map (MulAut.conj w).toMonoidHom =
      M ⊓ Subgroup.centralizer {w * d * w⁻¹} := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, ⟨hy, hyc⟩, rfl⟩
    refine ⟨mul_mem (mul_mem hw hy) (inv_mem hw), ?_⟩
    calc w * y * w⁻¹ * (w * d * w⁻¹) = w * (y * d) * w⁻¹ := by group
      _ = w * (d * y) * w⁻¹ := by rw [hyc]
      _ = w * d * w⁻¹ * (w * y * w⁻¹) := by group
  · rintro ⟨hx, hxc⟩
    refine ⟨w⁻¹ * x * w, ⟨mul_mem (mul_mem (inv_mem hw) hx) hw, ?_⟩, by group⟩
    have h1 : d * (w⁻¹ * x * w) = w⁻¹ * (w * d * w⁻¹ * x) * w := by group
    have h2 : (w⁻¹ * x * w) * d = w⁻¹ * (x * (w * d * w⁻¹)) * w := by group
    rw [h2, h1, hxc]

theorem planeWeyl_mem : planeWeyl K n j ∈ suppGroup (coords i ∪ coords j) :=
  suppGroup_mono Set.subset_union_right (isSupp_longBlock j _)

theorem conj_planeWeyl_planeTorusElt (hij : i ≠ j) (a b : Kˣ) :
    planeWeyl K n j * planeTorusElt K i j a b * (planeWeyl K n j)⁻¹ =
      planeTorusElt K i j a b⁻¹ := by
  rw [planeWeyl_mul_planeTorusElt hij, mul_assoc, mul_inv_cancel, mul_one]

variable (K) in
@[expose] noncomputable def shortGroupNeg (hij : i ≠ j) : Subgroup (StatedSp n K) :=
  (shortBlock K hij).range.map (MulAut.conj (planeWeyl K n j)).toMonoidHom

theorem commutator_planeTorusCent_neg (hij : i ≠ j) {a : Kˣ} (ha : (a : K) ≠ ((a⁻¹ : Kˣ) : K)) :
    ⁅suppGroup (coords i ∪ coords j) ⊓ Subgroup.centralizer {planeTorusElt K i j a a⁻¹},
      suppGroup (coords i ∪ coords j) ⊓ Subgroup.centralizer {planeTorusElt K i j a a⁻¹}⁆ =
      shortGroupNeg K hij := by
  rw [← conj_planeWeyl_planeTorusElt hij a a, ← map_conj_inf_centralizer _ (planeWeyl_mem),
    ← Subgroup.map_commutator]
  exact congrArg _ (commutator_leviCent hij ha)

end Neg

section Characterization

variable (K) in
@[expose] def transvOne : SL(2, K) := mkSL !![1, 1; 0, 1] (by simp [Matrix.det_fin_two])

theorem not_commute_longBlock_planeTorusElt (hij : i ≠ j) {a : Kˣ} (ha : (a : K) ≠ ((a⁻¹ : Kˣ) : K))
    (b : Kˣ) : ¬ Commute (longBlock K n i (transvOne K)) (planeTorusElt K i j a b) := by
  intro h
  have := (commute_planeTorusElt_iff hij a b _).1 h (Sum.inl i) (Sum.inr i)
  rw [planeTorusDiag_inr_i, planeTorusDiag_inl_i, mat_longBlock] at this
  simp [blockMat, transvOne] at this
  rw [Units.val_inv_eq_inv_val] at ha
  exact ha this.symm

theorem not_commute_shortBlock_longInv (hij : i ≠ j) (h2 : (2 : K) ≠ 0) :
    ¬ Commute (shortBlock K hij (transvOne K)) (longInv K n i) := by
  intro h
  have := (commute_longInv_iff i _).1 h (Sum.inl i) (Sum.inl j)
  rw [mat_shortBlock, Matrix.fromBlocks_apply₁₁] at this
  have hji : j ≠ i := hij.symm
  simp [blockMat, transvOne, coords, hji] at this
  exact h2 (by linear_combination this)

theorem commute_planeWeyl_longInv (hij : i ≠ j) : Commute (planeWeyl K n j) (longInv K n i) :=
  commute_longBlock_longBlock hij.symm _ _

@[expose] def IsAdaptedShortIn {Γ : Type*} [Group Γ] (M TA TB : Subgroup Γ) (zA : Γ)
    (S : Subgroup Γ) :
    Prop :=
  ∃ x ∈ TA, ∃ y ∈ TB, ¬ M ≤ Subgroup.centralizer {x * y} ∧
    ¬ (M ⊓ Subgroup.centralizer {x * y} ≤ Subgroup.centralizer {zA}) ∧
    S = ⁅M ⊓ Subgroup.centralizer {x * y}, M ⊓ Subgroup.centralizer {x * y}⁆

variable (K n) in
@[expose] noncomputable def planeTorus (k : Fin n) : Subgroup (StatedSp n K) :=
  (diagTorus2 K).map (longBlock K n k)

theorem isAdaptedShortIn_iff (hij : i ≠ j) (h2 : (2 : K) ≠ 0)
    (hex : ∃ a : Kˣ, (a : K) ≠ ((a⁻¹ : Kˣ) : K)) (S : Subgroup (StatedSp n K)) :
    IsAdaptedShortIn (suppGroup (coords i ∪ coords j)) (planeTorus K n i) (planeTorus K n j)
        (longInv K n i) S ↔ S = (shortBlock K hij).range ∨ S = shortGroupNeg K hij := by
  constructor
  · rintro ⟨x, hx, y, hy, hnc, hnz, rfl⟩
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨a, rfl⟩ := mem_diagTorus2_iff.1 hu
    obtain ⟨b, rfl⟩ := mem_diagTorus2_iff.1 hv
    change ¬ _ ≤ Subgroup.centralizer {planeTorusElt K i j a b} at hnc
    change ¬ _ ≤ Subgroup.centralizer {longInv K n i} at hnz
    by_cases hab : a = b ∨ a = b⁻¹
    · rcases hab with h | h
      · subst h
        by_cases ha : (a : K) = ((a⁻¹ : Kˣ) : K)
        · exact absurd (suppGroup_le_centralizer_planeTorusElt hij a ha) hnc
        · exact Or.inl (commutator_leviCent hij ha)
      · have hb : b = a⁻¹ := by rw [h, inv_inv]
        subst hb
        by_cases ha : (a : K) = ((a⁻¹ : Kˣ) : K)
        · have : a⁻¹ = a := (Units.ext ha).symm
          rw [this] at hnc
          exact absurd (suppGroup_le_centralizer_planeTorusElt hij a ha) hnc
        · exact Or.inr (commutator_planeTorusCent_neg hij ha)
    · rw [not_or] at hab
      exact absurd (planeTorusCent_le_centralizer_longInv hij hab.1 hab.2) hnz
  · obtain ⟨a, ha⟩ := hex
    have hg₁ : longBlock K n i (transvOne K) ∈ suppGroup (coords i ∪ coords j) :=
      suppGroup_mono Set.subset_union_left (isSupp_longBlock i _)
    rintro (rfl | rfl)
    · refine ⟨longBlock K n i (torusHom K a), Subgroup.mem_map.2 ⟨_, ⟨a, rfl⟩, rfl⟩,
        longBlock K n j (torusHom K a), Subgroup.mem_map.2 ⟨_, ⟨a, rfl⟩, rfl⟩, ?_, ?_, ?_⟩
      · intro h
        exact not_commute_longBlock_planeTorusElt hij ha a
          (Subgroup.mem_centralizer_singleton_iff.1 (h hg₁))
      · intro h
        have hs : shortBlock K hij (transvOne K) ∈ leviCent K i j a :=
          shortBlock_mem_leviCent hij a _
        exact not_commute_shortBlock_longInv hij h2
          (Subgroup.mem_centralizer_singleton_iff.1 (h hs))
      · exact (commutator_leviCent hij ha).symm
    · refine ⟨longBlock K n i (torusHom K a), Subgroup.mem_map.2 ⟨_, ⟨a, rfl⟩, rfl⟩,
        longBlock K n j (torusHom K a⁻¹), Subgroup.mem_map.2 ⟨_, ⟨a⁻¹, rfl⟩, rfl⟩, ?_, ?_, ?_⟩
      · intro h
        exact not_commute_longBlock_planeTorusElt hij ha a⁻¹
          (Subgroup.mem_centralizer_singleton_iff.1 (h hg₁))
      · intro h
        have hs : shortBlock K hij (transvOne K) ∈ leviCent K i j a :=
          shortBlock_mem_leviCent hij a _
        have hs' : planeWeyl K n j * shortBlock K hij (transvOne K) * (planeWeyl K n j)⁻¹ ∈
            suppGroup (coords i ∪ coords j) ⊓ Subgroup.centralizer {planeTorusElt K i j a a⁻¹} := by
          rw [← conj_planeWeyl_planeTorusElt hij a a, ← map_conj_inf_centralizer _ (planeWeyl_mem)]
          exact ⟨_, hs, rfl⟩
        have hc : Commute (planeWeyl K n j * shortBlock K hij (transvOne K) * (planeWeyl K n j)⁻¹)
            (longInv K n i) := Subgroup.mem_centralizer_singleton_iff.1 (h hs')
        have hw := commute_planeWeyl_longInv (K := K) (n := n) hij
        have : Commute (shortBlock K hij (transvOne K)) (longInv K n i) := by
          have e : shortBlock K hij (transvOne K) = (planeWeyl K n j)⁻¹ *
              (planeWeyl K n j * shortBlock K hij (transvOne K) * (planeWeyl K n j)⁻¹) *
                planeWeyl K n j := by
            group
          rw [e]
          exact ((hw.inv_left).mul_left hc).mul_left hw
        exact not_commute_shortBlock_longInv hij h2 this
      · exact (commutator_planeTorusCent_neg hij ha).symm

end Characterization

end CFSG.ClassicalInvolution.Models.SymplecticPairs
