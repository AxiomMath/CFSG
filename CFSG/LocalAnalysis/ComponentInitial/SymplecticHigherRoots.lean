module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylQuotient
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagTriangular

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Matrix SymplecticFlag CFSG.Assembly.LowTwoRank SymplecticTorusWeyl

variable {r : ℕ} {K : Type} [Field K]

variable (K) in
@[expose] def lineSign (x : Fin r ⊕ Fin r) : K :=
  Sum.elim (fun _ => 1) (fun _ => -1) x

theorem lineSign_swap (x : Fin r ⊕ Fin r) : lineSign K x.swap = -lineSign K x := by
  rcases x with x | x <;> simp [lineSign]

theorem lineSign_mul_self (x : Fin r ⊕ Fin r) : lineSign K x * lineSign K x = 1 := by
  rcases x with x | x <;> simp [lineSign]

theorem lineSign_ne_zero (x : Fin r ⊕ Fin r) : lineSign K x ≠ 0 := fun h => by
  have := lineSign_mul_self (K := K) x
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem J_apply (y z : Fin r ⊕ Fin r) :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) y z =
      if z = y.swap then lineSign K y else 0 := by
  rcases y with y | y <;> rcases z with z | z <;> by_cases h : y = z <;>
    simp [lineSign, one_apply, h, eq_comm]

theorem swap_injective' : Function.Injective (Sum.swap : Fin r ⊕ Fin r → Fin r ⊕ Fin r) :=
  Sum.swap_leftInverse.injective

theorem J_mul_single (a b : Fin r ⊕ Fin r) (c : K) :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * single a b c =
      single a.swap b (lineSign K a.swap * c) := by
  ext y z
  rw [mul_apply, Finset.sum_eq_single a]
  · rw [J_apply, single_apply, single_apply]
    by_cases hy : y = a.swap
    · subst hy
      simp
    · have h1 : ¬a = y.swap := fun h => hy (by rw [h, Sum.swap_swap])
      have h2 : ¬a.swap = y := fun h => hy h.symm
      simp [h1, h2]
  · intro w _ hw
    rw [single_apply, ite_eq_right (fun h => hw h.1.symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem single_mul_J (a b : Fin r ⊕ Fin r) (c : K) :
    single a b c * (fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      single a b.swap (lineSign K b * c) := by
  ext y z
  rw [mul_apply, Finset.sum_eq_single b]
  · rw [J_apply, single_apply, single_apply]
    by_cases hy : a = y
    · by_cases hz : z = b.swap
      · simp [hy, hz, mul_comm]
      · simp [hy, hz, Ne.symm hz]
    · simp [hy]
  · intro w _ hw
    rw [single_apply, ite_eq_right (fun h => hw h.2.symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ b) h

variable (K) in
@[expose] def rootNil (a b : Fin r ⊕ Fin r) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  if b = a.swap then single a b 1
  else single a b 1 + single b.swap a.swap (-(lineSign K a * lineSign K b))

variable (K) in
@[expose] def pairRootMat (a b : Fin r ⊕ Fin r) (t : K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  1 + t • rootNil K a b

theorem swap_ne_self (x : Fin r ⊕ Fin r) : x.swap ≠ x := by
  rcases x with x | x <;> simp

theorem rootNil_mul_self {a b : Fin r ⊕ Fin r} (hab : a ≠ b) :
    rootNil K a b * rootNil K a b = 0 := by
  have hab' : a.swap ≠ b.swap := fun h => hab (swap_injective' h)
  unfold rootNil
  split_ifs with h
  · rw [single_mul_single_of_ne _ _ _ _ (Ne.symm hab)]
  · simp only [Matrix.add_mul, Matrix.mul_add,
      single_mul_single_of_ne _ _ _ _ (Ne.symm hab),
      single_mul_single_of_ne _ _ _ _ (swap_ne_self b).symm,
      single_mul_single_of_ne _ _ _ _ (swap_ne_self a),
      single_mul_single_of_ne _ _ _ _ hab', add_zero]

theorem rootNil_transpose_J_add {a b : Fin r ⊕ Fin r} :
    (rootNil K a b)ᵀ * fromBlocks 0 1 (-1) 0 + fromBlocks 0 1 (-1) 0 * rootNil K a b = 0 := by
  unfold rootNil
  split_ifs with h
  · rw [transpose_single, single_mul_J, J_mul_single, h, ← single_add, lineSign_swap]
    simp
  · rw [transpose_add, transpose_single, transpose_single, Matrix.add_mul, Matrix.mul_add,
      single_mul_J, single_mul_J, J_mul_single, J_mul_single, Sum.swap_swap, lineSign_swap,
      lineSign_swap]
    have h1 : single b a.swap (lineSign K a * 1) +
        single b a.swap (lineSign K b * -(lineSign K a * lineSign K b)) = 0 := by
      rw [← single_add, mul_one, mul_neg, ← mul_assoc, mul_comm (lineSign K b) (lineSign K a),
        mul_assoc, lineSign_mul_self, mul_one, add_neg_cancel, single_zero]
    have h2 : single a.swap b (-lineSign K b * -(lineSign K a * lineSign K b)) +
        single a.swap b (-lineSign K a * 1) = 0 := by
      rw [← single_add, neg_mul_neg, mul_one, mul_comm (lineSign K a), ← mul_assoc,
        lineSign_mul_self, one_mul, add_neg_cancel, single_zero]
    calc single b a.swap (lineSign K a * 1) +
          single a.swap b (-lineSign K b * -(lineSign K a * lineSign K b)) +
          (single a.swap b (-lineSign K a * 1) +
            single b a.swap (lineSign K b * -(lineSign K a * lineSign K b))) =
          (single b a.swap (lineSign K a * 1) +
            single b a.swap (lineSign K b * -(lineSign K a * lineSign K b))) +
          (single a.swap b (-lineSign K b * -(lineSign K a * lineSign K b)) +
            single a.swap b (-lineSign K a * 1)) := by abel
      _ = 0 := by rw [h1, h2, add_zero]

theorem rootNil_transpose_J_mul {a b : Fin r ⊕ Fin r} (hab : a ≠ b) :
    (rootNil K a b)ᵀ * fromBlocks 0 1 (-1) 0 * rootNil K a b = 0 := by
  have hab' : a.swap ≠ b.swap := fun h => hab (swap_injective' h)
  unfold rootNil
  split_ifs with h
  · rw [transpose_single, single_mul_J, single_mul_single_of_ne _ _ _ _ (swap_ne_self a)]
  · simp only [transpose_add, transpose_single, Matrix.add_mul, Matrix.mul_add, single_mul_J,
      Sum.swap_swap, single_mul_single_of_ne _ _ _ _ (swap_ne_self a),
      single_mul_single_of_ne _ _ _ _ hab', single_mul_single_of_ne _ _ _ _ (Ne.symm hab),
      single_mul_single_of_ne _ _ _ _ (swap_ne_self b).symm, add_zero]

theorem pairRootMat_mul {a b : Fin r ⊕ Fin r} (hab : a ≠ b) (s t : K) :
    pairRootMat K a b s * pairRootMat K a b t = pairRootMat K a b (s + t) := by
  rw [pairRootMat, pairRootMat, pairRootMat, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add,
    Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, rootNil_mul_self hab, smul_zero,
    smul_zero, add_zero, add_smul]
  abel

theorem pairRootMat_zero (a b : Fin r ⊕ Fin r) : pairRootMat K a b 0 = 1 := by
  rw [pairRootMat, zero_smul, add_zero]

theorem pairRootMat_symplectic {a b : Fin r ⊕ Fin r} (hab : a ≠ b) (t : K) :
    (pairRootMat K a b t)ᵀ * fromBlocks 0 1 (-1) 0 * pairRootMat K a b t =
      fromBlocks 0 1 (-1) 0 := by
  have h1 := rootNil_transpose_J_add (K := K) (a := a) (b := b)
  have h2 := rootNil_transpose_J_mul (K := K) hab
  set N := rootNil K a b
  set J : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := fromBlocks 0 1 (-1) 0
  have hT : (pairRootMat K a b t)ᵀ = 1 + t • Nᵀ := by
    rw [pairRootMat, transpose_add, transpose_one, transpose_smul]
  have hexp : (1 + t • Nᵀ) * J * (1 + t • N) =
      J + t • (Nᵀ * J + J * N) + (t * t) • (Nᵀ * J * N) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_add, smul_smul, Matrix.mul_assoc]
    abel
  rw [hT, pairRootMat, hexp, h1, h2, smul_zero, smul_zero, add_zero, add_zero]

@[expose] def pairRootElt {a b : Fin r ⊕ Fin r} (hab : a ≠ b) (t : K) : StatedSp r K :=
  ⟨⟨pairRootMat K a b t, pairRootMat K a b (-t),
    by rw [pairRootMat_mul hab, add_neg_cancel, pairRootMat_zero],
    by rw [pairRootMat_mul hab, neg_add_cancel, pairRootMat_zero]⟩,
    SymplecticTorusWeyl.mem_statedSp_iff.mpr (pairRootMat_symplectic hab t)⟩

theorem coe_pairRootElt {a b : Fin r ⊕ Fin r} (hab : a ≠ b) (t : K) :
    (((pairRootElt hab t : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = pairRootMat K a b t :=
  rfl

variable (K) in
@[expose] def pairRootHom {a b : Fin r ⊕ Fin r} (hab : a ≠ b) : Multiplicative K →* StatedSp r K
    where
  toFun t := pairRootElt hab t.toAdd
  map_one' := statedSp_ext (by rw [coe_pairRootElt, toAdd_one, pairRootMat_zero]; rfl)
  map_mul' s t := statedSp_ext (by
    rw [Subgroup.coe_mul, Units.val_mul, coe_pairRootElt, coe_pairRootElt, coe_pairRootElt,
      toAdd_mul, pairRootMat_mul hab])

theorem pairRootHom_apply {a b : Fin r ⊕ Fin r} (hab : a ≠ b) (t : K) :
    pairRootHom K hab (Multiplicative.ofAdd t) = pairRootElt hab t :=
  rfl

theorem pairRootMat_apply_self {a b : Fin r ⊕ Fin r} (hab : a ≠ b) (t : K) :
    pairRootMat K a b t a b = t := by
  rw [pairRootMat, Matrix.add_apply, one_apply_ne hab, zero_add, Matrix.smul_apply, rootNil]
  split_ifs with h
  · simp
  · have h' : ¬(b.swap = a ∧ a.swap = b) := fun hh => h (by rw [← hh.1, Sum.swap_swap])
    simp [h']

theorem pairRootHom_injective {a b : Fin r ⊕ Fin r} (hab : a ≠ b) :
    Function.Injective (pairRootHom K hab) := by
  intro s t h
  have := congrArg (fun g : StatedSp r K => ((g : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) a b) h
  simp only [pairRootHom, MonoidHom.coe_mk, OneHom.coe_mk, coe_pairRootElt,
    pairRootMat_apply_self hab] at this
  exact Multiplicative.toAdd.injective this

theorem pairRootMat_partner {a b : Fin r ⊕ Fin r} (t : K) :
    pairRootMat K b.swap a.swap t =
      pairRootMat K a b (-(lineSign K a * lineSign K b) * t) := by
  by_cases h : b = a.swap
  · subst h
    rw [Sum.swap_swap, lineSign_swap, mul_neg, neg_neg, lineSign_mul_self, one_mul]
  · set s := -(lineSign K a * lineSign K b) with hs
    have hss : s * s = 1 := by
      rw [hs, neg_mul_neg, mul_mul_mul_comm, lineSign_mul_self, lineSign_mul_self, one_mul]
    have h' : ¬a.swap = b.swap.swap := fun h'' => h (by rw [Sum.swap_swap] at h''; rw [← h''])
    have hN' : rootNil K b.swap a.swap = single b.swap a.swap 1 + single a b s := by
      rw [rootNil, ite_eq_right h', Sum.swap_swap, Sum.swap_swap, lineSign_swap, lineSign_swap,
        neg_mul_neg, mul_comm (lineSign K b)]
    have hN : rootNil K a b = single a b 1 + single b.swap a.swap s := by
      rw [rootNil, ite_eq_right h]
    have hsts : s * t * s = t := by rw [mul_comm s t, mul_assoc, hss, mul_one]
    rw [pairRootMat, pairRootMat, hN', hN, smul_add, smul_add, smul_single, smul_single,
      smul_single, smul_single, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_one,
      mul_one, hsts, mul_comm t s, add_comm (single b.swap a.swap t)]

theorem pairRootMat_inl_inl {i j : Fin r} (t : K) :
    pairRootMat K (Sum.inl i) (Sum.inl j) t =
      1 + t • single (Sum.inl i) (Sum.inl j) 1 - t • single (Sum.inr j) (Sum.inr i) 1 := by
  rw [pairRootMat, rootNil, ite_eq_right (by simp)]
  simp [lineSign, smul_add, sub_eq_add_neg, add_assoc, smul_single, single_neg]

theorem pairRootMat_inl_inr {i j : Fin r} (hij : i ≠ j) (t : K) :
    pairRootMat K (Sum.inl i) (Sum.inr j) t =
      1 + t • (single (Sum.inl i) (Sum.inr j) 1 + single (Sum.inl j) (Sum.inr i) 1) := by
  rw [pairRootMat, rootNil, ite_eq_right (by simpa using hij.symm)]
  simp [lineSign]

theorem pairRootMat_inr_inl {i j : Fin r} (hij : i ≠ j) (t : K) :
    pairRootMat K (Sum.inr i) (Sum.inl j) t =
      1 + t • (single (Sum.inr i) (Sum.inl j) 1 + single (Sum.inr j) (Sum.inl i) 1) := by
  rw [pairRootMat, rootNil, ite_eq_right (by simpa using hij.symm)]
  simp [lineSign]

theorem pairRootMat_inl_inr_self (i : Fin r) (t : K) :
    pairRootMat K (Sum.inl i) (Sum.inr i) t = 1 + t • single (Sum.inl i) (Sum.inr i) 1 := by
  rw [pairRootMat, rootNil, ite_eq_left (show Sum.inr i = (Sum.inl i).swap from rfl)]

theorem pairRootMat_inr_inl_self (i : Fin r) (t : K) :
    pairRootMat K (Sum.inr i) (Sum.inl i) t = 1 + t • single (Sum.inr i) (Sum.inl i) 1 := by
  rw [pairRootMat, rootNil, ite_eq_left (show Sum.inl i = (Sum.inr i).swap from rfl)]

variable (r) in
@[expose] def lineVec : Fin r ⊕ Fin r → Fin r → ℤ :=
  Sum.elim (fun i => Pi.single i 1) (fun i => -Pi.single i 1)

@[expose] def rootVec (a b : Fin r ⊕ Fin r) : Fin r → ℤ :=
  lineVec r a - lineVec r b

theorem lineVec_swap (x : Fin r ⊕ Fin r) : lineVec r x.swap = -lineVec r x := by
  rcases x with x | x <;> simp [lineVec]

theorem lineVal_lineVec (x y : Fin r ⊕ Fin r) :
    lineVal (lineVec r x) y = (if y = x then 1 else 0) - (if y = x.swap then 1 else 0) := by
  rcases x with x | x <;> rcases y with y | y <;>
    simp [lineVal, lineVec, Pi.single_apply, eq_comm]

theorem lineVec_injective : Function.Injective (lineVec r) := by
  intro x y h
  have h1 := lineVal_lineVec (r := r) x x
  rw [h, lineVal_lineVec, ite_eq_left rfl, ite_eq_right (swap_ne_self x).symm] at h1
  by_contra hxy
  rw [ite_eq_right hxy] at h1
  split_ifs at h1 <;> omega

theorem rootVec_partner (a b : Fin r ⊕ Fin r) : rootVec b.swap a.swap = rootVec a b := by
  rw [rootVec, rootVec, lineVec_swap, lineVec_swap]
  abel

theorem neg_rootVec (a b : Fin r ⊕ Fin r) : -rootVec a b = rootVec b a := by
  rw [rootVec, rootVec, neg_sub]

theorem lineVal_add (e e' : Fin r → ℤ) (x : Fin r ⊕ Fin r) :
    lineVal (e + e') x = lineVal e x + lineVal e' x := by
  rcases x with x | x <;> simp [lineVal, add_comm]

theorem lineVal_sub (e e' : Fin r → ℤ) (x : Fin r ⊕ Fin r) :
    lineVal (e - e') x = lineVal e x - lineVal e' x := by
  rcases x with x | x <;> simp [lineVal]
  abel

theorem rootVec_eq_rootVec_iff {a b c d : Fin r ⊕ Fin r} (hab : a ≠ b) (hcd : c ≠ d) :
    rootVec a b = rootVec c d ↔ (c = a ∧ d = b) ∨ (c = b.swap ∧ d = a.swap) := by
  constructor
  · intro h
    have hval := congrArg (fun e => lineVal e a) h
    simp only [rootVec, lineVal_sub, lineVal_lineVec] at hval
    have haa : a ≠ a.swap := (swap_ne_self a).symm
    by_cases hac : a = c
    · subst hac
      have hbd : lineVec r b = lineVec r d := by
        have := h
        simp only [rootVec] at this
        exact sub_right_injective this
      exact Or.inl ⟨rfl, (lineVec_injective hbd).symm⟩
    by_cases had : a = d.swap
    ·
      have hc : lineVec r c = lineVec r b.swap := by
        have h' := h
        simp only [rootVec] at h'
        rw [had, lineVec_swap] at h'
        rw [lineVec_swap]
        have : lineVec r c = -lineVec r d - lineVec r b + lineVec r d := by
          rw [h']; abel
        rw [this]
        abel
      refine Or.inr ⟨lineVec_injective hc, ?_⟩
      rw [had, Sum.swap_swap]
    · exfalso
      have h1 : (if a = a.swap then (1 : ℤ) else 0) = 0 := ite_eq_right haa
      have h2 : (if a = b then (1 : ℤ) else 0) = 0 := ite_eq_right hab
      have h3 : (if a = c then (1 : ℤ) else 0) = 0 := ite_eq_right hac
      have h4 : (if a = d.swap then (1 : ℤ) else 0) = 0 := ite_eq_right had
      simp only [↓reduceIte, h1, h2, h3, h4] at hval
      split_ifs at hval <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact (rootVec_partner a b).symm

variable (r) in
@[expose] def posRoots : Finset (Fin r → ℤ) :=
  ((Finset.univ.filter fun p : Fin r × Fin r => p.1 < p.2).image
      fun p => Pi.single p.1 1 - Pi.single p.2 1) ∪
    ((Finset.univ.filter fun p : Fin r × Fin r => p.1 < p.2).image
      fun p => Pi.single p.1 1 + Pi.single p.2 1) ∪
    Finset.univ.image fun i : Fin r => 2 • Pi.single i 1

variable (r) in
@[expose] def negRoots : Finset (Fin r → ℤ) :=
  (posRoots r).image Neg.neg

theorem mem_posRoots {α : Fin r → ℤ} :
    α ∈ posRoots r ↔ (∃ i j : Fin r, i < j ∧ α = Pi.single i 1 - Pi.single j 1) ∨
      (∃ i j : Fin r, i < j ∧ α = Pi.single i 1 + Pi.single j 1) ∨
      ∃ i : Fin r, α = 2 • Pi.single i 1 := by
  simp only [posRoots, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, Prod.exists]
  constructor
  · rintro ((⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩) | ⟨i, rfl⟩)
    · exact Or.inl ⟨i, j, hij, rfl⟩
    · exact Or.inr (Or.inl ⟨i, j, hij, rfl⟩)
    · exact Or.inr (Or.inr ⟨i, rfl⟩)
  · rintro (⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩ | ⟨i, rfl⟩)
    · exact Or.inl (Or.inl ⟨i, j, hij, rfl⟩)
    · exact Or.inl (Or.inr ⟨i, j, hij, rfl⟩)
    · exact Or.inr ⟨i, rfl⟩

theorem mem_negRoots {α : Fin r → ℤ} : α ∈ negRoots r ↔ -α ∈ posRoots r := by
  rw [negRoots, Finset.mem_image]
  constructor
  · rintro ⟨β, hβ, rfl⟩
    rwa [neg_neg]
  · intro h
    exact ⟨-α, h, neg_neg α⟩

@[expose] def height (v : Fin r → ℤ) : ℤ :=
  ∑ i, ((r : ℤ) - i) * v i

theorem height_sub (v w : Fin r → ℤ) : height (v - w) = height v - height w := by
  simp only [height, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem height_neg (v : Fin r → ℤ) : height (-v) = -height v := by
  simp only [height, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem height_single (i : Fin r) : height (Pi.single i (1 : ℤ)) = r - i := by
  rw [height, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_apply, ite_eq_right hj, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem height_lineVec_inl (i : Fin r) : height (lineVec r (Sum.inl i)) = r - i :=
  height_single i

theorem height_lineVec_inr (i : Fin r) : height (lineVec r (Sum.inr i)) = -(r - i) := by
  change height (-Pi.single i 1) = _
  rw [height_neg, height_single]

theorem height_lineVec_lt {x y : Fin r ⊕ Fin r} (h : (flagOrder r x : ℕ) < flagOrder r y) :
    height (lineVec r y) < height (lineVec r x) := by
  rcases x with x | x <;> rcases y with y | y <;>
    simp only [height_lineVec_inl, height_lineVec_inr, flagOrder_inl, flagOrder_inr] at h ⊢ <;>
    have := x.2 <;> have := y.2 <;> omega

theorem height_rootVec_pos {a b : Fin r ⊕ Fin r} (h : (flagOrder r a : ℕ) < flagOrder r b) :
    0 < height (rootVec a b) := by
  rw [rootVec, height_sub]
  have := height_lineVec_lt h
  omega

theorem height_pos_of_mem_posRoots {α : Fin r → ℤ} (h : α ∈ posRoots r) : 0 < height α := by
  rcases mem_posRoots.mp h with ⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩ | ⟨i, rfl⟩
  · rw [height_sub, height_single, height_single]
    have : (i : ℕ) < j := hij
    omega
  · have : height (Pi.single i (1 : ℤ) + Pi.single j 1) =
        height (Pi.single i 1) + height (Pi.single j 1) := by
      simp only [height, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [this, height_single, height_single]
    have := i.2
    have := j.2
    omega
  · have : height (2 • Pi.single i (1 : ℤ)) = 2 * height (Pi.single i 1) := by
      simp only [height, Pi.smul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, height_single]
    have := i.2
    omega

theorem height_neg_of_mem_negRoots {α : Fin r → ℤ} (h : α ∈ negRoots r) : height α < 0 := by
  have := height_pos_of_mem_posRoots (mem_negRoots.mp h)
  rw [height_neg] at this
  omega

theorem not_mem_negRoots_of_mem_posRoots {α : Fin r → ℤ} (h : α ∈ posRoots r) :
    α ∉ negRoots r := fun h' =>
  absurd (height_pos_of_mem_posRoots h) (not_lt.mpr (height_neg_of_mem_negRoots h').le)

theorem rootVec_mem_posRoots {a b : Fin r ⊕ Fin r} (h : (flagOrder r a : ℕ) < flagOrder r b) :
    rootVec a b ∈ posRoots r := by
  rw [mem_posRoots]
  rcases a with i | i <;> rcases b with j | j <;>
    simp only [flagOrder_inl, flagOrder_inr] at h
  · exact Or.inl ⟨i, j, h, rfl⟩
  · rcases lt_trichotomy i j with hij | rfl | hij
    · exact Or.inr (Or.inl ⟨i, j, hij, by simp [rootVec, lineVec, sub_eq_add_neg]⟩)
    · exact Or.inr (Or.inr ⟨i, by simp [rootVec, lineVec, two_smul]⟩)
    · exact Or.inr (Or.inl ⟨j, i, hij, by simp [rootVec, lineVec, add_comm]⟩)
  · have := j.2
    omega
  · have hji : j < i := by
      change (j : ℕ) < i
      have := i.2
      have := j.2
      omega
    exact Or.inl ⟨j, i, hji, by simp [rootVec, lineVec, sub_eq_add_neg, add_comm]⟩

theorem exists_rootVec_of_mem_posRoots {α : Fin r → ℤ} (h : α ∈ posRoots r) :
    ∃ a b : Fin r ⊕ Fin r, (flagOrder r a : ℕ) < flagOrder r b ∧ α = rootVec a b := by
  rcases mem_posRoots.mp h with ⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩ | ⟨i, rfl⟩
  · exact ⟨Sum.inl i, Sum.inl j, by simpa [flagOrder_inl] using hij, rfl⟩
  · refine ⟨Sum.inl i, Sum.inr j, ?_, by simp [rootVec, lineVec, sub_eq_add_neg]⟩
    rw [flagOrder_inl, flagOrder_inr]
    have := i.2
    omega
  · refine ⟨Sum.inl i, Sum.inr i, ?_, by simp [rootVec, lineVec, two_smul]⟩
    rw [flagOrder_inl, flagOrder_inr]
    have := i.2
    omega

theorem flagOrder_ne {a b : Fin r ⊕ Fin r} (hab : a ≠ b) :
    (flagOrder r a : ℕ) ≠ flagOrder r b := fun h =>
  hab ((flagOrder r).injective (Fin.ext h))

theorem rootVec_mem_posRoots_iff {a b : Fin r ⊕ Fin r} (hab : a ≠ b) :
    rootVec a b ∈ posRoots r ↔ (flagOrder r a : ℕ) < flagOrder r b := by
  refine ⟨fun h => ?_, rootVec_mem_posRoots⟩
  by_contra hlt
  have hgt : (flagOrder r b : ℕ) < flagOrder r a :=
    lt_of_le_of_ne (not_lt.mp hlt) (flagOrder_ne hab).symm
  have h1 := height_pos_of_mem_posRoots h
  have h2 := height_rootVec_pos hgt
  rw [← neg_rootVec, height_neg] at h2
  omega

theorem rootVec_mem_negRoots_iff {a b : Fin r ⊕ Fin r} (hab : a ≠ b) :
    rootVec a b ∈ negRoots r ↔ (flagOrder r b : ℕ) < flagOrder r a := by
  rw [mem_negRoots, neg_rootVec, rootVec_mem_posRoots_iff (Ne.symm hab)]

theorem rootVec_mem_posRoots_or {a b : Fin r ⊕ Fin r} (hab : a ≠ b) :
    rootVec a b ∈ posRoots r ∨ rootVec a b ∈ negRoots r := by
  rw [rootVec_mem_posRoots_iff hab, rootVec_mem_negRoots_iff hab]
  exact lt_or_gt_of_ne (flagOrder_ne hab)

variable (K) in
@[expose] def rootSubgroup (α : Fin r → ℤ) : Subgroup (StatedSp r K) :=
  ⨆ p : {p : (Fin r ⊕ Fin r) × (Fin r ⊕ Fin r) // p.1 ≠ p.2 ∧ rootVec p.1 p.2 = α},
    (pairRootHom K p.2.1).range

theorem range_pairRootHom_le_rootSubgroup {a b : Fin r ⊕ Fin r} (hab : a ≠ b) :
    (pairRootHom K hab).range ≤ rootSubgroup K (rootVec a b) :=
  le_iSup_of_le ⟨(a, b), hab, rfl⟩ le_rfl

theorem pairRootElt_mem_rootSubgroup {a b : Fin r ⊕ Fin r} (hab : a ≠ b) (t : K) :
    pairRootElt hab t ∈ rootSubgroup K (rootVec a b) :=
  range_pairRootHom_le_rootSubgroup hab ⟨Multiplicative.ofAdd t, rfl⟩

theorem range_pairRootHom_partner {a b : Fin r ⊕ Fin r} (hab : a ≠ b)
    (hab' : b.swap ≠ a.swap) : (pairRootHom K hab').range = (pairRootHom K hab).range := by
  have hs : ∀ t : K, pairRootElt hab' t =
      pairRootElt hab (-(lineSign K a * lineSign K b) * t) := fun t =>
    statedSp_ext (by rw [coe_pairRootElt, coe_pairRootElt, pairRootMat_partner])
  have hunit : (-(lineSign K a * lineSign K b)) * (-(lineSign K a * lineSign K b)) = 1 := by
    rw [neg_mul_neg, mul_mul_mul_comm, lineSign_mul_self, lineSign_mul_self, one_mul]
  ext g
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨Multiplicative.ofAdd (-(lineSign K a * lineSign K b) * t.toAdd), (hs t.toAdd).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨Multiplicative.ofAdd (-(lineSign K a * lineSign K b) * t.toAdd), ?_⟩
    change pairRootElt hab' _ = pairRootElt hab t.toAdd
    rw [hs, toAdd_ofAdd, ← mul_assoc, hunit, one_mul]

theorem rootSubgroup_eq_range {a b : Fin r ⊕ Fin r} (hab : a ≠ b) :
    rootSubgroup K (rootVec a b) = (pairRootHom K hab).range := by
  refine le_antisymm (iSup_le fun p => ?_) (range_pairRootHom_le_rootSubgroup hab)
  obtain ⟨⟨c, d⟩, hcd, hroot⟩ := p
  rcases (rootVec_eq_rootVec_iff hab hcd).mp hroot.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact le_rfl
  · exact (range_pairRootHom_partner hab hcd).le

@[expose] def simpleSnd (k : Fin r) : Fin r ⊕ Fin r :=
  if h : (k : ℕ) + 1 < r then Sum.inl ⟨k + 1, h⟩ else Sum.inr k

theorem inl_ne_simpleSnd (k : Fin r) : Sum.inl k ≠ simpleSnd k := by
  unfold simpleSnd
  split_ifs with h
  · intro h'
    have := congrArg
      (fun x : Fin r ⊕ Fin r => Sum.elim (fun i : Fin r => (i : ℕ)) (fun _ => 0) x) h'
    simp at this
  · simp

variable (r) in
@[expose] def simpleRootVec (k : Fin r) : Fin r → ℤ :=
  if h : (k : ℕ) + 1 < r then Pi.single k 1 - Pi.single ⟨k + 1, h⟩ 1 else 2 • Pi.single k 1

theorem rootVec_simpleSnd (k : Fin r) :
    rootVec (Sum.inl k) (simpleSnd k) = simpleRootVec r k := by
  unfold simpleSnd simpleRootVec
  split_ifs with h
  · rfl
  · simp [rootVec, lineVec, two_smul]

variable (r) in
@[expose] def simpleRefl (k : Fin r) : Equiv.Perm (Fin r ⊕ Fin r) :=
  if h : (k : ℕ) + 1 < r then
    Equiv.sumCongr (Equiv.swap k ⟨k + 1, h⟩) (Equiv.swap k ⟨k + 1, h⟩)
  else Equiv.swap (Sum.inl k) (Sum.inr k)

theorem simpleRefl_mem (k : Fin r) : simpleRefl r k ∈ signedPermGroup r := by
  unfold simpleRefl
  split_ifs
  · exact sumCongr_mem_signedPermGroup _
  · exact swap_inl_inr_mem_signedPermGroup k

theorem simpleRefl_mul_self (k : Fin r) : simpleRefl r k * simpleRefl r k = 1 := by
  unfold simpleRefl
  split_ifs
  · rw [Equiv.Perm.sumCongr_mul, Equiv.swap_mul_self, Equiv.Perm.sumCongr_one]
  · exact Equiv.swap_mul_self _ _

theorem simpleRefl_inv (k : Fin r) : (simpleRefl r k)⁻¹ = simpleRefl r k :=
  inv_eq_of_mul_eq_one_right (simpleRefl_mul_self k)

variable (K) in
@[expose] def weylRep (k : Fin r) : StatedSp r K :=
  pairRootElt (inl_ne_simpleSnd k) 1 * pairRootElt (inl_ne_simpleSnd k).symm (-1) *
    pairRootElt (inl_ne_simpleSnd k) 1

theorem weylRep_mem_of_rootSubgroup_le {A : Subgroup (StatedSp r K)} (k : Fin r)
    (hpos : rootSubgroup K (simpleRootVec r k) ≤ A)
    (hneg : rootSubgroup K (-simpleRootVec r k) ≤ A) : weylRep K k ∈ A := by
  have h1 : pairRootElt (inl_ne_simpleSnd k) (1 : K) ∈ A := hpos (by
    rw [← rootVec_simpleSnd]
    exact pairRootElt_mem_rootSubgroup _ _)
  have h2 : pairRootElt (inl_ne_simpleSnd k).symm (-1 : K) ∈ A := hneg (by
    rw [← rootVec_simpleSnd, neg_rootVec]
    exact pairRootElt_mem_rootSubgroup _ _)
  exact mul_mem (mul_mem h1 h2) h1

theorem root_matrix_data :
    (∀ (a b : Fin r ⊕ Fin r) (hab : a ≠ b) (s t : K),
      (pairRootMat K a b t)ᵀ * fromBlocks 0 1 (-1) 0 * pairRootMat K a b t =
        fromBlocks 0 1 (-1) 0 ∧
      pairRootElt hab s * pairRootElt hab t = pairRootElt hab (s + t) ∧
      (pairRootElt hab t)⁻¹ = pairRootElt hab (-t) ∧
      Function.Injective (pairRootHom K hab) ∧
      rootSubgroup K (rootVec a b) = (pairRootHom K hab).range) ∧
    (∀ (i j : Fin r) (t : K), i ≠ j →
      pairRootMat K (Sum.inl i) (Sum.inl j) t =
          1 + t • single (Sum.inl i) (Sum.inl j) 1 - t • single (Sum.inr j) (Sum.inr i) 1 ∧
        rootVec (Sum.inl i) (Sum.inl j) = Pi.single i 1 - Pi.single j 1) ∧
    (∀ (i j : Fin r) (t : K), i ≠ j →
      pairRootMat K (Sum.inl i) (Sum.inr j) t =
          1 + t • (single (Sum.inl i) (Sum.inr j) 1 + single (Sum.inl j) (Sum.inr i) 1) ∧
        rootVec (Sum.inl i) (Sum.inr j) = Pi.single i 1 + Pi.single j 1 ∧
      pairRootMat K (Sum.inr i) (Sum.inl j) t =
          1 + t • (single (Sum.inr i) (Sum.inl j) 1 + single (Sum.inr j) (Sum.inl i) 1) ∧
        rootVec (Sum.inr i) (Sum.inl j) = -Pi.single i 1 - Pi.single j 1) ∧
    (∀ (i : Fin r) (t : K),
      pairRootMat K (Sum.inl i) (Sum.inr i) t = 1 + t • single (Sum.inl i) (Sum.inr i) 1 ∧
        rootVec (Sum.inl i) (Sum.inr i) = 2 • Pi.single i 1 ∧
      pairRootMat K (Sum.inr i) (Sum.inl i) t = 1 + t • single (Sum.inr i) (Sum.inl i) 1 ∧
        rootVec (Sum.inr i) (Sum.inl i) = -(2 • Pi.single i 1)) ∧
    (∀ k : Fin r, simpleRefl r k ∈ signedPermGroup r ∧ simpleRefl r k * simpleRefl r k = 1 ∧
      rootVec (Sum.inl k) (simpleSnd k) = simpleRootVec r k ∧
      weylRep K k = pairRootElt (inl_ne_simpleSnd k) 1 *
        pairRootElt (inl_ne_simpleSnd k).symm (-1) * pairRootElt (inl_ne_simpleSnd k) 1) := by
  refine ⟨fun a b hab s t => ⟨pairRootMat_symplectic hab t, ?_, ?_, pairRootHom_injective hab,
    rootSubgroup_eq_range hab⟩, fun i j t _ => ⟨pairRootMat_inl_inl t, rfl⟩,
    fun i j t hij => ⟨pairRootMat_inl_inr hij t, by simp [rootVec, lineVec, sub_eq_add_neg],
      pairRootMat_inr_inl hij t, by simp [rootVec, lineVec]⟩,
    fun i t => ⟨pairRootMat_inl_inr_self i t, by simp [rootVec, lineVec, two_smul],
      pairRootMat_inr_inl_self i t, by simp [rootVec, lineVec, two_smul]; abel⟩,
    fun k => ⟨simpleRefl_mem k, simpleRefl_mul_self k, rootVec_simpleSnd k, rfl⟩⟩
  · exact (map_mul (pairRootHom K hab) (Multiplicative.ofAdd s) (Multiplicative.ofAdd t)).symm
  · exact (map_inv (pairRootHom K hab) (Multiplicative.ofAdd t)).symm

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
