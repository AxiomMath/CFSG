module

public import CFSG.ClassicalInvolution.WeakCT.Blocks
public import CFSG.ClassicalInvolution.SL2Facts
public import CFSG.ClassicalInvolution.Models.LinearPairs.Frame

public section

namespace CFSG.ClassicalInvolution.Models

open Matrix CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.Phan (blockMat blockSel blockMat_apply blockMat_mul blockMat_one
  det_blockMat blockIdx blockSel_transpose_mul_self)
open scoped MatrixGroups

theorem two_ne_zero_of_odd_natCard {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K)) :
    (2 : K) ≠ 0 :=
  CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd

section LongRootGroup

variable {K : Type} [Field K] {n : ℕ}

@[expose] def longRootGroup (i : Matrix (Fin n) (Fin n) K) : Subgroup SL(n, K) where
  carrier := {x | (x : Matrix (Fin n) (Fin n) K) * i = i * x ∧
    (x : Matrix (Fin n) (Fin n) K) * (1 + i) = 1 + i}
  one_mem' := by simp
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc, hy1, ← Matrix.mul_assoc, hx1,
        Matrix.mul_assoc]
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc, hy2, hx2]
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    have hxy : (x : Matrix (Fin n) (Fin n) K) *
        ((x⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hyx : ((x⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) *
        (x : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    refine ⟨?_, ?_⟩
    · calc ((x⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) * i
          = ((x⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) * i * (x * ((x⁻¹ : SL(n, K)) :
              Matrix (Fin n) (Fin n) K)) := by rw [hxy, Matrix.mul_one]
        _ = ((x⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) * (i * x) * ((x⁻¹ : SL(n, K)) :
              Matrix (Fin n) (Fin n) K) := by simp only [Matrix.mul_assoc]
        _ = i * ((x⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) := by
          rw [← hx1]
          simp only [← Matrix.mul_assoc, hyx, Matrix.one_mul]
    · calc ((x⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) * (1 + i)
          = ((x⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) * ((x : Matrix (Fin n) (Fin n) K) *
              (1 + i)) := by rw [hx2]
        _ = 1 + i := by rw [← Matrix.mul_assoc, hyx, Matrix.one_mul]

theorem mem_longRootGroup {i : Matrix (Fin n) (Fin n) K} {x : SL(n, K)} :
    x ∈ longRootGroup i ↔
      (x : Matrix (Fin n) (Fin n) K) * i = i * x ∧
        (x : Matrix (Fin n) (Fin n) K) * (1 + i) = 1 + i :=
  Iff.rfl

end LongRootGroup

section Standard

variable (K : Type) [Field K]

@[expose] def negBlock (n j : ℕ) : Matrix (Fin n) (Fin n) K :=
  blockMat n j (-1 : Matrix (Fin 2) (Fin 2) K)

variable {K} {n : ℕ}

theorem negBlock_eq_diagonal (n j : ℕ) :
    negBlock K n j = Matrix.diagonal (fun a : Fin n =>
      if j ≤ a.val ∧ a.val < j + 2 then (-1 : K) else 1) := by
  ext a b
  rw [negBlock, blockMat_apply, Matrix.diagonal_apply]
  by_cases hb : (j ≤ a.val ∧ a.val < j + 2) ∧ (j ≤ b.val ∧ b.val < j + 2)
  · rw [dite_eq_left hb]
    by_cases hab : a = b
    · subst hab
      simp [hb.1]
    · have : (⟨a.val - j, by omega⟩ : Fin 2) ≠ ⟨b.val - j, by omega⟩ := by
        intro h
        apply hab
        apply Fin.ext
        have := congrArg Fin.val h
        simp only at this
        omega
      simp [hab, this]
  · rw [dite_eq_right hb]
    by_cases hab : a = b
    · subst hab
      have : ¬ (j ≤ a.val ∧ a.val < j + 2) := fun h => hb ⟨h, h⟩
      simp [this]
    · simp [hab]

theorem negBlock_mul_self (n j : ℕ) : negBlock K n j * negBlock K n j = 1 := by
  rw [negBlock_eq_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

@[expose] def rootSL2 (K : Type) [Field K] {n : ℕ} (hn : 2 ≤ n) : Subgroup SL(n, K) :=
  (blockSL K n 2 0 (by omega)).range

@[expose] def rootInv (K : Type) [Field K] {n : ℕ} (hn : 2 ≤ n) : SL(n, K) :=
  blockSL K n 2 0 (by omega) (-1)

theorem coe_rootInv (hn : 2 ≤ n) :
    ((rootInv K hn : SL(n, K)) : Matrix (Fin n) (Fin n) K) = negBlock K n 0 := by
  simp [rootInv, coe_blockSL, negBlock]

theorem rootInv_mem_rootSL2 (hn : 2 ≤ n) : rootInv K hn ∈ rootSL2 K hn :=
  ⟨-1, rfl⟩

theorem coe_blockSL_neg_one {j : ℕ} (hj : j + 2 ≤ n) :
    ((blockSL K n 2 j hj (-1) : SL(n, K)) : Matrix (Fin n) (Fin n) K) = negBlock K n j := by
  simp [coe_blockSL, negBlock]

theorem blockSL_mem_longRootGroup {j : ℕ} (hj : j + 2 ≤ n) (A : SL(2, K)) :
    blockSL K n 2 j hj A ∈ longRootGroup (negBlock K n j) := by
  have hA : (-1 : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) =
      (A : Matrix (Fin 2) (Fin 2) K) * (-1) := by simp
  refine ⟨?_, ?_⟩
  · rw [coe_blockSL, negBlock, ← blockMat_mul hj, ← blockMat_mul hj, hA]
  · rw [coe_blockSL, negBlock, Matrix.mul_add, Matrix.mul_one, ← blockMat_mul hj]
    have : ((A : Matrix (Fin 2) (Fin 2) K) * (-1)) = -(A : Matrix (Fin 2) (Fin 2) K) := by simp
    rw [this]
    unfold blockMat
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul]
    abel

theorem exists_blockSL_of_mem_longRootGroup (h2 : (2 : K) ≠ 0) {j : ℕ} (hj : j + 2 ≤ n)
    {x : SL(n, K)} (hx : x ∈ longRootGroup (negBlock K n j)) :
    ∃ A : SL(2, K), blockSL K n 2 j hj A = x := by
  obtain ⟨h1, h3⟩ := hx
  rw [negBlock_eq_diagonal] at h1 h3
  set X : Matrix (Fin n) (Fin n) K := (x : Matrix (Fin n) (Fin n) K) with hX
  set d : Fin n → K := fun a => if j ≤ a.val ∧ a.val < j + 2 then (-1 : K) else 1 with hd
  have e1 : ∀ a b, X a b * d b = d a * X a b := fun a b => by
    have := congr_fun (congr_fun h1 a) b
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  have h3' : X * Matrix.diagonal (fun a => 1 + d a) = Matrix.diagonal (fun a => 1 + d a) := by
    have : (1 : Matrix (Fin n) (Fin n) K) + Matrix.diagonal d =
        Matrix.diagonal (fun a => 1 + d a) := by
      rw [← Matrix.diagonal_one, Matrix.diagonal_add]
    rwa [this] at h3
  have e3 : ∀ a b, X a b * (1 + d b) = if a = b then 1 + d a else 0 := fun a b => by
    have := congr_fun (congr_fun h3' a) b
    simpa [Matrix.mul_diagonal, Matrix.diagonal_apply] using this
  let A : Matrix (Fin 2) (Fin 2) K := Matrix.of fun p q => X (blockIdx j hj p) (blockIdx j hj q)
  have hXA : X = blockMat n j A := by
    ext a b
    rw [blockMat_apply]
    by_cases hab : (j ≤ a.val ∧ a.val < j + 2) ∧ (j ≤ b.val ∧ b.val < j + 2)
    · rw [dite_eq_left hab]
      have ha : blockIdx j hj (⟨a.val - j, by omega⟩ : Fin 2) = a :=
        Fin.ext (by simp only [blockIdx]; omega)
      have hb : blockIdx j hj (⟨b.val - j, by omega⟩ : Fin 2) = b :=
        Fin.ext (by simp only [blockIdx]; omega)
      simp only [A, Matrix.of_apply, ha, hb]
    · rw [dite_eq_right hab]
      by_cases hb : j ≤ b.val ∧ b.val < j + 2
      · have ha : ¬ (j ≤ a.val ∧ a.val < j + 2) := fun h => hab ⟨h, hb⟩
        have hne : a ≠ b := fun h => ha (h ▸ hb)
        have := e1 a b
        simp only [hd, ite_eq_left hb, ite_eq_right ha] at this
        rw [Matrix.one_apply_ne hne]
        have h' : (2 : K) * X a b = 0 := by linear_combination -this
        exact (mul_eq_zero.mp h').resolve_left h2
      · have := e3 a b
        by_cases hab' : a = b
        · subst hab'
          rw [Matrix.one_apply_eq]
          simp only [hd, ite_eq_right hb, ite_true] at this
          have h' : (2 : K) * (X a a - 1) = 0 := by linear_combination this
          have := (mul_eq_zero.mp h').resolve_left h2
          linear_combination this
        · rw [Matrix.one_apply_ne hab']
          simp only [hd, ite_eq_right hb, hab', ite_false] at this
          have h' : (2 : K) * X a b = 0 := by linear_combination this
          exact (mul_eq_zero.mp h').resolve_left h2
  have hdet : A.det = 1 := by
    rw [← det_blockMat hj A, ← hXA]
    exact x.2
  exact ⟨⟨A, hdet⟩, Subtype.ext hXA.symm⟩

theorem range_blockSL_eq_longRootGroup (h2 : (2 : K) ≠ 0) {j : ℕ} (hj : j + 2 ≤ n) :
    (blockSL K n 2 j hj).range = longRootGroup (negBlock K n j) := by
  ext x
  constructor
  · rintro ⟨A, rfl⟩
    exact blockSL_mem_longRootGroup hj A
  · intro hx
    obtain ⟨A, hA⟩ := exists_blockSL_of_mem_longRootGroup h2 hj hx
    exact ⟨A, hA⟩

theorem rootSL2_eq_longRootGroup (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) :
    rootSL2 K hn = longRootGroup (negBlock K n 0) :=
  range_blockSL_eq_longRootGroup h2 (by omega)

end Standard

section Conjugation

variable {K : Type} [Field K] {n : ℕ}

theorem mem_map_conj_iff {H : Subgroup SL(n, K)} {g x : SL(n, K)} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  rw [Subgroup.mem_map_equiv]
  simp

theorem coe_mul_coe_inv (g : SL(n, K)) :
    (g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem coe_inv_mul_coe (g : SL(n, K)) :
    ((g⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem conj_mul_conj {A B Pm Qm : Matrix (Fin n) (Fin n) K} (hQP : Qm * Pm = 1) :
    (Pm * A * Qm) * (Pm * B * Qm) = Pm * (A * B) * Qm := by
  calc (Pm * A * Qm) * (Pm * B * Qm) = Pm * A * (Qm * Pm) * B * Qm := by
        simp only [Matrix.mul_assoc]
    _ = Pm * (A * B) * Qm := by
        rw [hQP, Matrix.mul_one]
        simp only [Matrix.mul_assoc]

theorem conj_one_add {A Pm Qm : Matrix (Fin n) (Fin n) K} (hPQ : Pm * Qm = 1) :
    Pm * (1 + A) * Qm = 1 + Pm * A * Qm := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPQ]

theorem mem_longRootGroup_conj_aux {i xm Pm Qm : Matrix (Fin n) (Fin n) K} (hPQ : Pm * Qm = 1)
    (hQP : Qm * Pm = 1) (h1 : xm * i = i * xm) (h3 : xm * (1 + i) = 1 + i) :
    (Pm * xm * Qm) * (Pm * i * Qm) = (Pm * i * Qm) * (Pm * xm * Qm) ∧
      (Pm * xm * Qm) * (1 + Pm * i * Qm) = 1 + Pm * i * Qm := by
  refine ⟨?_, ?_⟩
  · rw [conj_mul_conj hQP, conj_mul_conj hQP, h1]
  · rw [← conj_one_add hPQ, conj_mul_conj hQP, h3]

theorem conj_mem_longRootGroup_conj {i : Matrix (Fin n) (Fin n) K} (g : SL(n, K))
    {x : SL(n, K)} (hx : x ∈ longRootGroup i) :
    g * x * g⁻¹ ∈ longRootGroup ((g : Matrix (Fin n) (Fin n) K) * i *
      ((g⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨h1, h3⟩ := hx
  have := mem_longRootGroup_conj_aux (coe_mul_coe_inv g) (coe_inv_mul_coe g) h1 h3
  exact mem_longRootGroup.mpr (by simpa only [Matrix.SpecialLinearGroup.coe_mul] using this)

theorem longRootGroup_conj (i : Matrix (Fin n) (Fin n) K) (g : SL(n, K)) :
    longRootGroup ((g : Matrix (Fin n) (Fin n) K) * i * ((g⁻¹ : SL(n, K)) :
      Matrix (Fin n) (Fin n) K)) = (longRootGroup i).map (MulAut.conj g).toMonoidHom := by
  ext y
  rw [mem_map_conj_iff]
  constructor
  · intro hy
    have h := conj_mem_longRootGroup_conj g⁻¹ hy
    have e : ((g⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) *
        ((g : Matrix (Fin n) (Fin n) K) * i * ((g⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K)) *
          (((g⁻¹)⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) = i := by
      rw [inv_inv]
      calc _ = (((g⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K)) *
            i * (((g⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) *
              (g : Matrix (Fin n) (Fin n) K)) := by simp only [Matrix.mul_assoc]
        _ = i := by rw [coe_inv_mul_coe, Matrix.one_mul, Matrix.mul_one]
    rw [e, inv_inv] at h
    exact h
  · intro hy
    have h := conj_mem_longRootGroup_conj g hy
    have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rwa [e] at h

theorem longRootGroup_eq_map_conj_of_mul_eq {i D : Matrix (Fin n) (Fin n) K} (P : SL(n, K))
    (h : i * (P : Matrix (Fin n) (Fin n) K) = (P : Matrix (Fin n) (Fin n) K) * D) :
    longRootGroup i = (longRootGroup D).map (MulAut.conj P).toMonoidHom := by
  have e : i = (P : Matrix (Fin n) (Fin n) K) * D *
      ((P⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) := by
    rw [← h, Matrix.mul_assoc, coe_mul_coe_inv, Matrix.mul_one]
  rw [e]
  exact longRootGroup_conj D P

theorem conj_mem_longRootGroup_of_commute {i : Matrix (Fin n) (Fin n) K} {c x : SL(n, K)}
    (hc : (c : Matrix (Fin n) (Fin n) K) * i = i * c) (hx : x ∈ longRootGroup i) :
    c * x * c⁻¹ ∈ longRootGroup i := by
  have h := conj_mem_longRootGroup_conj c hx
  have e : (c : Matrix (Fin n) (Fin n) K) * i *
      ((c⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) = i := by
    rw [hc, Matrix.mul_assoc, coe_mul_coe_inv, Matrix.mul_one]
  rwa [e] at h

end Conjugation

section LongRoot

variable {K : Type} [Field K] {n : ℕ}

@[expose] def IsLongRootSL2 (hn : 2 ≤ n) (L : Subgroup SL(n, K)) (i : SL(n, K)) : Prop :=
  ∃ g : SL(n, K), L = (rootSL2 K hn).map (MulAut.conj g).toMonoidHom ∧
    i = g * rootInv K hn * g⁻¹

theorem isLongRootSL2_standard (hn : 2 ≤ n) :
    IsLongRootSL2 hn (rootSL2 K hn) (rootInv K hn) :=
  ⟨1, by ext x; simp, by simp⟩

theorem IsLongRootSL2.conj {hn : 2 ≤ n} {L : Subgroup SL(n, K)} {i : SL(n, K)}
    (h : IsLongRootSL2 hn L i) (g : SL(n, K)) :
    IsLongRootSL2 hn (L.map (MulAut.conj g).toMonoidHom) (g * i * g⁻¹) := by
  obtain ⟨g₀, rfl, rfl⟩ := h
  refine ⟨g * g₀, ?_, by group⟩
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem IsLongRootSL2.eq_longRootGroup (h2 : (2 : K) ≠ 0) {hn : 2 ≤ n}
    {L : Subgroup SL(n, K)} {i : SL(n, K)} (h : IsLongRootSL2 hn L i) :
    L = longRootGroup (i : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨g, rfl, rfl⟩ := h
  rw [rootSL2_eq_longRootGroup h2 hn, ← longRootGroup_conj]
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_rootInv]

theorem IsLongRootSL2.mem_iff (h2 : (2 : K) ≠ 0) {hn : 2 ≤ n}
    {L : Subgroup SL(n, K)} {i : SL(n, K)} (h : IsLongRootSL2 hn L i) {x : SL(n, K)} :
    x ∈ L ↔ (x : Matrix (Fin n) (Fin n) K) * i = i * x ∧
      (x : Matrix (Fin n) (Fin n) K) * (1 + i) = 1 + i := by
  rw [h.eq_longRootGroup h2]
  exact mem_longRootGroup

end LongRoot

section Classical

variable {K : Type} [Field K] {n : ℕ}

theorem isClassicalSL2_rootSL2 (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) :
    IsClassicalSL2 K (rootSL2 K hn) (rootInv K hn) where
  nonempty_mulEquiv :=
    ⟨(MonoidHom.ofInjective (blockSL_injective (K := K) (m := n) (k := 2) (i := 0)
      (by omega))).symm⟩
  mem := rootInv_mem_rootSL2 hn
  orderOf_eq_two := by
    rw [rootInv, orderOf_injective (blockSL K n 2 0 (by omega)) (blockSL_injective _) (-1)]
    exact CFSG.Semidihedral.OddFieldSL2.minusIdentity_orderOf K h2
  le_centralizer := by
    rintro _ ⟨A, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, rootInv, ← map_mul, ← map_mul, mul_neg, mul_one,
      neg_mul, one_mul]
  centralizer_le_normalizer := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    have e : ∀ {c : SL(n, K)}, c ∈ Subgroup.centralizer ({rootInv K hn} : Set SL(n, K)) →
        (c : Matrix (Fin n) (Fin n) K) * negBlock K n 0 = negBlock K n 0 * c := fun {c} hc => by
      have := congrArg (fun g : SL(n, K) => (g : Matrix (Fin n) (Fin n) K))
        (Subgroup.mem_centralizer_singleton_iff.mp hc)
      simpa [coe_rootInv] using this
    have e1 := e hc
    have e2 := e ((Subgroup.centralizer ({rootInv K hn} : Set SL(n, K))).inv_mem hc)
    intro x
    rw [rootSL2_eq_longRootGroup h2 hn]
    constructor
    · exact fun hx => conj_mem_longRootGroup_of_commute e1 hx
    · intro hx
      have := conj_mem_longRootGroup_of_commute e2 hx
      have e3 : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
      rwa [e3] at this

theorem IsLongRootSL2.isClassicalSL2 (h2 : (2 : K) ≠ 0) {hn : 2 ≤ n}
    {L : Subgroup SL(n, K)} {i : SL(n, K)} (h : IsLongRootSL2 hn L i) : IsClassicalSL2 K L i := by
  obtain ⟨g, rfl, rfl⟩ := h
  exact (isClassicalSL2_rootSL2 h2 hn).conj g

end Classical

section Spaces

variable {K : Type} [Field K] {n : ℕ}

@[expose] def minusSpace (i : SL(n, K)) : Submodule K (Fin n → K) :=
  eigSpace (i : Matrix (Fin n) (Fin n) K) (-1)

@[expose] def fixSpace (i : SL(n, K)) : Submodule K (Fin n → K) :=
  eigSpace (i : Matrix (Fin n) (Fin n) K) 1

theorem mem_minusSpace {i : SL(n, K)} {v : Fin n → K} :
    v ∈ minusSpace i ↔ (i : Matrix (Fin n) (Fin n) K) *ᵥ v = -v :=
  mem_eigSpace_neg_one

theorem mem_fixSpace {i : SL(n, K)} {v : Fin n → K} :
    v ∈ fixSpace i ↔ (i : Matrix (Fin n) (Fin n) K) *ᵥ v = v :=
  mem_eigSpace_one

end Spaces

end CFSG.ClassicalInvolution.Models
