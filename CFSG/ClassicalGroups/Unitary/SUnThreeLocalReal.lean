module

public import CFSG.ClassicalGroups.Unitary.SUnThreeLocalDefs
public import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalSignedPerm
import Mathlib.LinearAlgebra.Matrix.Permutation

public section

namespace CFSG.ClassicalGroups.SUnThreeLocal

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.ThreeLocalSignedPerm

variable {L : Type} [Field L] {n : ℕ} {σ : L ≃+* L}

private def permGL (L : Type) [Field L] (n : ℕ) : Equiv.Perm (Fin n) →* GL (Fin n) L :=
  MonoidHom.toHomUnits (Matrix.permMatrixHom (n := Fin n) (R := L))

private theorem coe_permGL (π : Equiv.Perm (Fin n)) :
    ((permGL L n π : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = (π⁻¹).permMatrix L :=
  rfl

private theorem permMatrix_apply (π : Equiv.Perm (Fin n)) (a b : Fin n) :
    (π.permMatrix L) a b = if π a = b then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

private theorem det_permGL (π : Equiv.Perm (Fin n)) :
    ((permGL L n π : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det =
      (((Equiv.Perm.sign π : ℤˣ) : ℤ) : L) := by
  rw [coe_permGL, Matrix.det_permutation, Equiv.Perm.sign_inv]

private theorem permGL_mul_diagGL (π : Equiv.Perm (Fin n)) (d : Fin n → Lˣ) :
    permGL L n π * diagGL L n d = diagGL L n (fun a => d (π⁻¹ a)) * permGL L n π := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_permGL, coe_diagGL, coe_diagGL]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, permMatrix_apply]
  by_cases h : π⁻¹ a = b
  · subst h
    simp
  · rw [if_neg h]
    simp

private theorem conjTr_permGL (σ : L ≃+* L) (π : Equiv.Perm (Fin n)) :
    conjTr σ ((permGL L n π : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = π.permMatrix L := by
  rw [coe_permGL, conjTr]
  ext a b
  simp only [Matrix.transpose_apply, Matrix.map_apply, permMatrix_apply]
  by_cases h : π a = b
  · have h' : π.symm b = a := by rw [← h]; simp
    simp [h, h']
  · have h' : ¬ π.symm b = a := by
      intro h'
      apply h
      rw [← h']
      simp
    simp [h, h']

private theorem antidiag_eq_permMatrix :
    (antidiag n : Matrix (Fin n) (Fin n) L) = (Fin.revPerm : Equiv.Perm (Fin n)).permMatrix L := by
  ext a b
  by_cases h : b = Fin.rev a
  · subst h
    simp [antidiag, permMatrix_apply]
  · have h' : Fin.rev a ≠ b := fun h'' => h h''.symm
    simp [antidiag, permMatrix_apply, h, h']

private theorem permGL_isometry (σ : L ≃+* L) (π : Equiv.Perm (Fin n))
    (hπ : ∀ a, π (Fin.rev a) = Fin.rev (π a)) :
    conjTr σ ((permGL L n π : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * antidiag n *
      ((permGL L n π : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = antidiag n := by
  have hcomm : (Fin.revPerm : Equiv.Perm (Fin n)) * π = π * Fin.revPerm :=
    Equiv.ext fun a => by
      simp only [Equiv.Perm.mul_apply, Fin.revPerm_apply]
      exact (hπ a).symm
  rw [conjTr_permGL, coe_permGL, antidiag_eq_permMatrix, ← Matrix.permMatrix_mul,
    ← Matrix.permMatrix_mul, hcomm, inv_mul_cancel_left]

private theorem permGL_mul_diagGL_mem_SU (π : Equiv.Perm (Fin n))
    (hπ : ∀ a, π (Fin.rev a) = Fin.rev (π a)) (m : Fin n → Lˣ)
    (hm : ∀ a, σ (m a : L) * (m (Fin.rev a) : L) = 1)
    (hdet : (((Equiv.Perm.sign π : ℤˣ) : ℤ) : L) * ∏ a, (m a : L) = 1) :
    permGL L n π * diagGL L n m ∈ SU σ n := by
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Matrix.det_mul, det_permGL, det_diagGL]
    exact hdet
  · rw [Units.val_mul, conjTr_mul]
    calc conjTr σ ((diagGL L n m : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          conjTr σ ((permGL L n π : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * antidiag n *
          (((permGL L n π : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
            ((diagGL L n m : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))
        = conjTr σ ((diagGL L n m : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          (conjTr σ ((permGL L n π : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * antidiag n *
            ((permGL L n π : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
          ((diagGL L n m : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
          simp only [Matrix.mul_assoc]
      _ = conjTr σ ((diagGL L n m : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * antidiag n *
          ((diagGL L n m : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
          rw [permGL_isometry σ π hπ, Matrix.mul_assoc]
      _ = antidiag n := conjTr_diagGL_mul_antidiag_mul m hm

section Realizers

variable (ζ : FixedCubeRoot σ)

private theorem realizes_of_perm_diag (hn : n = 6 ∨ n = 7) (g : SU σ n)
    (π : Equiv.Perm (Fin n)) (m : Fin n → Lˣ)
    (hg : (g : GL (Fin n) L) = permGL L n π * diagGL L n m)
    (α : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3)) (hα : ∀ v a, wt n (α v) (π a) = wt n v a) :
    Realizes (c₀ ζ hn) g α := by
  intro v
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_eq_iff_eq_mul, hg,
    coe_c₀, coe_c₀, toAdd_ofAdd]
  set d : Fin n → Lˣ := fun a => ζ.pow (wt n (Multiplicative.toAdd v) a) with hd
  have key : (fun a => ζ.pow (wt n (α (Multiplicative.toAdd v)) a)) = fun a => d (π⁻¹ a) := by
    funext a
    have := hα (Multiplicative.toAdd v) (π⁻¹ a)
    have h' : π (π⁻¹ a) = a := by simp
    rw [h'] at this
    simp only [hd, this]
  rw [key]
  calc permGL L n π * diagGL L n m * diagGL L n d
      = permGL L n π * (diagGL L n m * diagGL L n d) := mul_assoc _ _ _
    _ = permGL L n π * (diagGL L n d * diagGL L n m) := by
        rw [((Commute.all m d).map (diagGL L n)).eq]
    _ = (permGL L n π * diagGL L n d) * diagGL L n m := (mul_assoc _ _ _).symm
    _ = (diagGL L n (fun a => d (π⁻¹ a)) * permGL L n π) * diagGL L n m := by
        rw [permGL_mul_diagGL]
    _ = diagGL L n (fun a => d (π⁻¹ a)) * (permGL L n π * diagGL L n m) := mul_assoc _ _ _

private def pairSwap (hn : n = 6 ∨ n = 7) (x y : Fin 3) : Equiv.Perm (Fin n) :=
  Equiv.swap (pos hn x) (pos hn y) * Equiv.swap (Fin.rev (pos hn x)) (Fin.rev (pos hn y))

private theorem pairSwap_pos (hn : n = 6 ∨ n = 7) (x y i : Fin 3) :
    pairSwap hn x y (pos hn i) = pos hn (Equiv.swap x y i) := by
  rw [pairSwap, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne (pos_ne_rev_pos hn i x) (pos_ne_rev_pos hn i y)]
  exact (pos_injective hn).swap_apply x y i

private theorem pairSwap_neg (hn : n = 6 ∨ n = 7) (x y i : Fin 3) :
    pairSwap hn x y (Fin.rev (pos hn i)) = Fin.rev (pos hn (Equiv.swap x y i)) := by
  rw [pairSwap, Equiv.Perm.mul_apply]
  have h := (rev_pos_injective hn).swap_apply x y i
  rw [h]
  exact Equiv.swap_apply_of_ne_of_ne (rev_pos_ne_pos hn _ x) (rev_pos_ne_pos hn _ y)

private theorem mid_ne_pos (hn : n = 6 ∨ n = 7) {a : Fin n} (h1 : 3 ≤ a.val) (i : Fin 3) :
    a ≠ pos hn i := by
  intro h
  have := congrArg Fin.val h
  have hi := i.isLt
  simp only [pos] at this
  omega

private theorem mid_ne_rev_pos (hn : n = 6 ∨ n = 7) {a : Fin n} (h2 : a.val + 3 < n)
    (i : Fin 3) : a ≠ Fin.rev (pos hn i) := by
  intro h
  have := congrArg Fin.val h
  have hi := i.isLt
  simp only [pos, Fin.val_rev] at this
  omega

private theorem pairSwap_mid (hn : n = 6 ∨ n = 7) (x y : Fin 3) {a : Fin n} (h1 : 3 ≤ a.val)
    (h2 : a.val + 3 < n) : pairSwap hn x y a = a := by
  have e1 : Equiv.swap (Fin.rev (pos hn x)) (Fin.rev (pos hn y)) a = a :=
    Equiv.swap_apply_of_ne_of_ne (mid_ne_rev_pos hn h2 x) (mid_ne_rev_pos hn h2 y)
  have e2 : Equiv.swap (pos hn x) (pos hn y) a = a :=
    Equiv.swap_apply_of_ne_of_ne (mid_ne_pos hn h1 x) (mid_ne_pos hn h1 y)
  rw [pairSwap, Equiv.Perm.mul_apply, e1, e2]

private theorem pairSwap_rev (hn : n = 6 ∨ n = 7) (x y : Fin 3) (a : Fin n) :
    pairSwap hn x y (Fin.rev a) = Fin.rev (pairSwap hn x y a) := by
  rcases pos_cases hn a with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨h1, h2⟩
  · rw [pairSwap_pos, pairSwap_neg]
  · rw [Fin.rev_rev, pairSwap_pos, pairSwap_neg, Fin.rev_rev]
  · have h1' : 3 ≤ (Fin.rev a).val := by simp only [Fin.val_rev]; omega
    have h2' : (Fin.rev a).val + 3 < n := by simp only [Fin.val_rev]; omega
    rw [pairSwap_mid hn x y h1' h2', pairSwap_mid hn x y h1 h2]

private theorem sign_pairSwap (hn : n = 6 ∨ n = 7) {x y : Fin 3} (h : x ≠ y) :
    Equiv.Perm.sign (pairSwap hn x y) = 1 := by
  rw [pairSwap, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap ((pos_injective hn).ne h),
    Equiv.Perm.sign_swap ((rev_pos_injective hn).ne h)]
  decide

private theorem wt_pairSwap (hn : n = 6 ∨ n = 7) (x y : Fin 3) (v : Fin 3 → ZMod 3)
    (a : Fin n) : wt n (fun i => v (Equiv.swap x y i)) (pairSwap hn x y a) = wt n v a := by
  rcases pos_cases hn a with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨h1, h2⟩
  · simp only [pairSwap_pos, wt_pos, Equiv.swap_apply_self]
  · simp only [pairSwap_neg, wt_neg, Equiv.swap_apply_self]
  · rw [pairSwap_mid hn x y h1 h2, wt_eq_zero_of_mid _ h1 h2, wt_eq_zero_of_mid _ h1 h2]

private theorem exists_realizes_swap (hn : n = 6 ∨ n = 7) (x y : Fin 3) (hxy : x ≠ y) :
    ∃ g : SU σ n, Realizes (c₀ ζ hn) g fun v i => v (Equiv.swap x y i) := by
  have hsign : (((Equiv.Perm.sign (pairSwap hn x y) : ℤˣ) : ℤ) : L) = 1 := by
    simp [sign_pairSwap hn hxy]
  have hmem : permGL L n (pairSwap hn x y) * diagGL L n 1 ∈ SU σ n :=
    permGL_mul_diagGL_mem_SU (pairSwap hn x y) (pairSwap_rev hn x y) 1 (by simp)
      (by simp [hsign])
  exact ⟨⟨_, hmem⟩, realizes_of_perm_diag ζ hn _ (pairSwap hn x y) 1 rfl _
    fun v a => wt_pairSwap hn x y v a⟩

private def negSwap (hn : n = 6 ∨ n = 7) (j : Fin 3) : Equiv.Perm (Fin n) :=
  Equiv.swap (pos hn j) (Fin.rev (pos hn j))

private theorem negSwap_pos (hn : n = 6 ∨ n = 7) (j i : Fin 3) :
    negSwap hn j (pos hn i) = if i = j then Fin.rev (pos hn j) else pos hn i := by
  by_cases h : i = j
  · subst h
    simp [negSwap]
  · rw [if_neg h, negSwap, Equiv.swap_apply_of_ne_of_ne]
    · exact fun h' => h ((pos_injective hn) h')
    · exact pos_ne_rev_pos hn i j

private theorem negSwap_neg (hn : n = 6 ∨ n = 7) (j i : Fin 3) :
    negSwap hn j (Fin.rev (pos hn i)) = if i = j then pos hn j else Fin.rev (pos hn i) := by
  by_cases h : i = j
  · subst h
    simp [negSwap]
  · rw [if_neg h, negSwap, Equiv.swap_apply_of_ne_of_ne]
    · exact rev_pos_ne_pos hn i j
    · exact fun h' => h ((pos_injective hn) (Fin.rev_injective h'))

private theorem negSwap_mid (hn : n = 6 ∨ n = 7) (j : Fin 3) {a : Fin n} (h1 : 3 ≤ a.val)
    (h2 : a.val + 3 < n) : negSwap hn j a = a :=
  Equiv.swap_apply_of_ne_of_ne (mid_ne_pos hn h1 j) (mid_ne_rev_pos hn h2 j)

private theorem negSwap_rev (hn : n = 6 ∨ n = 7) (j : Fin 3) (a : Fin n) :
    negSwap hn j (Fin.rev a) = Fin.rev (negSwap hn j a) := by
  rcases pos_cases hn a with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨h1, h2⟩
  · rw [negSwap_pos, negSwap_neg]
    split_ifs <;> simp
  · rw [Fin.rev_rev, negSwap_pos, negSwap_neg]
    split_ifs <;> simp
  · have h1' : 3 ≤ (Fin.rev a).val := by simp only [Fin.val_rev]; omega
    have h2' : (Fin.rev a).val + 3 < n := by simp only [Fin.val_rev]; omega
    rw [negSwap_mid hn j h1' h2', negSwap_mid hn j h1 h2]

private theorem sign_negSwap (hn : n = 6 ∨ n = 7) (j : Fin 3) :
    Equiv.Perm.sign (negSwap hn j) = -1 :=
  Equiv.Perm.sign_swap (pos_ne_rev_pos hn j j)

private theorem wt_negSwap (hn : n = 6 ∨ n = 7) (j : Fin 3) (v : Fin 3 → ZMod 3)
    (a : Fin n) :
    wt n (fun i => if i = j then -v i else v i) (negSwap hn j a) = wt n v a := by
  rcases pos_cases hn a with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨h1, h2⟩
  · by_cases h : i = j
    · subst h
      simp [negSwap_pos, wt_neg, wt_pos]
    · simp [negSwap_pos, h, wt_pos]
  · by_cases h : i = j
    · subst h
      simp [negSwap_neg, wt_neg, wt_pos]
    · simp [negSwap_neg, h, wt_neg]
  · rw [negSwap_mid hn j h1 h2, wt_eq_zero_of_mid _ h1 h2, wt_eq_zero_of_mid _ h1 h2]

private theorem exists_realizes_neg (htr : ∃ c : L, c ≠ 0 ∧ σ c = -c) (hn : n = 6 ∨ n = 7)
    (j : Fin 3) :
    ∃ g : SU σ n, Realizes (c₀ ζ hn) g fun v i => if i = j then -v i else v i := by
  classical
  obtain ⟨c, hc0, hcσ⟩ := htr
  let lam : Lˣ := Units.mk0 c hc0
  let mu : Lˣ := -lam⁻¹
  let m : Fin n → Lˣ := fun a =>
    if a = pos hn j then lam else if a = Fin.rev (pos hn j) then mu else 1
  have hne : Fin.rev (pos hn j) ≠ pos hn j := rev_pos_ne_pos hn j j
  have hlam : (lam : L) = c := rfl
  have hmu : (mu : L) = -c⁻¹ := by simp [mu, lam]
  have h1 : σ (lam : L) * (mu : L) = 1 := by
    rw [hlam, hmu, hcσ]
    field_simp
  have h2 : σ (mu : L) * (lam : L) = 1 := by
    rw [hlam, hmu, map_neg, map_inv₀, hcσ]
    field_simp
  have hm : ∀ a, σ (m a : L) * (m (Fin.rev a) : L) = 1 := by
    intro a
    by_cases ha : a = pos hn j
    · subst ha
      simp only [m, if_true, if_neg hne, Fin.rev_rev]
      simpa using h1
    · by_cases ha' : a = Fin.rev (pos hn j)
      · subst ha'
        simp only [m, if_neg hne, if_true, Fin.rev_rev]
        simpa using h2
      · have h3 : Fin.rev a ≠ pos hn j := fun h => ha' (by rw [← h, Fin.rev_rev])
        have h4 : Fin.rev a ≠ Fin.rev (pos hn j) := fun h => ha (Fin.rev_injective h)
        simp [m, ha, ha', h3, h4]
  have hprod : ∏ a, (m a : L) = (lam : L) * (mu : L) := by
    rw [Finset.prod_eq_mul (pos hn j) (Fin.rev (pos hn j)) hne.symm]
    · simp [m, hne]
    · intro a _ ha
      simp [m, ha.1, ha.2]
    · intro h
      exact absurd (Finset.mem_univ _) h
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hlm : (lam : L) * (mu : L) = -1 := by
    rw [hlam, hmu]
    field_simp
  have hmem : permGL L n (negSwap hn j) * diagGL L n m ∈ SU σ n :=
    permGL_mul_diagGL_mem_SU (negSwap hn j) (negSwap_rev hn j) m hm (by
      rw [hprod, hlm, sign_negSwap]
      simp)
  exact ⟨⟨_, hmem⟩, realizes_of_perm_diag ζ hn _ (negSwap hn j) m rfl _
    fun v a => wt_negSwap hn j v a⟩

theorem exists_conj_c₀ (htr : ∃ c : L, c ≠ 0 ∧ σ c = -c) (hn : n = 6 ∨ n = 7)
    (τ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3) (hε : ∀ i, ε i ≠ 0) :
    ∃ m : SU σ n, ∀ v : Multiplicative (Fin 3 → ZMod 3),
      m * c₀ ζ hn v * m⁻¹ =
        c₀ ζ hn (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd v (τ i)) :=
  exists_conj_signedPerm (c := c₀ ζ hn) (fun x y hxy => exists_realizes_swap ζ hn x y hxy)
    (fun j => exists_realizes_neg ζ htr hn j) τ ε hε

end Realizers

end CFSG.ClassicalGroups.SUnThreeLocal
