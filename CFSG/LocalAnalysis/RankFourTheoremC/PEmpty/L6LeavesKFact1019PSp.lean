module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact1019Hom
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact1019PSL
public import CFSG.Open.StatedDefs
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact1019

open Matrix CFSG.Open

section PSp

variable {n : ℕ} {F : Type} [Field F]

@[expose] def symS (x : Fin 4 → F) : Matrix (Fin n) (Fin n) F := fun i j =>
  if i.val = 0 ∧ j.val = 0 then x 0 else if i.val = 1 ∧ j.val = 1 then x 1 else
    if (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) then x 2 else
      if i.val = 2 ∧ j.val = 2 then x 3 else 0

theorem symS_transpose (x : Fin 4 → F) : (symS (n := n) x)ᵀ = symS x := by
  ext i j
  simp only [Matrix.transpose_apply, symS]
  split_ifs <;> first | rfl | (exfalso; omega) | simp_all

theorem symS_add (x y : Fin 4 → F) : symS (n := n) (x + y) = symS x + symS y := by
  ext i j
  simp only [symS, Pi.add_apply, Matrix.add_apply]
  split_ifs <;> simp

@[expose] def uGL (S : Matrix (Fin n) (Fin n) F) : GL (Fin n ⊕ Fin n) F :=
  ⟨Matrix.fromBlocks 1 S 0 1, Matrix.fromBlocks 1 (-S) 0 1,
    by simp [Matrix.fromBlocks_multiply], by simp [Matrix.fromBlocks_multiply]⟩

theorem uGL_mem {S : Matrix (Fin n) (Fin n) F} (hS : Sᵀ = S) : uGL S ∈ StatedSp n F := by
  apply Subgroup.subset_closure
  show (Matrix.fromBlocks 1 S 0 1)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * Matrix.fromBlocks 1 S 0 1 =
    Matrix.fromBlocks 0 1 (-1) 0
  simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, hS]

theorem uGL_add (S T : Matrix (Fin n) (Fin n) F) : uGL (S + T) = uGL S * uGL T := by
  apply Units.ext
  change Matrix.fromBlocks 1 (S + T) 0 1 = Matrix.fromBlocks 1 S 0 1 * Matrix.fromBlocks 1 T 0 1
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, zero_add,
    add_zero, add_comm S T]

@[expose] def sgnVec (i : Fin n) : F := if i.val = 0 then -1 else 1

@[expose] def Tm : Matrix (Fin n) (Fin n) F := Matrix.diagonal (sgnVec (n := n) (F := F))

theorem Tm_mul_self : Tm (n := n) (F := F) * Tm = 1 := by
  unfold Tm
  rw [Matrix.diagonal_mul_diagonal]
  have h1 : (fun i : Fin n => sgnVec (n := n) (F := F) i * sgnVec (n := n) (F := F) i) =
      fun _ => 1 := by
    funext i
    unfold sgnVec
    split_ifs <;> norm_num
  rw [h1]
  simp

theorem Tm_transpose : (Tm (n := n) (F := F))ᵀ = Tm := by
  unfold Tm
  rw [Matrix.diagonal_transpose]

@[expose] def tGL : GL (Fin n ⊕ Fin n) F :=
  ⟨Matrix.fromBlocks Tm 0 0 Tm, Matrix.fromBlocks Tm 0 0 Tm,
    by simp [Matrix.fromBlocks_multiply, Tm_mul_self],
    by simp [Matrix.fromBlocks_multiply, Tm_mul_self]⟩

theorem tGL_mem : tGL (n := n) (F := F) ∈ StatedSp n F := by
  apply Subgroup.subset_closure
  show (Matrix.fromBlocks Tm 0 0 Tm)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 *
      Matrix.fromBlocks Tm 0 0 Tm = Matrix.fromBlocks 0 1 (-1) 0
  simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Tm_transpose, Tm_mul_self]

theorem sgnVec_mul_symS (x : Fin 4 → F) (i j : Fin n) :
    sgnVec (n := n) (F := F) i * symS x i j = symS x i j * sgnVec (n := n) (F := F) j := by
  simp only [symS, sgnVec]
  split_ifs <;> first | (exfalso; omega) | ring1 | simp

theorem tGL_mul_uGL (x : Fin 4 → F) :
    tGL (n := n) (F := F) * uGL (symS x) = uGL (symS x) * tGL := by
  apply Units.ext
  change Matrix.fromBlocks Tm 0 0 Tm * Matrix.fromBlocks 1 (symS x) 0 1 =
    Matrix.fromBlocks 1 (symS x) 0 1 * Matrix.fromBlocks Tm 0 0 Tm
  have hTS : Tm (n := n) (F := F) * symS (n := n) x = symS (n := n) x * Tm (n := n) (F := F) := by
    ext i j
    simp only [Tm, Matrix.diagonal_mul, Matrix.mul_diagonal]
    exact sgnVec_mul_symS x i j
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, zero_add,
    add_zero, hTS]

@[expose] def fSpH (p : ℕ) [CharP F p] : Multiplicative (Fin 4 → ZMod p) →* StatedSp n F :=
  MonoidHom.mk' (fun x => ⟨uGL (symS (coeffs (F := F) p x)),
      uGL_mem (symS_transpose _)⟩) fun x y => by
    apply Subtype.ext
    change uGL (symS (coeffs (F := F) p (x * y))) =
      uGL (symS (coeffs (F := F) p x)) * uGL (symS (coeffs (F := F) p y))
    rw [← uGL_add, ← symS_add]
    congr 2
    funext k
    simp [coeffs]

@[expose] def fSp (p : ℕ) [CharP F p] :
    Multiplicative (Fin 4 → ZMod p) →* StatedProj (StatedSp n F) :=
  (QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) F).subgroupOf (StatedSp n F))).comp
    (fSpH p)

theorem offdiag_of_scalar_gl {c : Fˣ} {g : GL (Fin n ⊕ Fin n) F}
    (hg : Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c = g) {i j : Fin n ⊕ Fin n}
    (hij : i ≠ j) : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) i j = 0 := by
  rw [← hg, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_ne _ hij]

theorem diag_of_scalar_gl {c : Fˣ} {g : GL (Fin n ⊕ Fin n) F}
    (hg : Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c = g) (i : Fin n ⊕ Fin n) :
    (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) i i = (c : F) := by
  rw [← hg, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq]

theorem fSp_injective (p : ℕ) [CharP F p] [Fact p.Prime] (hn : 3 ≤ n) :
    Function.Injective (fSp (n := n) (F := F) p) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : fSpH (n := n) (F := F) p x ∈ (StatedScalars (Fin n ⊕ Fin n) F).subgroupOf
      (StatedSp n F) := (QuotientGroup.eq_one_iff _).1 hx
  have h2 : ((fSpH (n := n) (F := F) p x : StatedSp n F) : GL (Fin n ⊕ Fin n) F) ∈
      StatedScalars (Fin n ⊕ Fin n) F := Subgroup.mem_subgroupOf.1 h1
  have h3 : ((fSpH (n := n) (F := F) p x : StatedSp n F) : GL (Fin n ⊕ Fin n) F) ∈
      (Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n)).range := h2
  obtain ⟨c, hc⟩ := h3
  have hS : ∀ a b : Fin n, symS (n := n) (coeffs (F := F) p x) a b = 0 := by
    intro a b
    have h := offdiag_of_scalar_gl hc (i := Sum.inl a) (j := Sum.inr b) Sum.inl_ne_inr
    simpa [uGL, fSpH] using h
  have hc0 : coeffs (F := F) p x 0 = 0 := by
    have h := hS ⟨0, by omega⟩ ⟨0, by omega⟩
    simpa [symS] using h
  have hc1 : coeffs (F := F) p x 1 = 0 := by
    have h := hS ⟨1, by omega⟩ ⟨1, by omega⟩
    simpa [symS] using h
  have hc2 : coeffs (F := F) p x 2 = 0 := by
    have h := hS ⟨1, by omega⟩ ⟨2, by omega⟩
    simpa [symS] using h
  have hc3 : coeffs (F := F) p x 3 = 0 := by
    have h := hS ⟨2, by omega⟩ ⟨2, by omega⟩
    simpa [symS] using h
  have hx1 : Multiplicative.toAdd x = 0 := funext fun k => by
    have hk : coeffs (F := F) p x k = 0 := by
      fin_cases k
      · exact hc0
      · exact hc1
      · exact hc2
      · exact hc3
    exact (map_eq_zero_iff (castF (F := F) p) (castF (F := F) p).injective).1 hk
  exact Multiplicative.toAdd.injective (hx1.trans toAdd_one.symm)

@[expose] def tSp : StatedSp n F := ⟨tGL, tGL_mem⟩

@[expose] def tPSp : StatedProj (StatedSp n F) := QuotientGroup.mk tSp

theorem tSp_sq : tSp (n := n) (F := F) * tSp = 1 := by
  apply Subtype.ext
  apply Units.ext
  change Matrix.fromBlocks Tm 0 0 Tm * Matrix.fromBlocks Tm 0 0 Tm = 1
  simp [Matrix.fromBlocks_multiply, Tm_mul_self]

theorem tPSp_sq : tPSp (n := n) (F := F) ^ 2 = 1 := by
  rw [tPSp, ← QuotientGroup.mk_pow, sq, tSp_sq, QuotientGroup.mk_one]

theorem tPSp_ne_one (p : ℕ) [CharP F p] [hp : Fact p.Prime] (hp2 : p ≠ 2) (hn : 3 ≤ n) :
    tPSp (n := n) (F := F) ≠ 1 := by
  intro h
  have h1 : tSp (n := n) (F := F) ∈ (StatedScalars (Fin n ⊕ Fin n) F).subgroupOf
      (StatedSp n F) := (QuotientGroup.eq_one_iff _).1 h
  have h2 : (tGL (n := n) (F := F)) ∈ StatedScalars (Fin n ⊕ Fin n) F :=
    Subgroup.mem_subgroupOf.1 h1
  have h3 : (tGL (n := n) (F := F)) ∈ (Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n)).range :=
    h2
  obtain ⟨c, hc⟩ := h3
  have e0 := diag_of_scalar_gl hc (Sum.inl ⟨0, by omega⟩)
  have e1 := diag_of_scalar_gl hc (Sum.inl ⟨1, by omega⟩)
  have t0 : (tGL (n := n) (F := F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
      (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩) = -1 := by
    simp [tGL, Tm, sgnVec]
  have t1 : (tGL (n := n) (F := F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
      (Sum.inl ⟨1, by omega⟩) (Sum.inl ⟨1, by omega⟩) = 1 := by
    simp [tGL, Tm, sgnVec]
  have h4 : (-1 : F) = 1 := t0.symm.trans (e0.trans (e1.symm.trans t1))
  have h2' : ((2 : ℕ) : F) = 0 := by
    push_cast
    linear_combination -h4
  have hp2' : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).1 h2'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 hp2')

theorem tPSp_comm (p : ℕ) [CharP F p] (x : Multiplicative (Fin 4 → ZMod p)) :
    tPSp (n := n) (F := F) * fSp (n := n) (F := F) p x =
      fSp (n := n) (F := F) p x * tPSp := by
  change QuotientGroup.mk tSp * QuotientGroup.mk (fSpH (n := n) (F := F) p x) =
    QuotientGroup.mk (fSpH (n := n) (F := F) p x) * QuotientGroup.mk tSp
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  change tGL * uGL (symS (coeffs (F := F) p x)) = uGL (symS (coeffs (F := F) p x)) * tGL
  exact tGL_mul_uGL _

theorem exists_involution_statedSp (p : ℕ) [CharP F p] [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hn : 3 ≤ n) :
    ∃ t : StatedProj (StatedSp n F), orderOf t = 2 ∧
      ∃ E : Subgroup (StatedProj (StatedSp n F)),
        E ≤ Subgroup.centralizer {t} ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 4 :=
  ⟨tPSp, orderOf_eq_prime tPSp_sq (tPSp_ne_one p hp2 hn),
    exists_subgroup_of_hom (fSp (n := n) (F := F) p) (fSp_injective p hn) tPSp (tPSp_comm p)⟩

end PSp

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact1019
