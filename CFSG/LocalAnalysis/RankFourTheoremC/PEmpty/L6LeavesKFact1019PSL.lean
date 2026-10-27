module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact1019Hom

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact1019

open Matrix CFSG.Open

section PSL

variable {n : ℕ} {F : Type} [Field F]

@[expose] def blockN (a : Fin 4 → F) : Matrix (Fin n) (Fin n) F := fun i j =>
  if i.val = 0 ∧ j.val = 2 then a 0 else if i.val = 0 ∧ j.val = 3 then a 1 else
    if i.val = 1 ∧ j.val = 2 then a 2 else if i.val = 1 ∧ j.val = 3 then a 3 else 0

theorem blockN_add (a b : Fin 4 → F) : blockN (n := n) (a + b) = blockN a + blockN b := by
  ext i j
  simp only [blockN, Pi.add_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem blockN_mul_blockN (a b : Fin 4 → F) : blockN (n := n) a * blockN b = 0 := by
  ext i k
  rw [Matrix.mul_apply]
  simp only [blockN, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro m _
  split_ifs <;> first | (exfalso; omega) | simp

theorem blockN_apply_of_le (a : Fin 4 → F) (i j : Fin n) (h : j.val ≤ i.val) :
    blockN a i j = 0 := by
  simp only [blockN]
  split_ifs <;> first | (exfalso; omega) | rfl

theorem det_one_add_blockN (a : Fin 4 → F) : (1 + blockN (n := n) a).det = 1 := by
  have hT : (1 + blockN (n := n) a).IsUpperTriangular := by
    intro i j hji
    have hji' : j.val < i.val := hji
    have hne : i ≠ j := by
      intro h
      subst h
      exact lt_irrefl _ hji'
    rw [Matrix.add_apply, Matrix.one_apply_ne hne, blockN_apply_of_le a i j hji'.le]
    simp
  rw [Matrix.det_of_isUpperTriangular hT]
  simp [blockN_apply_of_le a _ _ le_rfl]

@[expose] def uSL (a : Fin 4 → F) : SpecialLinearGroup (Fin n) F :=
  ⟨1 + blockN a, det_one_add_blockN a⟩

theorem uSL_add (a b : Fin 4 → F) : uSL (n := n) (a + b) = uSL a * uSL b := by
  apply Subtype.ext
  change 1 + blockN (n := n) (a + b) = (1 + blockN a) * (1 + blockN b)
  rw [blockN_add]
  simp only [add_mul, mul_add, one_mul, mul_one, blockN_mul_blockN, add_zero]
  abel

@[expose] def castF (p : ℕ) [CharP F p] : ZMod p →+* F := ZMod.castHom (dvd_refl p) F

@[expose] def coeffs (p : ℕ) [CharP F p] (x : Multiplicative (Fin 4 → ZMod p)) : Fin 4 → F :=
  fun k => castF p (Multiplicative.toAdd x k)

@[expose] def fSL (p : ℕ) [CharP F p] :
    Multiplicative (Fin 4 → ZMod p) →* SpecialLinearGroup (Fin n) F :=
  MonoidHom.mk' (fun x => uSL (coeffs p x)) fun x y => by
    show uSL (coeffs p (x * y)) = uSL (coeffs p x) * uSL (coeffs p y)
    rw [← uSL_add]
    congr 1
    funext k
    simp [coeffs]

@[expose] def fPSL (p : ℕ) [CharP F p] :
    Multiplicative (Fin 4 → ZMod p) →* Matrix.ProjectiveSpecialLinearGroup (Fin n) F :=
  (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F))).comp (fSL p)

theorem offdiag_of_scalar {r : F} {A : Matrix (Fin n) (Fin n) F}
    (hr : Matrix.scalar (Fin n) r = A) {i j : Fin n} (hij : i ≠ j) : A i j = 0 := by
  rw [← hr, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]

theorem fPSL_injective (p : ℕ) [CharP F p] [Fact p.Prime] (hn : 4 ≤ n) :
    Function.Injective (fPSL (n := n) (F := F) p) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : fSL (n := n) (F := F) p x ∈ Subgroup.center (SpecialLinearGroup (Fin n) F) :=
    (QuotientGroup.eq_one_iff _).1 hx
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h1
  have hfx : ((fSL (n := n) (F := F) p x : SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = 1 + blockN (n := n) (coeffs (F := F) p x) := rfl
  have hA : ∀ i j : Fin n, i ≠ j →
      ((fSL (n := n) (F := F) p x : SpecialLinearGroup (Fin n) F) :
        Matrix (Fin n) (Fin n) F) i j = blockN (n := n) (coeffs (F := F) p x) i j := by
    intro i j hij
    rw [hfx, Matrix.add_apply, Matrix.one_apply_ne hij, zero_add]
  have hoff : ∀ i j : Fin n, i ≠ j → blockN (n := n) (coeffs (F := F) p x) i j = 0 :=
    fun i j hij => by
      rw [← hA i j hij]
      exact offdiag_of_scalar hr hij
  have hc0 : coeffs (F := F) p x 0 = 0 := by
    have h := hoff ⟨0, by omega⟩ ⟨2, by omega⟩ (by simp [Fin.ext_iff])
    simpa [blockN] using h
  have hc1 : coeffs (F := F) p x 1 = 0 := by
    have h := hoff ⟨0, by omega⟩ ⟨3, by omega⟩ (by simp [Fin.ext_iff])
    simpa [blockN] using h
  have hc2 : coeffs (F := F) p x 2 = 0 := by
    have h := hoff ⟨1, by omega⟩ ⟨2, by omega⟩ (by simp [Fin.ext_iff])
    simpa [blockN] using h
  have hc3 : coeffs (F := F) p x 3 = 0 := by
    have h := hoff ⟨1, by omega⟩ ⟨3, by omega⟩ (by simp [Fin.ext_iff])
    simpa [blockN] using h
  have hx1 : Multiplicative.toAdd x = 0 := funext fun k => by
    have hk : coeffs (F := F) p x k = 0 := by
      fin_cases k
      · exact hc0
      · exact hc1
      · exact hc2
      · exact hc3
    exact (map_eq_zero_iff (castF (F := F) p) (castF (F := F) p).injective).1 hk
  exact Multiplicative.toAdd.injective (hx1.trans toAdd_one.symm)

@[expose] def signVec (k : Fin n) : F := if k.val < 4 then -1 else 1

theorem det_diagonal_signVec (hn : 4 ≤ n) :
    (Matrix.diagonal (signVec (n := n) (F := F))).det = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 + m := ⟨n - 4, by omega⟩
  rw [Matrix.det_diagonal, Fin.prod_univ_add, Fin.prod_univ_four]
  have h2 : ∏ i : Fin m, (signVec (n := 4 + m) (F := F) (Fin.natAdd 4 i)) = 1 :=
    Finset.prod_eq_one fun i _ => by simp [signVec]
  rw [h2, mul_one]
  simp [signVec]

@[expose] def tSL (hn : 4 ≤ n) : SpecialLinearGroup (Fin n) F :=
  ⟨Matrix.diagonal (signVec (n := n) (F := F)), det_diagonal_signVec hn⟩

theorem tSL_mul_self (hn : 4 ≤ n) : tSL (F := F) hn * tSL hn = 1 := by
  apply Subtype.ext
  have h1 : (fun k : Fin n => signVec (n := n) (F := F) k * signVec (n := n) (F := F) k) =
      fun _ => 1 := by
    funext k
    unfold signVec
    split_ifs <;> norm_num
  change Matrix.diagonal (signVec (n := n) (F := F)) * Matrix.diagonal (signVec (n := n) (F := F)) =
    (1 : Matrix (Fin n) (Fin n) F)
  rw [Matrix.diagonal_mul_diagonal, h1]
  simp

theorem signVec_mul_blockN (a : Fin 4 → F) (i j : Fin n) :
    signVec (n := n) (F := F) i * blockN a i j = blockN a i j * signVec (n := n) (F := F) j := by
  simp only [blockN, signVec]
  split_ifs <;> first | (exfalso; omega) | ring1 | simp

theorem tSL_mul_uSL (hn : 4 ≤ n) (a : Fin 4 → F) : tSL (F := F) hn * uSL a = uSL a * tSL hn := by
  apply Subtype.ext
  change Matrix.diagonal (signVec (n := n) (F := F)) * (1 + blockN a) =
    (1 + blockN a) * Matrix.diagonal (signVec (n := n) (F := F))
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact signVec_mul_blockN a i j

@[expose] def tPSL (hn : 4 ≤ n) : Matrix.ProjectiveSpecialLinearGroup (Fin n) F :=
  QuotientGroup.mk (tSL hn)

theorem tPSL_sq (hn : 4 ≤ n) : tPSL (F := F) hn ^ 2 = 1 := by
  rw [tPSL, ← QuotientGroup.mk_pow, sq, tSL_mul_self hn, QuotientGroup.mk_one]

theorem tPSL_ne_one (p : ℕ) [CharP F p] [hp : Fact p.Prime] (hp2 : p ≠ 2) (hn : 5 ≤ n) :
    tPSL (F := F) (show 4 ≤ n by omega) ≠ 1 := by
  intro h
  have hmem : tSL (F := F) (show 4 ≤ n by omega) ∈
      Subgroup.center (SpecialLinearGroup (Fin n) F) :=
    (QuotientGroup.eq_one_iff _).1 h
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hmem
  have e0 : r = signVec (n := n) (F := F) ⟨0, by omega⟩ := by
    have h0 := congrArg (fun B : Matrix (Fin n) (Fin n) F => B ⟨0, by omega⟩ ⟨0, by omega⟩) hr
    simpa [tSL, Matrix.scalar_apply] using h0
  have e4 : r = signVec (n := n) (F := F) ⟨4, by omega⟩ := by
    have h4 := congrArg (fun B : Matrix (Fin n) (Fin n) F => B ⟨4, by omega⟩ ⟨4, by omega⟩) hr
    simpa [tSL, Matrix.scalar_apply] using h4
  have s0 : signVec (n := n) (F := F) ⟨0, by omega⟩ = -1 := by simp [signVec]
  have s4 : signVec (n := n) (F := F) ⟨4, by omega⟩ = 1 := by simp [signVec]
  have h1 : (-1 : F) = 1 := s0.symm.trans (e0.symm.trans (e4.trans s4))
  have h2 : ((2 : ℕ) : F) = 0 := by
    push_cast
    linear_combination -h1
  have hp2' : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).1 h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 hp2')

theorem tPSL_comm (p : ℕ) [CharP F p] (hn : 4 ≤ n)
    (x : Multiplicative (Fin 4 → ZMod p)) :
    tPSL (F := F) hn * fPSL (n := n) (F := F) p x = fPSL (n := n) (F := F) p x * tPSL hn := by
  change QuotientGroup.mk (tSL hn) * QuotientGroup.mk (fSL (n := n) (F := F) p x) =
    QuotientGroup.mk (fSL (n := n) (F := F) p x) * QuotientGroup.mk (tSL hn)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact tSL_mul_uSL hn (coeffs (F := F) p x)

theorem exists_involution_pslProj (p : ℕ) [CharP F p] [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {n : ℕ} (hn : 5 ≤ n) :
    ∃ t : Matrix.ProjectiveSpecialLinearGroup (Fin n) F, orderOf t = 2 ∧
      ∃ E : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) F),
        E ≤ Subgroup.centralizer {t} ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 4 := by
  have h4 : 4 ≤ n := by omega
  refine ⟨tPSL (F := F) h4, orderOf_eq_prime (tPSL_sq h4) (tPSL_ne_one p hp2 hn), ?_⟩
  exact exists_subgroup_of_hom (fPSL (n := n) (F := F) p) (fPSL_injective p h4) (tPSL h4)
    (tPSL_comm p h4)

end PSL

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact1019
