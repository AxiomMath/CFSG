module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA6UWittChar
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def hermT (h : UnitaryFieldData p f K) (X : Matrix (Fin 6) (Fin 6) K) :
    Matrix (Fin 6) (Fin 6) K :=
  (X.map h.bar)ᵀ

theorem hermT_mul (h : UnitaryFieldData p f K) (X Y : Matrix (Fin 6) (Fin 6) K) :
    hermT h (X * Y) = hermT h Y * hermT h X := by
  unfold hermT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem hermT_one (h : UnitaryFieldData p f K) : hermT h (1 : Matrix (Fin 6) (Fin 6) K) = 1 := by
  unfold hermT
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

theorem hermT_diag (h : UnitaryFieldData p f K) (d : Fin 6 → K) :
    hermT h (Matrix.diagonal d) = Matrix.diagonal (fun i => h.bar (d i)) := by
  unfold hermT
  rw [Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose]

@[expose] noncomputable def gramT (h : UnitaryFieldData p f K) (T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K :=
  hermT h (T : Matrix (Fin 6) (Fin 6) K) * (T : Matrix (Fin 6) (Fin 6) K)

theorem gram_invariant (h : UnitaryFieldData p f K) (T g : GL (Fin 6) K)
    (hg : hermT h (g : Matrix (Fin 6) (Fin 6) K) * (g : Matrix (Fin 6) (Fin 6) K) = 1) :
    hermT h ((T⁻¹ * g * T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * gramT h T *
      ((T⁻¹ * g * T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = gramT h T := by
  set t := (T : Matrix (Fin 6) (Fin 6) K) with ht
  set ti := ((T⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) with hti
  set gm := (g : Matrix (Fin 6) (Fin 6) K) with hgm
  have htti : t * ti = 1 := Units.mul_inv T
  have hCA : hermT h ti * hermT h t = 1 := by
    rw [← hermT_mul, htti, hermT_one]
  have hD : ((T⁻¹ * g * T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = ti * gm * t := by
    rw [Units.val_mul, Units.val_mul]
  rw [hD, gramT, hermT_mul, hermT_mul]
  calc hermT h t * (hermT h gm * hermT h ti) * (hermT h t * t) * (ti * gm * t)
      = hermT h t * hermT h gm * (hermT h ti * hermT h t) * t * (ti * gm * t) := by
        simp only [Matrix.mul_assoc]
    _ = hermT h t * hermT h gm * t * (ti * gm * t) := by rw [hCA, Matrix.mul_one]
    _ = hermT h t * hermT h gm * (t * ti) * gm * t := by simp only [Matrix.mul_assoc]
    _ = hermT h t * hermT h gm * gm * t := by rw [htti, Matrix.mul_one]
    _ = hermT h t * (hermT h gm * gm) * t := by simp only [Matrix.mul_assoc]
    _ = hermT h t * t := by rw [hg, Matrix.mul_one]

theorem gram_entry_rel (h : UnitaryFieldData p f K) (T g : GL (Fin 6) K)
    (hg : hermT h (g : Matrix (Fin 6) (Fin 6) K) * (g : Matrix (Fin 6) (Fin 6) K) = 1)
    (hD : ((T⁻¹ * g * T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      Matrix.diagonal (chT T g)) (i j : Fin 6) :
    h.bar (chT T g i) * gramT h T i j * chT T g j = gramT h T i j := by
  have key := gram_invariant h T g hg
  rw [hD, hermT_diag] at key
  have := congrFun (congrFun key i) j
  simpa [Matrix.diagonal_mul, Matrix.mul_diagonal] using this

theorem exists_gram_ne (h : UnitaryFieldData p f K) (T : GL (Fin 6) K) (i : Fin 6) :
    ∃ j, gramT h T i j ≠ 0 := by
  by_contra hc
  push Not at hc
  have hdet : (gramT h T).det = 0 := Matrix.det_eq_zero_of_row_eq_zero i hc
  have hT : (T : Matrix (Fin 6) (Fin 6) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit T)).ne_zero
  have hdet' : (gramT h T).det = h.bar (T : Matrix (Fin 6) (Fin 6) K).det *
      (T : Matrix (Fin 6) (Fin 6) K).det := by
    unfold gramT hermT
    rw [Matrix.det_mul, Matrix.det_transpose]
    congr 1
    exact (RingHom.map_det h.bar _).symm
  rw [hdet'] at hdet
  rcases mul_eq_zero.mp hdet with h1 | h1
  · exact (map_ne_zero h.bar).mpr hT h1
  · exact hT h1

@[expose] def TrivC (P : Subgroup (GL (Fin 6) K)) (T : GL (Fin 6) K) (i : Fin 6) : Prop :=
  ∀ g ∈ P, chT T g i = 1

@[expose] def SameC (P : Subgroup (GL (Fin 6) K)) (T : GL (Fin 6) K) (i j : Fin 6) : Prop :=
  ∀ g ∈ P, chT T g i = chT T g j

@[expose] def InvC (P : Subgroup (GL (Fin 6) K)) (T : GL (Fin 6) K) (i j : Fin 6) : Prop :=
  ∀ g ∈ P, chT T g i * chT T g j = 1

theorem sameC_symm {P : Subgroup (GL (Fin 6) K)} {T : GL (Fin 6) K} {i j : Fin 6}
    (hI : SameC P T i j) : SameC P T j i :=
  fun g hg => (hI g hg).symm

theorem invC_symm {P : Subgroup (GL (Fin 6) K)} {T : GL (Fin 6) K} {i j : Fin 6}
    (hI : InvC P T i j) : InvC P T j i :=
  fun g hg => by rw [mul_comm]; exact hI g hg

theorem invC_of_gram (h : UnitaryFieldData p f K) (hbar : ∀ x : K, x ^ 3 = 1 → h.bar x = x)
    (P : Subgroup (GL (Fin 6) K)) (T : GL (Fin 6) K)
    (hdiag : ∀ g ∈ P, ∀ i j, i ≠ j →
      ((T⁻¹ * g * T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j = 0)
    (hgram : ∀ g ∈ P, hermT h (g : Matrix (Fin 6) (Fin 6) K) * (g : Matrix (Fin 6) (Fin 6) K) = 1)
    (hpow : ∀ g ∈ P, g ^ 3 = 1) {i j : Fin 6} (hij : gramT h T i j ≠ 0) :
    InvC P T i j := by
  intro g hg
  have hrel := gram_entry_rel h T g (hgram g hg) (conj_eq_diagonal P T hdiag hg) i j
  have hcube : chT T g i ^ 3 = 1 := by
    rw [← chT_pow P T hdiag hg i 3, hpow g hg, chT_one]
  rw [hbar _ hcube] at hrel
  have h0 : (chT T g i * chT T g j - 1) * gramT h T i j = 0 := by
    linear_combination hrel
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd h1 hij

theorem chT_ne_zero (P : Subgroup (GL (Fin 6) K)) (T : GL (Fin 6) K)
    (hdiag : ∀ g ∈ P, ∀ i j, i ≠ j →
      ((T⁻¹ * g * T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j = 0)
    (hpow : ∀ g ∈ P, g ^ 3 = 1) {g : GL (Fin 6) K} (hg : g ∈ P) (i : Fin 6) :
    chT T g i ≠ 0 := by
  intro h0
  have hcube : chT T g i ^ 3 = 1 := by
    rw [← chT_pow P T hdiag hg i 3, hpow g hg, chT_one]
  rw [h0] at hcube
  norm_num at hcube

theorem pair_cover_false [Finite K] (P : Subgroup (GL (Fin 6) K)) (T : GL (Fin 6) K)
    (hdiag : ∀ g ∈ P, ∀ i j, i ≠ j →
      ((T⁻¹ * g * T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j = 0)
    (hcard : Nat.card P = 27) (hpow : ∀ g ∈ P, g ^ 3 = 1) (a b : Fin 6)
    (hcover : ∀ i : Fin 6, TrivC P T i ∨ SameC P T i a ∨ InvC P T i a ∨
      SameC P T i b ∨ InvC P T i b) : False := by
  classical
  haveI : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fintype P := Fintype.ofFinite P
  have hPcard : Fintype.card P = 27 := by rw [← Nat.card_eq_fintype_card, hcard]
  let M : Finset K := (Polynomial.nthRoots 3 (1 : K)).toFinset
  have hMcard : M.card ≤ 3 := by
    calc M.card ≤ Multiset.card (Polynomial.nthRoots 3 (1 : K)) := Multiset.toFinset_card_le _
      _ ≤ 3 := Polynomial.card_nthRoots 3 1
  have hmemM : ∀ x : K, x ^ 3 = 1 → x ∈ M := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num)]
    exact hx
  have hmaps : ∀ x ∈ (Finset.univ : Finset P),
      ((fun y : P => (chT T y a, chT T y b)) x) ∈ M ×ˢ M := by
    intro x _
    rw [Finset.mem_product]
    constructor
    · apply hmemM
      rw [← chT_pow P T hdiag x.2 a 3, hpow _ x.2, chT_one]
    · apply hmemM
      rw [← chT_pow P T hdiag x.2 b 3, hpow _ x.2, chT_one]
  have hlt : (M ×ˢ M).card < (Finset.univ : Finset P).card := by
    rw [Finset.card_product, Finset.card_univ, hPcard]
    have : M.card * M.card ≤ 9 := Nat.mul_le_mul hMcard hMcard
    omega
  obtain ⟨x, -, y, -, hxy, hfxy⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  simp only [Prod.mk.injEq] at hfxy
  obtain ⟨hfa, hfb⟩ := hfxy
  have hzP : (x : GL (Fin 6) K)⁻¹ * (y : GL (Fin 6) K) ∈ P := P.mul_mem (P.inv_mem x.2) y.2
  have hz1 : (x : GL (Fin 6) K)⁻¹ * (y : GL (Fin 6) K) ≠ 1 := by
    intro h1
    exact hxy (Subtype.ext (inv_mul_eq_one.mp h1))
  have hza : chT T ((x : GL (Fin 6) K)⁻¹ * (y : GL (Fin 6) K)) a = 1 := by
    rw [chT_mul P T hdiag (P.inv_mem x.2) y.2, chT_inv P T hdiag x.2, hfa]
    exact inv_mul_cancel₀ (chT_ne_zero P T hdiag hpow y.2 a)
  have hzb : chT T ((x : GL (Fin 6) K)⁻¹ * (y : GL (Fin 6) K)) b = 1 := by
    rw [chT_mul P T hdiag (P.inv_mem x.2) y.2, chT_inv P T hdiag x.2, hfb]
    exact inv_mul_cancel₀ (chT_ne_zero P T hdiag hpow y.2 b)
  have hall : ∀ i, chT T ((x : GL (Fin 6) K)⁻¹ * (y : GL (Fin 6) K)) i = 1 := by
    intro i
    rcases hcover i with h1 | h2 | h3 | h4 | h5
    · exact h1 _ hzP
    · rw [h2 _ hzP, hza]
    · have := h3 _ hzP
      rw [hza, mul_one] at this
      exact this
    · rw [h4 _ hzP, hzb]
    · have := h5 _ hzP
      rw [hzb, mul_one] at this
      exact this
  exact hz1 (eq_one_of_chT P T hdiag hzP hall)

theorem exists_not_trivC (P : Subgroup (GL (Fin 6) K)) (T : GL (Fin 6) K)
    (hdiag : ∀ g ∈ P, ∀ i j, i ≠ j →
      ((T⁻¹ * g * T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j = 0)
    (hcard : Nat.card P = 27) : ∃ i, ¬ TrivC P T i := by
  by_contra hcon
  push Not at hcon
  have hbot : P = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    exact eq_one_of_chT P T hdiag hg (fun i => hcon i g hg)
  rw [hbot, Subgroup.card_bot] at hcard
  norm_num at hcard

theorem select3 [Finite K] (h : UnitaryFieldData p f K) (hbar : ∀ x : K, x ^ 3 = 1 → h.bar x = x)
    (P : Subgroup (GL (Fin 6) K)) (T : GL (Fin 6) K)
    (hdiag : ∀ g ∈ P, ∀ i j, i ≠ j →
      ((T⁻¹ * g * T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j = 0)
    (hcard : Nat.card P = 27) (hpow : ∀ g ∈ P, g ^ 3 = 1)
    (hgram : ∀ g ∈ P, hermT h (g : Matrix (Fin 6) (Fin 6) K) * (g : Matrix (Fin 6) (Fin 6) K) = 1) :
    ∃ a b : Fin 3 → Fin 6, (∀ k, ¬ TrivC P T (a k)) ∧ (∀ k, InvC P T (b k) (a k)) ∧
      (∀ k l, k ≠ l → ¬ SameC P T (a k) (a l) ∧ ¬ InvC P T (a k) (a l)) ∧
      (∀ k, gramT h T (a k) (b k) ≠ 0) := by
  obtain ⟨i0, hi0⟩ := exists_not_trivC P T hdiag hcard
  obtain ⟨j0, hj0⟩ := exists_gram_ne h T i0
  have hinv0 : InvC P T j0 i0 :=
    invC_symm (invC_of_gram h hbar P T hdiag hgram hpow hj0)
  obtain ⟨i1, hi1⟩ : ∃ i1, ¬ (TrivC P T i1 ∨ SameC P T i1 i0 ∨ InvC P T i1 i0) := by
    by_contra hcon
    push Not at hcon
    exact pair_cover_false P T hdiag hcard hpow i0 i0
      (fun i => by rcases hcon i with h1 | h1 | h1 <;> tauto)
  obtain ⟨n1a, n1b, n1c⟩ : ¬ TrivC P T i1 ∧ ¬ SameC P T i1 i0 ∧ ¬ InvC P T i1 i0 := by
    tauto
  obtain ⟨j1, hj1⟩ := exists_gram_ne h T i1
  have hinv1 : InvC P T j1 i1 :=
    invC_symm (invC_of_gram h hbar P T hdiag hgram hpow hj1)
  obtain ⟨i2, hi2⟩ : ∃ i2, ¬ (TrivC P T i2 ∨ SameC P T i2 i0 ∨ InvC P T i2 i0 ∨
      SameC P T i2 i1 ∨ InvC P T i2 i1) := by
    by_contra hcon
    push Not at hcon
    exact pair_cover_false P T hdiag hcard hpow i0 i1
      (fun i => by rcases hcon i with h1 | h1 | h1 | h1 | h1 <;> tauto)
  obtain ⟨n2a, n2b, n2c, n2d, n2e⟩ : ¬ TrivC P T i2 ∧ ¬ SameC P T i2 i0 ∧ ¬ InvC P T i2 i0 ∧
      ¬ SameC P T i2 i1 ∧ ¬ InvC P T i2 i1 := by
    tauto
  obtain ⟨j2, hj2⟩ := exists_gram_ne h T i2
  have hinv2 : InvC P T j2 i2 :=
    invC_symm (invC_of_gram h hbar P T hdiag hgram hpow hj2)
  refine ⟨![i0, i1, i2], ![j0, j1, j2], ?_, ?_, ?_, ?_⟩
  · intro k
    fin_cases k
    · exact hi0
    · exact n1a
    · exact n2a
  · intro k
    fin_cases k
    · exact hinv0
    · exact hinv1
    · exact hinv2
  · intro k l hkl
    fin_cases k <;> fin_cases l <;> simp only [Fin.isValue, Matrix.cons_val] at hkl ⊢ <;>
      first
      | exact absurd rfl hkl
      | exact ⟨n1b, n1c⟩
      | exact ⟨fun e => n1b (sameC_symm e), fun e => n1c (invC_symm e)⟩
      | exact ⟨n2b, n2c⟩
      | exact ⟨fun e => n2b (sameC_symm e), fun e => n2c (invC_symm e)⟩
      | exact ⟨n2d, n2e⟩
      | exact ⟨fun e => n2d (sameC_symm e), fun e => n2e (invC_symm e)⟩
  · intro k
    fin_cases k
    · exact hj0
    · exact hj1
    · exact hj2

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
