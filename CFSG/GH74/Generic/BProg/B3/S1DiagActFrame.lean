module

public import CFSG.GH74.Filter.Small.Eigenbasis
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.GH74.Generic.BProg.B3.S1DiagActFrame

open Matrix Module

variable {F : Type} [Field F]

theorem toLin'_gl_mul (x y : GL (Fin 4) F) :
    Matrix.toLin' ((x * y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.toLin' (x : Matrix (Fin 4) (Fin 4) F) * Matrix.toLin' (y : Matrix (Fin 4) (Fin 4) F) := by
  rw [Units.val_mul, Matrix.toLin'_mul]
  rfl

@[expose] def cnt (s : Fin 4 → Bool) : ℕ := (Finset.univ.filter fun j => s j = true).card

theorem card_even : Nat.card {s : Fin 4 → Bool // cnt s % 2 = 0} = 8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem exists_perm : ∀ s : Fin 4 → Bool, cnt s = 2 →
    ∃ τ : Equiv.Perm (Fin 4), s (τ 0) = true ∧ s (τ 1) = true ∧ s (τ 2) = false ∧ s (τ 3) = false := by
  unfold cnt
  decide

theorem even_of_prod (hneg : (-1 : F) ≠ 1) (s : Fin 4 → Bool) (ν : Fin 4 → F)
    (hν : ∀ j, ν j = if s j = true then -1 else 1) (hprod : ν 0 * ν 1 * ν 2 * ν 3 = 1) :
    cnt s % 2 = 0 := by
  unfold cnt
  rw [hν 0, hν 1, hν 2, hν 3] at hprod
  simp only [Finset.card_filter, Fin.sum_univ_four]
  cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3 <;>
    simp_all



open Classical in
theorem sign_eq_of_decide_eq (hneg : (-1 : F) ≠ 1) {a b : F} (ha : a = 1 ∨ a = -1)
    (hb : b = 1 ∨ b = -1) (h : decide (a = -1) = decide (b = -1)) : a = b := by
  rw [decide_eq_decide] at h
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rw [ha, hb]
  · exact absurd (ha.symm.trans (h.2 hb)) hneg.symm
  · exact absurd (hb.symm.trans (h.1 ha)) hneg.symm
  · rw [ha, hb]

open Classical in
theorem sign_decide (hneg : (-1 : F) ≠ 1) {a : F} (ha : a = 1 ∨ a = -1) :
    a = if decide (a = -1) = true then -1 else 1 := by
  rcases ha with rfl | rfl <;> simp [hneg.symm]

theorem exists_eigenbasis (h2 : (2 : F) ≠ 0) (E : Subgroup (GL (Fin 4) F)) [Finite E]
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1) :
    ∃ (b : Module.Basis (Fin 4) F (Fin 4 → F)) (μ : E → Fin 4 → F),
      ∀ (x : E) (j : Fin 4),
        Matrix.toLin' ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) (b j) = μ x j • b j := by
  classical
  let f : E → Module.End F (Fin 4 → F) :=
    fun x => Matrix.toLin' ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
  have hfcomm : ∀ x y, Commute (f x) (f y) := by
    intro x y
    show f x * f y = f y * f x
    simp only [f]
    rw [← toLin'_gl_mul, ← toLin'_gl_mul]
    exact congrArg _ (congrArg Units.val (hcomm x x.2 y y.2))
  have hfsq : ∀ x, f x ^ 2 = 1 := by
    intro x
    show f x ^ 2 = 1
    rw [sq]
    simp only [f]
    rw [← toLin'_gl_mul, hsq x x.2, Units.val_one, Matrix.toLin'_one]
    rfl
  obtain ⟨b, μ, hb⟩ :=
    CFSG.GH74.Filter.exists_basis_common_eigenvectors_of_sq_eq_one h2 f hfcomm hfsq
  have hfin : Module.finrank F (Fin 4 → F) = 4 := Module.finrank_fin_fun F
  refine ⟨b.reindex (finCongr hfin), fun x j => μ x ((finCongr hfin).symm j), fun x j => ?_⟩
  simp only [Module.Basis.reindex_apply]
  exact hb x _

theorem mat_eq_of_apply_eq (b : Module.Basis (Fin 4) F (Fin 4 → F)) {M N : Matrix (Fin 4) (Fin 4) F}
    (h : ∀ j, Matrix.toLin' M (b j) = Matrix.toLin' N (b j)) : M = N :=
  Matrix.toLin'.injective (b.ext h)

theorem sign_facts {E : Subgroup (GL (Fin 4) F)}
    (hsq : ∀ x ∈ E, x * x = 1) (hdet : ∀ x ∈ E, (x : Matrix (Fin 4) (Fin 4) F).det = 1)
    (b : Module.Basis (Fin 4) F (Fin 4 → F)) (μ : E → Fin 4 → F)
    (hb : ∀ (x : E) (j : Fin 4),
      Matrix.toLin' ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) (b j) = μ x j • b j) :
    (∀ x j, μ x j * μ x j = 1) ∧ ∀ x, μ x 0 * μ x 1 * μ x 2 * μ x 3 = 1 := by
  refine ⟨fun x j => ?_, fun x => ?_⟩
  · have h1 : Matrix.toLin' ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
        (Matrix.toLin' ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) (b j)) = b j := by
      have := congrArg (fun m : GL (Fin 4) F => Matrix.toLin' (m : Matrix (Fin 4) (Fin 4) F) (b j))
        (hsq x x.2)
      simpa [toLin'_gl_mul] using this
    rw [hb, map_smul, hb, smul_smul] at h1
    have h3 : (μ x j * μ x j - 1) • b j = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right (b.ne_zero j))
  · have h1 : LinearMap.toMatrix b b (Matrix.toLin' ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) =
        Matrix.diagonal (μ x) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [LinearMap.toMatrix_apply, hb]
      · simp [LinearMap.toMatrix_apply, hb, hij]
    have h2' := hdet x x.2
    rw [← LinearMap.det_toLin' ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F),
      ← LinearMap.det_toMatrix b, h1, Matrix.det_diagonal, Fin.prod_univ_four] at h2'
    exact h2'


theorem eigen_matrix (b : Module.Basis (Fin 4) F (Fin 4 → F)) (x : Matrix (Fin 4) (Fin 4) F)
    (μ : Fin 4 → F) (hb : ∀ j, Matrix.toLin' x (b j) = μ j • b j) :
    x * (Pi.basisFun F (Fin 4)).toMatrix b = (Pi.basisFun F (Fin 4)).toMatrix b * Matrix.diagonal μ := by
  have hPapp : ∀ a c, (Pi.basisFun F (Fin 4)).toMatrix b a c = b c a := fun a c => by
    simp [Module.Basis.toMatrix_apply]
  ext a c
  have h1 : (x * (Pi.basisFun F (Fin 4)).toMatrix b) a c = (Matrix.toLin' x (b c)) a := by
    simp only [Matrix.mul_apply, hPapp]
    rfl
  rw [h1, hb c, Matrix.mul_diagonal, hPapp, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem exists_gl_of_basis (b : Module.Basis (Fin 4) F (Fin 4 → F)) :
    ∃ P : GL (Fin 4) F, (P : Matrix (Fin 4) (Fin 4) F) = (Pi.basisFun F (Fin 4)).toMatrix b := by
  have hPunit : IsUnit ((Pi.basisFun F (Fin 4)).toMatrix b) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have := (Pi.basisFun F (Fin 4)).isUnit_det b
    rwa [Module.Basis.det_apply] at this
  obtain ⟨Pg, hPg⟩ := hPunit
  exact ⟨Pg, hPg⟩

theorem conj_eq_diagonal {P x : GL (Fin 4) F} {μ : Fin 4 → F}
    (h : (x : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) =
      (P : Matrix (Fin 4) (Fin 4) F) * Matrix.diagonal μ) :
    ((P⁻¹ * x * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal μ := by
  rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, h, ← Matrix.mul_assoc, Units.inv_mul,
    Matrix.one_mul]

theorem exists_frame (h2 : (2 : F) ≠ 0) (E : Subgroup (GL (Fin 4) F))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1)
    (hdet : ∀ x ∈ E, (x : Matrix (Fin 4) (Fin 4) F).det = 1) (hcard : Nat.card E = 8)
    {u : GL (Fin 4) F} (hu : u ∈ E) (hu1 : u ≠ 1) (hu2 : u ≠ -1) :
    ∃ P : GL (Fin 4) F,
      ((P⁻¹ * u * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![-1, -1, 1, 1] ∧
      ∀ ε : Fin 4 → F, (∀ i, ε i = 1 ∨ ε i = -1) → ε 0 * ε 1 * ε 2 * ε 3 = 1 →
        ∃ e ∈ E, ((P⁻¹ * e * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ε := by
  classical
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hneg : (-1 : F) ≠ 1 := by
    intro h
    apply h2
    have : (2 : F) = 1 - (-1) := by ring
    rw [this, h]; ring
  obtain ⟨b₀, μ₀, hb₀⟩ := exists_eigenbasis h2 E hcomm hsq
  obtain ⟨hs₀, hp₀⟩ := sign_facts hsq hdet b₀ μ₀ hb₀
  have hsign : ∀ (μ : E → Fin 4 → F), (∀ x j, μ x j * μ x j = 1) → ∀ x j, μ x j = 1 ∨ μ x j = -1 := by
    intro μ hμ x j
    have : (μ x j - 1) * (μ x j + 1) = 0 := by linear_combination hμ x j
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hsg₀ := hsign μ₀ hs₀
  let uE : E := ⟨u, hu⟩
  have hνu : ∀ j, μ₀ uE j = if decide (μ₀ uE j = -1) = true then -1 else 1 := fun j =>
    sign_decide hneg (hsg₀ uE j)
  have hev := even_of_prod hneg (fun j => decide (μ₀ uE j = -1)) (μ₀ uE) hνu (hp₀ uE)
  have hcnt : cnt (fun j => decide (μ₀ uE j = -1)) = 2 := by
    have hle : cnt (fun j => decide (μ₀ uE j = -1)) ≤ 4 := by
      unfold cnt
      calc _ ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_filter_le _ _
        _ = 4 := by simp
    have h0 : cnt (fun j => decide (μ₀ uE j = -1)) ≠ 0 := by
      intro h0
      apply hu1
      have hall : ∀ j, μ₀ uE j = 1 := by
        intro j
        have h' : ∀ j, ¬ (μ₀ uE j = -1) := by
          unfold cnt at h0
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
          intro j hj
          exact h0 (Finset.mem_univ j) (by simpa using hj)
        exact (hsg₀ uE j).resolve_right (h' j)
      have := mat_eq_of_apply_eq b₀ (M := (u : Matrix (Fin 4) (Fin 4) F)) (N := 1) (fun j => by
        rw [hb₀ uE j, hall j]; simp)
      exact Units.ext this
    have h4 : cnt (fun j => decide (μ₀ uE j = -1)) ≠ 4 := by
      intro h4
      apply hu2
      have hfu : (Finset.univ.filter fun j => decide (μ₀ uE j = -1) = true) = Finset.univ :=
        Finset.eq_univ_of_card _ (by simpa [cnt] using h4)
      have hall : ∀ j, μ₀ uE j = -1 := fun j => by
        have := hfu ▸ Finset.mem_univ j
        simpa using this
      have := mat_eq_of_apply_eq b₀ (M := (u : Matrix (Fin 4) (Fin 4) F)) (N := -1) (fun j => by
        rw [hb₀ uE j, hall j]; simp)
      apply Units.ext
      rw [this, Units.val_neg, Units.val_one]
    omega
  obtain ⟨τ, hτ0, hτ1, hτ2, hτ3⟩ := exists_perm _ hcnt
  simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hτ0 hτ1 hτ2 hτ3
  let b : Module.Basis (Fin 4) F (Fin 4 → F) := b₀.reindex τ.symm
  let μ : E → Fin 4 → F := fun x j => μ₀ x (τ j)
  have hb : ∀ (x : E) (j : Fin 4),
      Matrix.toLin' ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) (b j) = μ x j • b j := by
    intro x j
    simp only [b, μ, Module.Basis.reindex_apply, Equiv.symm_symm]
    exact hb₀ x (τ j)
  obtain ⟨hs, hp⟩ := sign_facts hsq hdet b μ hb
  have hsg := hsign μ hs
  obtain ⟨P, hP⟩ := exists_gl_of_basis b
  have hPx : ∀ x : E, ((P⁻¹ * (x : GL (Fin 4) F) * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal (μ x) := by
    intro x
    apply conj_eq_diagonal
    rw [hP]
    exact eigen_matrix b _ (μ x) (hb x)
  refine ⟨P, ?_, ?_⟩
  · have := hPx uE
    rw [this]
    congr 1
    funext j
    fin_cases j
    · simpa [μ] using hτ0
    · simpa [μ] using hτ1
    · simpa [μ] using (hsg₀ uE (τ 2)).resolve_right hτ2
    · simpa [μ] using (hsg₀ uE (τ 3)).resolve_right hτ3
  · intro ε hε hεp
    have hεν : ∀ j, ε j = if decide (ε j = -1) = true then -1 else 1 := fun j =>
      sign_decide hneg (hε j)
    let Ψ : E → {s : Fin 4 → Bool // cnt s % 2 = 0} := fun x =>
      ⟨fun j => decide (μ x j = -1), even_of_prod hneg _ (μ x) (fun j => sign_decide hneg (hsg x j))
        (hp x)⟩
    have hinj : Function.Injective Ψ := by
      intro x y hxy
      have hj : ∀ j, μ x j = μ y j := by
        intro j
        have := congrArg (fun s => s.1 j) hxy
        exact sign_eq_of_decide_eq hneg (hsg x j) (hsg y j) this
      have hxy' : ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = ((y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) :=
        mat_eq_of_apply_eq b (fun j => by rw [hb x j, hb y j, hj j])
      exact Subtype.ext (Units.ext hxy')
    have hbij : Function.Bijective Ψ :=
      hinj.bijective_of_nat_card_le (by rw [hcard, card_even])
    obtain ⟨x, hx⟩ := hbij.2 ⟨fun j => decide (ε j = -1),
      even_of_prod hneg _ ε hεν hεp⟩
    refine ⟨x, x.2, ?_⟩
    rw [hPx x]
    congr 1
    funext j
    have := congrArg (fun s => s.1 j) hx
    exact sign_eq_of_decide_eq hneg (hsg x j) (hε j) this

end CFSG.GH74.Generic.BProg.B3.S1DiagActFrame
