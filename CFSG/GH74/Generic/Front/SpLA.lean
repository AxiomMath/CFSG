module

public import CFSG.GH74.Generic.Front.InvolutionLA
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.GH74.Generic

open Module Matrix CFSG.Assembly.LowTwoRank

section SpLA

variable {F : Type} [Field F]

abbrev sp2Gram (F : Type) [Field F] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks 0 1 (-1) 0

abbrev sp2Form (u v : Fin 2 ⊕ Fin 2 → F) : F := u ⬝ᵥ (sp2Gram F *ᵥ v)

theorem sp2Gram_mul_self : sp2Gram F * sp2Gram F = -1 := by
  simp [fromBlocks_multiply, fromBlocks_neg, ← fromBlocks_one]

theorem sp2Gram_transpose : (sp2Gram F)ᵀ = -sp2Gram F := by
  simp [fromBlocks_transpose, fromBlocks_neg]

theorem sp2Form_comm (u v : Fin 2 ⊕ Fin 2 → F) : sp2Form v u = -sp2Form u v := by
  rw [sp2Form, sp2Form, dotProduct_mulVec, dotProduct_comm, ← vecMul_transpose, sp2Gram_transpose,
    vecMul_neg]
  simp

theorem sp2Form_self (h2 : (2 : F) ≠ 0) (u : Fin 2 ⊕ Fin 2 → F) : sp2Form u u = 0 := by
  have h := sp2Form_comm u u
  have : (2 : F) * sp2Form u u = 0 := by linear_combination h
  exact (mul_eq_zero.1 this).resolve_left h2

theorem sp2Form_add_right (v x y : Fin 2 ⊕ Fin 2 → F) :
    sp2Form v (x + y) = sp2Form v x + sp2Form v y := by
  simp [sp2Form, mulVec_add, dotProduct_add]

theorem sp2Form_smul_right (l : F) (u v : Fin 2 ⊕ Fin 2 → F) :
    sp2Form u (l • v) = l * sp2Form u v := by
  simp [sp2Form, mulVec_smul, dotProduct_smul]

theorem sp2Form_neg_left (u v : Fin 2 ⊕ Fin 2 → F) : sp2Form (-u) v = -sp2Form u v := by
  simp [sp2Form, neg_dotProduct]

theorem eq_zero_of_sp2Form_right {u : Fin 2 ⊕ Fin 2 → F} (h : ∀ v, sp2Form u v = 0) : u = 0 := by
  by_contra hu
  have hJ : u ᵥ* sp2Gram F ≠ 0 := by
    intro h0
    apply hu
    have : u ᵥ* sp2Gram F ᵥ* sp2Gram F = 0 := by rw [h0, zero_vecMul]
    rw [vecMul_vecMul, sp2Gram_mul_self, vecMul_neg, vecMul_one, neg_eq_zero] at this
    exact this
  obtain ⟨b, hb⟩ := Function.ne_iff.1 hJ
  have := h (Pi.single b 1)
  rw [sp2Form, dotProduct_mulVec, dotProduct_single, mul_one] at this
  exact hb (by simpa using this)

theorem sp2Form_mulVec_invariant {t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hs : tᵀ * sp2Gram F * t = sp2Gram F) (a b : Fin 2 ⊕ Fin 2 → F) :
    sp2Form (t *ᵥ a) (t *ᵥ b) = sp2Form a b := by
  have h1 : ∀ x : Fin 2 ⊕ Fin 2 → F, (t *ᵥ a) ⬝ᵥ x = a ⬝ᵥ (tᵀ *ᵥ x) := by
    intro x
    rw [dotProduct_comm, dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  rw [sp2Form, h1, mulVec_mulVec, mulVec_mulVec, hs]

theorem sp2Form_eigen_orth (h2 : (2 : F) ≠ 0) {t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hs : tᵀ * sp2Gram F * t = sp2Gram F) {w u : Fin 2 ⊕ Fin 2 → F} (hw : t *ᵥ w = -w)
    (hu : t *ᵥ u = u) : sp2Form w u = 0 := by
  have h := sp2Form_mulVec_invariant hs w u
  rw [hw, hu, sp2Form_neg_left] at h
  have : (2 : F) * sp2Form w u = 0 := by linear_combination (-1 : F) * h
  exact (mul_eq_zero.1 this).resolve_left h2

theorem exists_hyperbolic_pair {A B : Submodule F (Fin 2 ⊕ Fin 2 → F)} (hAB : A ⊔ B = ⊤)
    (horth : ∀ a ∈ A, ∀ b ∈ B, sp2Form a b = 0) (hA : A ≠ ⊥) :
    ∃ e ∈ A, ∃ f ∈ A, sp2Form e f = 1 := by
  obtain ⟨e, heA, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA
  have : ∃ f₀ ∈ A, sp2Form e f₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply he0
    apply eq_zero_of_sp2Form_right
    intro v
    have hv : v ∈ A ⊔ B := by rw [hAB]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    rw [sp2Form_add_right, hcon a ha, horth e heA b hb, add_zero]
  obtain ⟨f₀, hf₀, hne⟩ := this
  refine ⟨e, heA, (sp2Form e f₀)⁻¹ • f₀, A.smul_mem _ hf₀, ?_⟩
  rw [sp2Form_smul_right, inv_mul_cancel₀ hne]

abbrev sp2ColMat (p q : Fin 2 → Fin 2 ⊕ Fin 2 → F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.of fun a x => Sum.elim (fun i => p i a) (fun i => q i a) x

theorem sp2ColMat_mulVec_inl (p q : Fin 2 → Fin 2 ⊕ Fin 2 → F) (i : Fin 2) :
    sp2ColMat p q *ᵥ Pi.single (Sum.inl i) 1 = p i := by
  ext a
  simp [sp2ColMat, mulVec, dotProduct, Pi.single_apply]

theorem sp2ColMat_mulVec_inr (p q : Fin 2 → Fin 2 ⊕ Fin 2 → F) (i : Fin 2) :
    sp2ColMat p q *ᵥ Pi.single (Sum.inr i) 1 = q i := by
  ext a
  simp [sp2ColMat, mulVec, dotProduct, Pi.single_apply]

theorem sp2_gram_apply (C : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (a b : Fin 2 ⊕ Fin 2) :
    (Cᵀ * sp2Gram F * C) a b = sp2Form (C *ᵥ Pi.single a 1) (C *ᵥ Pi.single b 1) := by
  rw [mulVec_single_one, mulVec_single_one, sp2Form, Matrix.mul_assoc]
  rfl

theorem exists_sp2_mulVec {p q : Fin 2 → Fin 2 ⊕ Fin 2 → F}
    (hpp : ∀ i j, sp2Form (p i) (p j) = 0) (hqq : ∀ i j, sp2Form (q i) (q j) = 0)
    (hpq : ∀ i j, sp2Form (p i) (q j) = if i = j then 1 else 0) :
    ∃ g : StatedSp 2 F, ∀ i,
      ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
          Pi.single (Sum.inl i) 1 = p i ∧
      ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
          Pi.single (Sum.inr i) 1 = q i := by
  have hqp : ∀ i j, sp2Form (q i) (p j) = -(if j = i then 1 else 0) := fun i j => by
    rw [sp2Form_comm, hpq]
  have hgram : (sp2ColMat p q)ᵀ * sp2Gram F * sp2ColMat p q = sp2Gram F := by
    ext x y
    rw [sp2_gram_apply]
    rcases x with i | i <;> rcases y with j | j
    · rw [sp2ColMat_mulVec_inl, sp2ColMat_mulVec_inl, hpp]
      simp
    · rw [sp2ColMat_mulVec_inl, sp2ColMat_mulVec_inr, hpq]
      simp [Matrix.one_apply]
    · rw [sp2ColMat_mulVec_inr, sp2ColMat_mulVec_inl, hqp]
      simp [Matrix.one_apply, eq_comm]
    · rw [sp2ColMat_mulVec_inr, sp2ColMat_mulVec_inr, hqq]
      simp
  have hdet : (sp2ColMat p q).det ≠ 0 := by
    have hinv : (-(sp2Gram F * (sp2ColMat p q)ᵀ * sp2Gram F)) * sp2ColMat p q = 1 := by
      rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (sp2ColMat p q)ᵀ,
        hgram, sp2Gram_mul_self, neg_neg]
    exact (isUnit_det_of_left_inverse hinv).ne_zero
  let g0 : GL (Fin 2 ⊕ Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet
  have hg0 : g0 ∈ StatedSp 2 F := Subgroup.subset_closure hgram
  exact ⟨⟨g0, hg0⟩, fun i => ⟨sp2ColMat_mulVec_inl p q i, sp2ColMat_mulVec_inr p q i⟩⟩

theorem exists_symplectic_conj (h2 : (2 : F) ≠ 0) (t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (ht : t * t = 1) (hs : tᵀ * sp2Gram F * t = sp2Gram F) (h1 : t ≠ 1) (hm1 : t ≠ -1) :
    ∃ g : StatedSp 2 F,
      t * ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
          Matrix.diagonal (Sum.elim ![(-1 : F), 1] ![(-1 : F), 1]) := by
  classical
  let f := Matrix.toLin' t
  have hf : ∀ v, f (f v) = v := fun v => by
    have : f (f v) = (t * t).mulVec v := by
      show Matrix.toLin' t (Matrix.toLin' t v) = _
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec]
    rw [this, ht, Matrix.one_mulVec]
  have hcompl := involution_isCompl h2 f hf
  set W := LinearMap.ker (f + LinearMap.id) with hWdef
  set U := LinearMap.ker (f - LinearMap.id) with hUdef
  have hWmem : ∀ v, v ∈ W ↔ t *ᵥ v = -v := by
    intro v
    rw [hWdef, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, add_eq_zero_iff_eq_neg]
    simp [f, Matrix.toLin'_apply]
  have hUmem : ∀ v, v ∈ U ↔ t *ᵥ v = v := by
    intro v
    rw [hUdef, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    simp [f, Matrix.toLin'_apply]
  have hcols : ∀ M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F,
      (∀ j, M *ᵥ Pi.single j 1 = N *ᵥ Pi.single j 1) → M = N := fun M N h =>
    Matrix.ext fun i j => by
      have := congrFun (h j) i
      rwa [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this
  have hW0 : W ≠ ⊥ := by
    intro hW
    have hU : U = ⊤ := by
      have := hcompl.sup_eq_top
      rwa [hW, bot_sup_eq] at this
    apply h1
    apply hcols
    intro j
    have hv : (Pi.single j (1 : F) : Fin 2 ⊕ Fin 2 → F) ∈ U := by rw [hU]; trivial
    rw [(hUmem _).1 hv, Matrix.one_mulVec]
  have hU0 : U ≠ ⊥ := by
    intro hU
    have hW : W = ⊤ := by
      have := hcompl.sup_eq_top
      rwa [hU, sup_bot_eq] at this
    apply hm1
    apply hcols
    intro j
    have hv : (Pi.single j (1 : F) : Fin 2 ⊕ Fin 2 → F) ∈ W := by rw [hW]; trivial
    rw [(hWmem _).1 hv, Matrix.neg_mulVec, Matrix.one_mulVec]
  have hWU : ∀ a ∈ W, ∀ b ∈ U, sp2Form a b = 0 := fun a ha b hb =>
    sp2Form_eigen_orth h2 hs ((hWmem a).1 ha) ((hUmem b).1 hb)
  have hUW : ∀ a ∈ U, ∀ b ∈ W, sp2Form a b = 0 := fun a ha b hb => by
    rw [sp2Form_comm, hWU b hb a ha, neg_zero]
  obtain ⟨e, heW, f₁, hfW, hef⟩ := exists_hyperbolic_pair hcompl.sup_eq_top hWU hW0
  obtain ⟨e', heU, f', hfU, hef'⟩ :=
    exists_hyperbolic_pair (by rw [sup_comm]; exact hcompl.sup_eq_top) hUW hU0
  let p : Fin 2 → Fin 2 ⊕ Fin 2 → F := ![e, e']
  let q : Fin 2 → Fin 2 ⊕ Fin 2 → F := ![f₁, f']
  have hpp : ∀ i j, sp2Form (p i) (p j) = 0 := by
    simp only [Fin.forall_fin_two]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
      simp [p, sp2Form_self h2, hWU _ heW _ heU, hUW _ heU _ heW]
  have hqq : ∀ i j, sp2Form (q i) (q j) = 0 := by
    simp only [Fin.forall_fin_two]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
      simp [q, sp2Form_self h2, hWU _ hfW _ hfU, hUW _ hfU _ hfW]
  have hpq : ∀ i j, sp2Form (p i) (q j) = if i = j then 1 else 0 := by
    simp only [Fin.forall_fin_two]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
      simp [p, q, hef, hef', hWU _ heW _ hfU, hUW _ heU _ hfW]
  obtain ⟨g, hg⟩ := exists_sp2_mulVec hpp hqq hpq
  have heig : t *ᵥ e = -e := (hWmem e).1 heW
  have hfig : t *ᵥ f₁ = -f₁ := (hWmem f₁).1 hfW
  have heig' : t *ᵥ e' = e' := (hUmem e').1 heU
  have hfig' : t *ᵥ f' = f' := (hUmem f').1 hfU
  have key : ∀ i : Fin 2, t *ᵥ p i = (![(-1 : F), 1] i) • p i ∧
      t *ᵥ q i = (![(-1 : F), 1] i) • q i := by
    simp only [Fin.forall_fin_two]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp [p, q, heig, hfig, heig', hfig']
  have hD : ∀ c : Fin 2 ⊕ Fin 2,
      Matrix.diagonal (Sum.elim ![(-1 : F), 1] ![(-1 : F), 1]) *ᵥ Pi.single c 1 =
        (Sum.elim ![(-1 : F), 1] ![(-1 : F), 1] c) • (Pi.single c 1 : Fin 2 ⊕ Fin 2 → F) := by
    intro c
    ext j
    simp only [Matrix.mulVec_diagonal, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    by_cases hj : j = c
    · subst hj; simp
    · simp [hj]
  refine ⟨g, hcols _ _ fun c => ?_⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hD c, Matrix.mulVec_smul]
  rcases c with i | i
  · rw [(hg i).1]
    exact (key i).1
  · rw [(hg i).2]
    exact (key i).2

end SpLA

end CFSG.GH74.Generic
