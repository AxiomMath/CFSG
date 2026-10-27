module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotInvolutionCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSquareZero

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.LocalAnalysis.ComponentInitial

variable {K : Type*} [Field K]

section NilOf

variable {ι : Type*} [DecidableEq ι] {k : ℕ}

variable (K) in
@[expose] def nilOf (u w : Fin k → ι) : Matrix ι ι K :=
  Matrix.of fun i j => if ∃ a, u a = i ∧ w a = j then 1 else 0

theorem nilOf_apply (u w : Fin k → ι) (i j : ι) :
    nilOf K u w i j = if ∃ a, u a = i ∧ w a = j then 1 else 0 :=
  rfl

variable [Fintype ι]

theorem mul_nilOf_apply_w {u w : Fin k → ι} (hw : Function.Injective w) (B : Matrix ι ι K)
    (i : ι) (b : Fin k) : (B * nilOf K u w) i (w b) = B i (u b) := by
  simp only [mul_apply, nilOf_apply]
  rw [Finset.sum_eq_single (u b)]
  · rw [ite_eq_left ⟨b, rfl, rfl⟩, mul_one]
  · intro l _ hl
    rw [ite_eq_right, mul_zero]
    rintro ⟨a, rfl, ha⟩
    exact hl (by rw [hw ha])
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mul_nilOf_apply_of_forall_ne {u w : Fin k → ι} (B : Matrix ι ι K) (i : ι) {j : ι}
    (hj : ∀ a, w a ≠ j) : (B * nilOf K u w) i j = 0 := by
  simp only [mul_apply, nilOf_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [ite_eq_right, mul_zero]
  rintro ⟨a, -, ha⟩
  exact hj a ha

theorem diagonal_mul_nilOf {u w : Fin k → ι} {d : ι → K} (hd : ∀ a, d (u a) = d (w a)) :
    diagonal d * nilOf K u w = nilOf K u w * diagonal d := by
  ext i j
  rw [diagonal_mul, mul_diagonal, nilOf_apply]
  split_ifs with h
  · obtain ⟨a, rfl, rfl⟩ := h
    rw [mul_one, one_mul, hd a]
  · rw [mul_zero, zero_mul]

omit [Fintype ι] in
theorem nilOf_eq_zero_of_eq_zero {u w : Fin k → ι} (hk : k = 0) : nilOf K u w = 0 := by
  subst hk
  ext i j
  rw [nilOf_apply, ite_eq_right (by rintro ⟨a, -⟩; exact a.elim0), Matrix.zero_apply]

end NilOf

section NormalForm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem matrix_add_self_eq_zero [CharP K 2] (X : Matrix ι ι K) : X + X = 0 := by
  ext i j
  rw [Matrix.add_apply, CharTwo.add_self_eq_zero, Matrix.zero_apply]

theorem sub_one_mul_sub_one_eq_zero_of_mul_self [CharP K 2] {A : Matrix ι ι K}
    (hA : A * A = 1) : (A - 1) * (A - 1) = 0 := by
  calc (A - 1) * (A - 1) = A * A + 1 - (A + A) := by noncomm_ring
    _ = 0 := by rw [hA, matrix_add_self_eq_zero, matrix_add_self_eq_zero, sub_zero]

theorem exists_conj_eq_one_add_nilOf_of_basis [Finite K] [CharP K 2]
    {A : SpecialLinearGroup ι K} {ℓ r : ℕ} (b : Module.Basis (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K (ι → K))
    (hb1 : ∀ a, ((A : Matrix ι ι K) - 1) *ᵥ b (.inl a) = b (.inr (.inl a)))
    (hb2 : ∀ s, ((A : Matrix ι ι K) - 1) *ᵥ b (.inr s) = 0) :
    ∃ (u w : Fin ℓ → ι), Function.Injective u ∧ Function.Injective w ∧
      (∀ a b, u a ≠ w b) ∧ ∃ g : SpecialLinearGroup ι K,
        ((g * A * g⁻¹ : SpecialLinearGroup ι K) : Matrix ι ι K) = 1 + nilOf K u w := by
  classical
  set N : Matrix ι ι K := (A : Matrix ι ι K) - 1 with hNdef
  have hcard : Fintype.card (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) = Fintype.card ι := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card]
  set σ : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) ≃ ι := Fintype.equivOfCardEq hcard with hσ
  set u : Fin ℓ → ι := fun a => σ (.inr (.inl a)) with hu
  set w : Fin ℓ → ι := fun a => σ (.inl a) with hw
  have hui : Function.Injective u := fun a a' h => by
    have := σ.injective h
    simpa using this
  have hwi : Function.Injective w := fun a a' h => by
    have := σ.injective h
    simpa using this
  have huw : ∀ a a', u a ≠ w a' := fun a a' h => by
    have := σ.injective h
    simp at this
  set b' := b.reindex σ with hb'
  set M : Matrix ι ι K := (Pi.basisFun K ι).toMatrix b' with hM
  set Mi : Matrix ι ι K := b'.toMatrix (Pi.basisFun K ι) with hMi
  have hMMi : M * Mi = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hMiM : Mi * M = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hMapp : ∀ i j, M i j = b' j i := fun i j => by
    rw [hM, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
  have hNM : N * M = M * nilOf K u w := by
    ext i j
    have hcol : (N * M) i j = (N *ᵥ b' j) i := by
      simp only [mul_apply, mulVec, dotProduct, hMapp]
    rw [hcol]
    rcases hj : σ.symm j with a | s
    · have hjw : j = w a := by
        rw [hw]
        simp only
        rw [← hj, Equiv.apply_symm_apply]
      have h1 : b' j = b (.inl a) := by rw [hb', Module.Basis.reindex_apply, hj]
      have h2 : N *ᵥ b (.inl a) = b' (u a) := by
        rw [hb1 a, hb', Module.Basis.reindex_apply, hu]
        simp
      rw [h1, h2, hjw, mul_nilOf_apply_w hwi, hMapp]
    · have h1 : b' j = b (.inr s) := by rw [hb', Module.Basis.reindex_apply, hj]
      rw [h1, hb2 s, Pi.zero_apply, mul_nilOf_apply_of_forall_ne]
      intro a ha
      rw [← ha, hw] at hj
      simp at hj
  have hAN : (A : Matrix ι ι K) = 1 + N := by rw [hNdef]; abel
  have hMiA : Mi * (A : Matrix ι ι K) = (1 + nilOf K u w) * Mi := by
    calc Mi * (A : Matrix ι ι K) = Mi * (A : Matrix ι ι K) * (M * Mi) := by
          rw [hMMi, Matrix.mul_one]
      _ = Mi * (1 + N) * M * Mi := by rw [hAN]; simp only [Matrix.mul_assoc]
      _ = (Mi * M + Mi * (N * M)) * Mi := by
          rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul]; simp only [Matrix.mul_assoc]
      _ = (1 + nilOf K u w) * Mi := by
          rw [hNM, ← Matrix.mul_assoc, hMiM, Matrix.one_mul]
  have hdet : Mi.det * M.det = 1 := by rw [← det_mul, hMiM, det_one]
  have hδ : Mi.det ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  rcases Nat.eq_zero_or_pos ℓ with hℓ0 | hℓpos
  ·
    refine ⟨u, w, hui, hwi, huw, 1, ?_⟩
    rw [nilOf_eq_zero_of_eq_zero hℓ0, add_zero, one_mul, inv_one, mul_one]
    have h1 : Mi * (A : Matrix ι ι K) = Mi := by
      rw [hMiA, nilOf_eq_zero_of_eq_zero hℓ0, add_zero, Matrix.one_mul]
    calc (A : Matrix ι ι K) = M * (Mi * (A : Matrix ι ι K)) := by
          rw [← Matrix.mul_assoc, hMMi, Matrix.one_mul]
      _ = 1 := by rw [h1, hMMi]
  · set a₀ : Fin ℓ := ⟨0, hℓpos⟩
    obtain ⟨μ, hμ⟩ := isSquare_of_charTwo' (Mi.det)⁻¹
    set d : ι → K := Function.update (Function.update (1 : ι → K) (u a₀) μ) (w a₀) μ with hd
    have hdu : ∀ a, d (u a) = d (w a) := by
      intro a
      rw [hd, Function.update_apply, Function.update_apply, Function.update_apply,
        Function.update_apply, ite_eq_right (huw a a₀), ite_eq_right (huw a₀ a).symm]
      by_cases h : a = a₀
      · subst h
        simp
      · rw [ite_eq_right (fun h' => h (hui h')), ite_eq_right (fun h' => h (hwi h'))]
        rfl
    have hdetD : (diagonal d).det = μ * μ := by
      rw [det_diagonal, hd, Finset.prod_update_of_mem (Finset.mem_univ _),
        Finset.prod_update_of_mem (by simp [huw a₀ a₀])]
      simp
    have hgdet : (diagonal d * Mi).det = 1 := by
      rw [det_mul, hdetD, ← hμ, inv_mul_cancel₀ hδ]
    set g : SpecialLinearGroup ι K := ⟨diagonal d * Mi, hgdet⟩ with hg
    refine ⟨u, w, hui, hwi, huw, g, ?_⟩
    have hgA : (g : Matrix ι ι K) * (A : Matrix ι ι K) = (1 + nilOf K u w) * g := by
      change diagonal d * Mi * (A : Matrix ι ι K) = (1 + nilOf K u w) * (diagonal d * Mi)
      have hD1 : diagonal d * (1 + nilOf K u w) = (1 + nilOf K u w) * diagonal d := by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, diagonal_mul_nilOf hdu]
      rw [Matrix.mul_assoc, hMiA, ← Matrix.mul_assoc, hD1, Matrix.mul_assoc]
    have hgg : (g : Matrix ι ι K) * ((g⁻¹ : SpecialLinearGroup ι K) : Matrix ι ι K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hgA,
      Matrix.mul_assoc, hgg, Matrix.mul_one]

theorem exists_conj_eq_one_add_nilOf [Finite K] [CharP K 2] {A : SpecialLinearGroup ι K}
    (hA : A * A = 1) :
    ∃ (k : ℕ) (u w : Fin k → ι), Function.Injective u ∧ Function.Injective w ∧
      (∀ a b, u a ≠ w b) ∧ ∃ g : SpecialLinearGroup ι K,
        ((g * A * g⁻¹ : SpecialLinearGroup ι K) : Matrix ι ι K) = 1 + nilOf K u w := by
  have hA' : (A : Matrix ι ι K) * A = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hA, Matrix.SpecialLinearGroup.coe_one]
  have hNN := sub_one_mul_sub_one_eq_zero_of_mul_self hA'
  have hf2 : Matrix.mulVecLin ((A : Matrix ι ι K) - 1) ∘ₗ
      Matrix.mulVecLin ((A : Matrix ι ι K) - 1) = 0 := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, mulVec_mulVec,
      hNN, zero_mulVec, LinearMap.zero_apply]
  obtain ⟨r, b, hb1, hb2⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.exists_basis_sq_eq_zero _ hf2
  obtain ⟨u, w, hu, hw, huw, g, hg⟩ := exists_conj_eq_one_add_nilOf_of_basis b hb1 hb2
  exact ⟨_, u, w, hu, hw, huw, g, hg⟩

end NormalForm

section PSL

variable {n : ℕ}

@[expose] def InvPlacement.ofSubtype {I : Finset (Fin n)} {k : ℕ} (u w : Fin k → I)
    (hu : Function.Injective u) (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b) :
    InvPlacement n k where
  u a := u a
  w a := w a
  u_injective := Subtype.val_injective.comp hu
  w_injective := Subtype.val_injective.comp hw
  u_ne_w a b h := huw a b (Subtype.ext h)

theorem InvPlacement.outer_ofSubtype_subset {I : Finset (Fin n)} {k : ℕ} (u w : Fin k → I)
    (hu : Function.Injective u) (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b) :
    (InvPlacement.ofSubtype u w hu hw huw).outer ⊆ I := by
  intro i hi
  obtain ⟨s, rfl⟩ := (InvPlacement.ofSubtype u w hu hw huw).mem_outer.1 hi
  rcases s with a | a
  · exact (u a).2
  · exact (w a).2

theorem blockMatrix_one_add_nilOf {I : Finset (Fin n)} {k : ℕ} (u w : Fin k → I)
    (hu : Function.Injective u) (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b) :
    blockMatrix I (1 + nilOf K u w) =
      ((InvPlacement.ofSubtype u w hu hw huw).mat K : Matrix (Fin n) (Fin n) K) := by
  ext i j
  rw [blockMatrix_apply, InvPlacement.coe_mat, Matrix.add_apply]
  change _ = _ + (if ∃ a, (u a : Fin n) = i ∧ (w a : Fin n) = j then (1 : K) else 0)
  by_cases h : i ∈ I ∧ j ∈ I
  · rw [dite_eq_left h, Matrix.add_apply, nilOf_apply]
    have e1 : (1 : Matrix I I K) ⟨i, h.1⟩ ⟨j, h.2⟩ = (1 : Matrix (Fin n) (Fin n) K) i j := by
      by_cases hij : i = j
      · subst hij
        rw [one_apply_eq, one_apply_eq]
      · rw [one_apply_ne (fun h' => hij (congrArg Subtype.val h')), one_apply_ne hij]
    have e2 : (∃ a, u a = ⟨i, h.1⟩ ∧ w a = ⟨j, h.2⟩) ↔
        ∃ a, (u a : Fin n) = i ∧ (w a : Fin n) = j := by
      simp [Subtype.ext_iff]
    rw [e1]
    congr 1
    by_cases hp : ∃ a, (u a : Fin n) = i ∧ (w a : Fin n) = j
    · rw [ite_eq_left (e2.2 hp), ite_eq_left hp]
    · rw [ite_eq_right (fun h' => hp (e2.1 h')), ite_eq_right hp]
  · rw [dite_eq_right h, ite_eq_right, add_zero]
    rintro ⟨a, ha, hb⟩
    exact h ⟨ha ▸ (u a).2, hb ▸ (w a).2⟩

@[expose] def InvPlacement.ofFun {k : ℕ} (u w : Fin k → Fin n) (hu : Function.Injective u)
    (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b) : InvPlacement n k :=
  ⟨u, w, hu, hw, huw⟩

theorem one_add_nilOf_eq_coe_mat {k : ℕ} (u w : Fin k → Fin n) (hu : Function.Injective u)
    (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b) :
    1 + nilOf K u w = ((InvPlacement.ofFun u w hu hw huw).mat K : Matrix (Fin n) (Fin n) K) :=
  rfl

theorem eq_one_of_mul_self_eq_one_charTwo [CharP K 2] {x : K} (h : x * x = 1) : x = 1 := by
  have h2 : (x - 1) * (x - 1) = 0 := by
    calc (x - 1) * (x - 1) = x * x + 1 - (x + x) := by ring
      _ = 0 := by rw [h, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, sub_zero]
  exact sub_eq_zero.1 (mul_self_eq_zero.1 h2)

theorem exists_proj_eq_of_mul_self [Finite K] [CharP K 2] {y : LinearFlag.projectiveSL n K}
    (hy : y * y = 1) :
    ∃ A : SpecialLinearGroup (Fin n) K, A * A = 1 ∧ LinearFlag.proj n K A = y := by
  obtain ⟨B, rfl⟩ := LinearFlag.proj_surjective n K y
  rw [← map_mul, LinearFlag.proj_eq_one_iff] at hy
  obtain ⟨c, hcn, hc⟩ := LinearFlag.mem_scalars.1 hy
  obtain ⟨μ, hμ⟩ := isSquare_of_charTwo' (c : K)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hμ
    exact c.ne_zero hμ
  set m : Kˣ := Units.mk0 μ hμ0 with hm
  have hmn : m ^ n = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, hm, Units.val_mk0]
    refine eq_one_of_mul_self_eq_one_charTwo ?_
    rw [← mul_pow, ← hμ, ← Units.val_pow_eq_pow_val, hcn, Units.val_one]
  have hmn' : m⁻¹ ^ n = 1 := by rw [inv_pow, hmn, inv_one]
  set z := LinearFlag.scalarElement m⁻¹ hmn' with hz
  have hzc : z ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) :=
    LinearFlag.scalars_le_center n K (LinearFlag.scalarElement_mem_scalars _ _)
  refine ⟨B * z, ?_, ?_⟩
  · have hcomm : z * B = B * z := (Subgroup.mem_center_iff.1 hzc B).symm
    have e1 : B * z * (B * z) = B * B * (z * z) := by
      calc B * z * (B * z) = B * (z * B) * z := by simp only [mul_assoc]
        _ = B * (B * z) * z := by rw [hcomm]
        _ = B * B * (z * z) := by simp only [mul_assoc]
    rw [e1]
    ext i j
    have hzz : ((z * z : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        scalar (Fin n) ((m⁻¹ * m⁻¹ : Kˣ) : K) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, hz, LinearFlag.coe_scalarElement, ← map_mul,
        Units.val_mul]
    have hval : (c : K) * ((m⁻¹ * m⁻¹ : Kˣ) : K) = 1 := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, hm, Units.val_mk0, hμ]
      field_simp
    rw [Matrix.SpecialLinearGroup.coe_mul (B * B), hc, hzz, ← map_mul, hval, map_one,
      Matrix.SpecialLinearGroup.coe_one]
  · rw [map_mul, LinearFlag.proj_eq_one_iff.2 (LinearFlag.scalarElement_mem_scalars _ _),
      mul_one]

theorem exists_conj_eq_elt [Finite K] [CharP K 2] {y : LinearFlag.projectiveSL n K}
    (hy : y * y = 1) :
    ∃ (k : ℕ) (P : InvPlacement n k) (c : LinearFlag.projectiveSL n K),
      c * y * c⁻¹ = P.elt K := by
  obtain ⟨A, hA, rfl⟩ := exists_proj_eq_of_mul_self hy
  obtain ⟨k, u, w, hu, hw, huw, g, hg⟩ := exists_conj_eq_one_add_nilOf (K := K) hA
  refine ⟨k, InvPlacement.ofFun u w hu hw huw, LinearFlag.proj n K g, ?_⟩
  rw [← map_mul, ← map_inv, ← map_mul, InvPlacement.elt]
  congr 1
  exact Subtype.ext (hg.trans (one_add_nilOf_eq_coe_mat u w hu hw huw))

theorem eq_one_of_mem_scalars_of_mem_blockSpecialLinear {I : Finset (Fin n)} (hI : I.card < n)
    {A : SpecialLinearGroup (Fin n) K} (hA : A ∈ blockSpecialLinear I)
    (hAs : A ∈ LinearFlag.scalars n K) : A = 1 := by
  obtain ⟨c, -, hc⟩ := LinearFlag.mem_scalars.1 hAs
  obtain ⟨j, -, hj⟩ : ∃ j, j ∈ (Finset.univ : Finset (Fin n)) ∧ j ∉ I :=
    Finset.exists_mem_notMem_of_card_lt_card (by simpa using hI)
  have hjj := hA j j (Or.inl hj)
  rw [hc, scalar_apply, diagonal_apply_eq, one_apply_eq] at hjj
  apply Subtype.ext
  rw [hc, hjj, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem exists_conj_eq_elt_of_mem_blockSL [Finite K] [CharP K 2] {I : Finset (Fin n)}
    (hI : I.card < n) {y : LinearFlag.projectiveSL n K} (hyI : y ∈ blockSL I)
    (hy : y * y = 1) :
    ∃ (k : ℕ) (P : InvPlacement n k) (c : LinearFlag.projectiveSL n K),
      P.outer ⊆ I ∧ c * y * c⁻¹ = P.elt K := by
  obtain ⟨A, hAI, rfl⟩ := mem_blockSL.1 hyI
  have hA : A * A = 1 := by
    rw [← map_mul, LinearFlag.proj_eq_one_iff] at hy
    exact eq_one_of_mem_scalars_of_mem_blockSpecialLinear hI
      ((blockSpecialLinear I).mul_mem hAI hAI) hy
  rw [← range_blockEmbed] at hAI
  obtain ⟨A', rfl⟩ := hAI
  have hA' : A' * A' = 1 := by
    apply blockEmbed_injective I
    rw [map_mul, hA, map_one]
  obtain ⟨k, u, w, hu, hw, huw, g, hg⟩ := exists_conj_eq_one_add_nilOf (K := K) hA'
  refine ⟨k, InvPlacement.ofSubtype u w hu hw huw,
    LinearFlag.proj n K (blockEmbed I g), InvPlacement.outer_ofSubtype_subset u w hu hw huw, ?_⟩
  rw [← map_mul, ← map_inv, ← map_mul, InvPlacement.elt]
  congr 1
  apply Subtype.ext
  rw [← map_inv, ← map_mul, ← map_mul, coe_blockEmbed, hg]
  exact blockMatrix_one_add_nilOf u w hu hw huw

theorem InvPlacement.compl_subset_free_of_outer_subset {k : ℕ} (P : InvPlacement n k)
    {I : Finset (Fin n)} (h : P.outer ⊆ I) : Iᶜ ⊆ P.free := by
  intro i hi
  rw [Finset.mem_compl] at hi
  by_contra h'
  exact hi (h (P.mem_outer_of_not_mem_free h'))

theorem InvPlacement.free_card_two_le_of_outer_subset_compl_pair {k : ℕ} (P : InvPlacement n k)
    {a b : Fin n} (hab : a ≠ b) (h : P.outer ⊆ ({a, b} : Finset (Fin n))ᶜ) :
    a ∈ P.free ∧ b ∈ P.free ∧ 2 ≤ P.free.card := by
  have hsub := P.compl_subset_free_of_outer_subset h
  rw [compl_compl] at hsub
  refine ⟨hsub (by simp), hsub (by simp), ?_⟩
  calc 2 = ({a, b} : Finset (Fin n)).card := (Finset.card_pair hab).symm
    _ ≤ P.free.card := Finset.card_le_card hsub

end PSL

end CFSG.SeitzReduction.LinearPilot
