module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherDescents
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBruhat

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Matrix SymplecticFlag CFSG.Assembly.LowTwoRank SymplecticTorusWeyl
open CFSG.LieType.Universal.SpecialLinear (signedPerm signedPerm_apply)

variable {r : ℕ} {K : Type} [Field K]

theorem isLinePerm_mul_single {σ : Equiv.Perm (Fin r ⊕ Fin r)}
    {M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (hM : IsLinePerm σ M) (a b : Fin r ⊕ Fin r)
    (c : K) : M * single a b c = single (σ a) b (M (σ a) a * c) := by
  ext y z
  rw [mul_apply, Finset.sum_eq_single a, single_apply, single_apply]
  · by_cases hy : y = σ a
    · subst hy
      simp
    · rw [hM.apply_eq_zero hy, zero_mul]
      simp [Ne.symm hy]
  · intro u _ hu
    rw [single_apply, ite_eq_right (fun h => hu h.1.symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem single_mul_isLinePerm {τ : Equiv.Perm (Fin r ⊕ Fin r)}
    {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (hN : IsLinePerm τ N) (a b : Fin r ⊕ Fin r)
    (c : K) : single a b c * N = single a (τ⁻¹ b) (c * N b (τ⁻¹ b)) := by
  ext y z
  rw [mul_apply, Finset.sum_eq_single b, single_apply, single_apply]
  · by_cases hz : z = τ⁻¹ b
    · subst hz
      simp
    · have : N b z = 0 := hN.apply_eq_zero (fun h => hz (by rw [h]; simp))
      rw [this, mul_zero, ite_eq_right (fun h => hz h.2.symm)]
  · intro u _ hu
    rw [single_apply, ite_eq_right (fun h => hu h.2.symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ b) h

theorem mul_apply_swap_of_isLinePerm {g : GL (Fin r ⊕ Fin r) K} (hg : g ∈ StatedSp r K)
    {σ : Equiv.Perm (Fin r ⊕ Fin r)}
    (h : IsLinePerm σ (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) (x : Fin r ⊕ Fin r) :
    (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (σ x) x *
        (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (σ x.swap) x.swap =
      lineSign K x * lineSign K (σ x) := by
  have hσ := h.mem_signedPermGroup hg
  have hJ := congrFun (congrFun (mem_statedSp_iff.1 hg) x) x.swap
  rw [mul_apply, Finset.sum_eq_single (σ x.swap), mul_apply, Finset.sum_eq_single (σ x),
    transpose_apply] at hJ
  · rw [J_apply, J_apply, ite_eq_left (hσ x), ite_eq_left rfl] at hJ
    have e := lineSign_mul_self (K := K) (σ x)
    linear_combination (lineSign K (σ x)) * hJ -
      ((g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (σ x) x *
        (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (σ x.swap) x.swap) * e
  · intro z _ hz
    rw [transpose_apply, h.apply_eq_zero hz, zero_mul]
  · simp
  · intro z _ hz
    rw [h.apply_eq_zero hz, mul_zero]
  · simp

theorem apply_mul_inv_apply {g : GL (Fin r ⊕ Fin r) K} {σ : Equiv.Perm (Fin r ⊕ Fin r)}
    (h : IsLinePerm σ (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) (x : Fin r ⊕ Fin r) :
    (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (σ x) x * ((g⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) x (σ x) = 1 := by
  have hinv := h.inv
  have hmul : (((g⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) x x = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_apply_eq]
  rw [mul_apply, Finset.sum_eq_single (σ x)] at hmul
  · rw [mul_comm]
    exact hmul
  · intro z _ hz
    rw [h.apply_eq_zero hz, mul_zero]
  · simp

theorem conj_pairRootMat {g : GL (Fin r ⊕ Fin r) K} (hg : g ∈ StatedSp r K)
    {σ : Equiv.Perm (Fin r ⊕ Fin r)}
    (h : IsLinePerm σ (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    (a b : Fin r ⊕ Fin r) (t : K) :
    (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * pairRootMat K a b t *
        ((g⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      pairRootMat K (σ a) (σ b) ((g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (σ a) a *
        ((g⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) b (σ b) *
          t) := by
  have hσ := h.mem_signedPermGroup hg
  have hrel := mul_apply_swap_of_isLinePerm hg h
  have hinv := apply_mul_inv_apply h
  have hN : IsLinePerm σ⁻¹ ((g⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := h.inv
  have hMN : (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((g⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  set M := (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hMdef
  set N := ((g⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    with hNdef
  have hinvinv : ∀ x, σ⁻¹⁻¹ x = σ x := fun x => by rw [inv_inv]
  have hconj : ∀ (x y : Fin r ⊕ Fin r) (c : K),
      M * single x y c * N = single (σ x) (σ y) (M (σ x) x * c * N y (σ y)) := by
    intro x y c
    rw [isLinePerm_mul_single h, single_mul_isLinePerm hN, hinvinv]
  rw [pairRootMat, pairRootMat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hMN,
    Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  unfold rootNil
  by_cases hb : b = a.swap
  · have hb' : σ b = (σ a).swap := by rw [hb, hσ a]
    rw [ite_eq_left hb, ite_eq_left hb', hconj, smul_single, smul_single]
    congr 1
    simp only [smul_eq_mul]
    ring
  · have hb' : ¬σ b = (σ a).swap := fun h' => hb (by
      rw [← hσ a] at h'
      exact σ.injective h')
    rw [ite_eq_right hb, ite_eq_right hb', Matrix.mul_add, Matrix.add_mul, hconj, hconj,
      smul_add, smul_add]
    congr 1
    · rw [smul_single, smul_single]
      congr 1
      simp only [smul_eq_mul]
      ring
    · rw [smul_single, smul_single, hσ b, hσ a]
      congr 1
      simp only [smul_eq_mul]
      have h1 := hrel b
      have h2 := hrel a
      have h3 := hinv b
      have h4 := hinv a.swap
      rw [hσ b] at h1
      rw [hσ a] at h2 h4
      have e1 := lineSign_mul_self (K := K) a
      have e2 := lineSign_mul_self (K := K) b
      have e3 := lineSign_mul_self (K := K) (σ a)
      have e4 := lineSign_mul_self (K := K) (σ b)
      have hmb : M (σ b).swap b.swap = lineSign K b * lineSign K (σ b) * N b (σ b) := by
        refine mul_left_cancel₀ (h.apply_ne_zero b) ?_
        linear_combination h1 - lineSign K b * lineSign K (σ b) * h3
      have hna : N a.swap (σ a).swap = lineSign K a * lineSign K (σ a) * M (σ a) a := by
        refine mul_left_cancel₀ (show M (σ a).swap a.swap ≠ 0 by
          rw [← hσ a]; exact h.apply_ne_zero a.swap) ?_
        linear_combination h4 - lineSign K a * lineSign K (σ a) * h2 -
          lineSign K (σ a) * lineSign K (σ a) * e1 - e3
      rw [hmb, hna]
      set X := t * lineSign K (σ a) * lineSign K (σ b) * M (σ a) a * N b (σ b)
      linear_combination (-X * lineSign K b * lineSign K b) * e1 + (-X) * e2

theorem conj_pairRootElt (g : StatedSp r K) {σ : Equiv.Perm (Fin r ⊕ Fin r)}
    (h : IsLinePerm σ ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    {a b : Fin r ⊕ Fin r} (hab : a ≠ b) (t : K) :
    g * pairRootElt hab t * g⁻¹ = pairRootElt (σ.injective.ne hab)
      (((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (σ a) a *
        (((g⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) b (σ b) * t) :=
  statedSp_ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_pairRootElt,
      coe_pairRootElt, Subgroup.coe_inv]
    exact conj_pairRootMat g.2 h a b t)

theorem range_pairRootHom_congr {a b a' b' : Fin r ⊕ Fin r} (ha : a = a') (hb : b = b')
    (hab : a ≠ b) (hab' : a' ≠ b') : (pairRootHom K hab).range = (pairRootHom K hab').range := by
  subst ha
  subst hb
  rfl

theorem map_conj_range_pairRootHom (g : StatedSp r K) {σ : Equiv.Perm (Fin r ⊕ Fin r)}
    (h : IsLinePerm σ ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    {a b : Fin r ⊕ Fin r} (hab : a ≠ b) :
    (pairRootHom K hab).range.map (MulAut.conj g).toMonoidHom =
      (pairRootHom K (σ.injective.ne hab)).range := by
  set c := ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (σ a) a *
    (((g⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) b (σ b) with hc
  have hc0 : c ≠ 0 := by
    have hinv := (h.inv (g := (g : GL (Fin r ⊕ Fin r) K)))
    refine mul_ne_zero (h.apply_ne_zero a) ?_
    have := hinv.apply_ne_zero (σ b)
    rw [Subgroup.coe_inv]
    simpa using this
  ext x
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    refine ⟨Multiplicative.ofAdd (c * t.toAdd), ?_⟩
    change pairRootElt (σ.injective.ne hab) _ = g * pairRootElt hab t.toAdd * g⁻¹
    rw [conj_pairRootElt g h hab]
    rfl
  · rintro ⟨t, rfl⟩
    refine ⟨pairRootElt hab (c⁻¹ * t.toAdd), ⟨Multiplicative.ofAdd (c⁻¹ * t.toAdd), rfl⟩, ?_⟩
    change g * pairRootElt hab _ * g⁻¹ = pairRootElt (σ.injective.ne hab) t.toAdd
    rw [conj_pairRootElt g h hab, ← hc, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

theorem map_conj_rootSubgroup (g : StatedSp r K) {σ : Equiv.Perm (Fin r ⊕ Fin r)}
    (h : IsLinePerm σ ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    (α : Fin r → ℤ) :
    (rootSubgroup K α).map (MulAut.conj g).toMonoidHom = rootSubgroup K (epsAct σ α) := by
  have hσ := h.mem_signedPermGroup g.2
  rw [rootSubgroup, Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le fun p => ?_
    obtain ⟨⟨a, b⟩, hab, hroot⟩ := p
    rw [map_conj_range_pairRootHom g h hab]
    refine le_iSup_of_le ⟨(σ a, σ b), σ.injective.ne hab, ?_⟩ le_rfl
    rw [← epsAct_rootVec hσ, ← hroot]
  · refine iSup_le fun q => ?_
    obtain ⟨⟨c, d⟩, hcd, hroot⟩ := q
    have hab : σ⁻¹ c ≠ σ⁻¹ d := σ⁻¹.injective.ne hcd
    have hroot' : rootVec (σ⁻¹ c) (σ⁻¹ d) = α := by
      have := epsAct_rootVec (inv_mem hσ) c d
      rw [hroot, epsAct_inv_epsAct hσ] at this
      exact this.symm
    have hc : σ (σ⁻¹ c) = c := by simp
    have hd : σ (σ⁻¹ d) = d := by simp
    rw [range_pairRootHom_congr hc.symm hd.symm hcd (σ.injective.ne hab),
      ← map_conj_range_pairRootHom g h hab]
    exact le_iSup_of_le
      (ι := {p : (Fin r ⊕ Fin r) × (Fin r ⊕ Fin r) // p.1 ≠ p.2 ∧ rootVec p.1 p.2 = α})
      ⟨(σ⁻¹ c, σ⁻¹ d), hab, hroot'⟩ le_rfl

theorem isLinePerm_dotW (w : signedPermGroup r) :
    IsLinePerm (w : Equiv.Perm (Fin r ⊕ Fin r))
      (((dotW K w : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  rw [coe_dotW]
  exact isLinePerm_signedPerm _ (dotSign_ne_zero _)

theorem exists_torus_of_isLinePerm {w : signedPermGroup r} {g : StatedSp r K}
    (h : IsLinePerm (w : Equiv.Perm (Fin r ⊕ Fin r))
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) :
    ∃ t ∈ torus r K, g = dotW K w * t := by
  set t := (dotW K w)⁻¹ * g with ht
  have hdot := isLinePerm_dotW (K := K) w
  have h1 : IsLinePerm 1 (((t : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    have := hdot.inv.mul h
    rw [inv_mul_cancel] at this
    rw [ht, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv]
    exact this
  set D := (((t : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hD
  have hrel := mul_apply_swap_of_isLinePerm t.2 h1
  have hd0 : ∀ x, D x x ≠ 0 := fun x => h1.apply_ne_zero x
  set s : Fin r → Kˣ := fun i => Units.mk0 (D (Sum.inl i) (Sum.inl i)) (hd0 _)
  refine ⟨t, ⟨s, statedSp_ext ?_⟩, by rw [ht, mul_inv_cancel_left]⟩
  rw [coe_torusHom]
  ext y z
  by_cases hyz : y = z
  · subst hyz
    rw [diagonal_apply_eq]
    rcases y with i | i
    · rfl
    · have := hrel (Sum.inl i)
      simp only [Equiv.Perm.one_apply, Sum.swap_inl, lineSign, Sum.elim_inl, mul_one] at this
      simp only [Sum.elim_inr, s, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [eq_inv_of_mul_eq_one_right this]
  · rw [diagonal_apply_ne _ hyz]
    exact (h1.apply_eq_zero hyz).symm

theorem isLinePerm_torusHom' {t : StatedSp r K} (ht : t ∈ torus r K) :
    IsLinePerm 1 (((t : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  obtain ⟨s, rfl⟩ := ht
  exact isLinePerm_torusHom s

variable (K) in
@[expose] def sl2Up (t : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, t; 0, 1], by simp [det_fin_two_of]⟩

variable (K) in
@[expose] def sl2Low (t : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 0; t, 1], by simp [det_fin_two_of]⟩

theorem coe_sl2Up_inv (t : K) :
    (((sl2Up K t)⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![1, -t; 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  change adjugate !![1, t; 0, 1] = _
  rw [adjugate_fin_two_of]
  simp

theorem coe_sl2Low_inv (t : K) :
    (((sl2Low K t)⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![1, 0; -t, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  change adjugate !![1, 0; t, 1] = _
  rw [adjugate_fin_two_of]
  simp

theorem sl2Up_mul_sl2Low_mul_sl2Up :
    sl2Up K 1 * sl2Low K (-1) * sl2Up K 1 = sl2W⁻¹ := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_sl2W_inv]
  fin_cases i <;> fin_cases j <;> simp [sl2Up, sl2Low, mul_apply, Fin.sum_univ_two]

theorem pairMat_up {ι : Type*} [DecidableEq ι] {a b : ι} (hab : a ≠ b) (t : K) :
    pairMat a b !![1, t; 0, 1] = 1 + single a b t := by
  ext x y
  simp only [pairMat, Matrix.of_apply, Matrix.add_apply, single_apply, one_apply]
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hya : y = a <;>
    by_cases hyb : y = b <;> simp_all [eq_comm]

theorem pairMat_low {ι : Type*} [DecidableEq ι] {a b : ι} (hab : a ≠ b) (t : K) :
    pairMat a b !![1, 0; t, 1] = 1 + single b a t := by
  ext x y
  simp only [pairMat, Matrix.of_apply, Matrix.add_apply, single_apply, one_apply]
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hya : y = a <;>
    by_cases hyb : y = b <;> simp_all [eq_comm]

theorem pairRootElt_long (i : Fin r) (t : K) :
    pairRootElt (Sum.inl_ne_inr : (Sum.inl i : Fin r ⊕ Fin r) ≠ Sum.inr i) t = lam i (sl2Up K t) :=
  statedSp_ext (by
    rw [coe_pairRootElt, pairRootMat_inl_inr_self, coe_lam]
    change _ = pairMat _ _ !![1, t; 0, 1]
    rw [pairMat_up Sum.inl_ne_inr, smul_single, smul_eq_mul, mul_one])

theorem pairRootElt_long' (i : Fin r) (t : K) :
    pairRootElt (Sum.inr_ne_inl : (Sum.inr i : Fin r ⊕ Fin r) ≠ Sum.inl i) t =
      lam i (sl2Low K t) :=
  statedSp_ext (by
    rw [coe_pairRootElt, pairRootMat_inr_inl_self, coe_lam]
    change _ = pairMat _ _ !![1, 0; t, 1]
    rw [pairMat_low Sum.inl_ne_inr, smul_single, smul_eq_mul, mul_one])

theorem fromBlocks_one_add_single {i j k l : Fin r} (c d : K) :
    fromBlocks (1 + single i j c) 0 0 (1 + single k l d) =
      (1 + single (Sum.inl i) (Sum.inl j) c + single (Sum.inr k) (Sum.inr l) d :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  ext (x | x) (y | y) <;> simp [single_apply, one_apply]

theorem pairRootElt_short {i j : Fin r} (hij : i ≠ j) (t : K) :
    pairRootElt (fun h => hij (Sum.inl_injective h) : (Sum.inl i : Fin r ⊕ Fin r) ≠ Sum.inl j) t =
      rho i j hij (sl2Up K t) :=
  statedSp_ext (by
    rw [coe_pairRootElt, pairRootMat_inl_inl, coe_rho', coe_sl2Up_inv]
    change _ = fromBlocks (pairMat i j !![1, t; 0, 1]) 0 0 (pairMat i j !![1, -t; 0, 1]ᵀ)
    rw [pairMat_up hij, show (!![1, -t; 0, 1] : Matrix (Fin 2) (Fin 2) K)ᵀ = !![1, 0; -t, 1] by
      ext a b; fin_cases a <;> fin_cases b <;> rfl, pairMat_low hij, fromBlocks_one_add_single]
    simp only [smul_single, smul_eq_mul, mul_one, sub_eq_add_neg, single_neg])

theorem pairRootElt_short' {i j : Fin r} (hij : i ≠ j) (t : K) :
    pairRootElt (fun h => hij (Sum.inl_injective h).symm :
      (Sum.inl j : Fin r ⊕ Fin r) ≠ Sum.inl i) t = rho i j hij (sl2Low K t) :=
  statedSp_ext (by
    rw [coe_pairRootElt, pairRootMat_inl_inl, coe_rho', coe_sl2Low_inv]
    change _ = fromBlocks (pairMat i j !![1, 0; t, 1]) 0 0 (pairMat i j !![1, 0; -t, 1]ᵀ)
    rw [pairMat_low hij, show (!![1, 0; -t, 1] : Matrix (Fin 2) (Fin 2) K)ᵀ = !![1, -t; 0, 1] by
      ext a b; fin_cases a <;> fin_cases b <;> rfl, pairMat_up hij, fromBlocks_one_add_single]
    simp only [smul_single, smul_eq_mul, mul_one, sub_eq_add_neg, single_neg])

theorem weylRep_eq_pair (k : Fin r) {b : Fin r ⊕ Fin r} (hb : simpleSnd k = b)
    (hkb : Sum.inl k ≠ b) :
    weylRep K k = pairRootElt hkb 1 * pairRootElt hkb.symm (-1) * pairRootElt hkb 1 := by
  subst hb
  rfl

theorem isLinePerm_weylRep (k : Fin r) :
    IsLinePerm (simpleRefl r k) (((weylRep K k : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  by_cases h : (k : ℕ) + 1 < r
  · set k' : Fin r := ⟨k + 1, h⟩
    have hkk' : k ≠ k' := fun e => by
      have := congrArg Fin.val e
      simp [k'] at this
    have hsnd : simpleSnd k = Sum.inl k' := by
      unfold simpleSnd
      rw [dite_eq_left h]
    rw [weylRep_eq_pair k hsnd (fun e => hkk' (Sum.inl_injective e)), pairRootElt_short hkk',
      pairRootElt_short' hkk', ← map_mul, ← map_mul, sl2Up_mul_sl2Low_mul_sl2Up, map_inv,
      Subgroup.coe_inv]
    have := (isLinePerm_rho_sl2W (k := K) hkk').inv
    unfold simpleRefl
    rw [dite_eq_left h]
    convert this using 1
    rw [Equiv.Perm.sumCongr_inv, Equiv.swap_inv]
  · have hsnd : simpleSnd k = Sum.inr k := by
      unfold simpleSnd
      rw [dite_eq_right h]
    rw [weylRep_eq_pair k hsnd Sum.inl_ne_inr, pairRootElt_long, pairRootElt_long', ← map_mul,
      ← map_mul, sl2Up_mul_sl2Low_mul_sl2Up, map_inv, Subgroup.coe_inv]
    have := (isLinePerm_lam_sl2W (k := K) k).inv
    unfold simpleRefl
    rw [dite_eq_right h]
    convert this using 1
    rw [Equiv.swap_inv]

theorem isFlagUpper_pairRootMat {a b : Fin r ⊕ Fin r}
    (hab : (flagOrder r a : ℕ) < flagOrder r b) (t : K) : IsFlagUpper (pairRootMat K a b t) := by
  intro x y hxy
  have hne : y ≠ x := fun h => by rw [h] at hxy; exact lt_irrefl _ hxy
  rw [pairRootMat, Matrix.add_apply, one_apply_ne hne, zero_add, Matrix.smul_apply, rootNil]
  have h1 : ¬(a = y ∧ b = x) := by
    rintro ⟨rfl, rfl⟩
    exact lt_asymm hab hxy
  split_ifs with h
  · simp [h1]
  · have h2 : ¬(b.swap = y ∧ a.swap = x) := by
      rintro ⟨rfl, rfl⟩
      rw [flagOrder_swap', flagOrder_swap'] at hxy
      have := (flagOrder r a).2
      have := (flagOrder r b).2
      omega
    simp [h1, h2]

theorem rootSubgroup_le_borelSubgroup {α : Fin r → ℤ} (hα : α ∈ posRoots r) :
    rootSubgroup K α ≤ borelSubgroup r K := by
  refine iSup_le fun p => ?_
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := p
  rintro _ ⟨t, rfl⟩
  rw [mem_borelSubgroup_iff_isFlagUpper]
  exact isFlagUpper_pairRootMat ((rootVec_mem_posRoots_iff hab).mp hα) _

theorem root_transport :
    (∀ (w : signedPermGroup r) (α : Fin r → ℤ),
      (rootSubgroup K α).map (MulAut.conj (dotW K w)).toMonoidHom =
        rootSubgroup K (epsAct (w : Equiv.Perm (Fin r ⊕ Fin r)) α)) ∧
    (∀ t ∈ torus r K, ∀ α : Fin r → ℤ,
      (rootSubgroup K α).map (MulAut.conj t).toMonoidHom = rootSubgroup K α) ∧
    (∀ (w : signedPermGroup r) (g : StatedSp r K), IsLinePerm (w : Equiv.Perm (Fin r ⊕ Fin r))
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) →
      ∃ t ∈ torus r K, g = dotW K w * t) ∧
    (∀ k : Fin r, IsLinePerm (simpleRefl r k)
      (((weylRep K k : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) ∧
    (∀ α ∈ posRoots r, rootSubgroup K α ≤ borelSubgroup r K) := by
  refine ⟨fun w α => map_conj_rootSubgroup _ (isLinePerm_dotW w) α,
    fun t ht α => (map_conj_rootSubgroup t (isLinePerm_torusHom' ht) α).trans (by rw [epsAct_one]),
    fun w g h => exists_torus_of_isLinePerm h, isLinePerm_weylRep,
    fun α hα => rootSubgroup_le_borelSubgroup hα⟩

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
