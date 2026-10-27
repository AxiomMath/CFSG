module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSelfE

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Sp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff
  lam coe_lam pairMat pairMat_mul pairMat_one sl2Diag coe_sl2Diag)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (invSMulOp)
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj
open scoped commutatorElement MatrixGroups

variable {K : Type} [Field K]

section Pair

variable {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ι}

theorem blockDiag_pow {J : Finset ι} {M : Matrix ι ι K} (hM : BlockDiag J M) (k : ℕ) :
    BlockDiag J (M ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero]
    exact blockDiag_of_pairSupp (pairSupp_one J)
  | succ k ih => rw [pow_succ]; exact blockDiag_mul ih hM

omit [Fintype ι] in
theorem pairBlock_one (hab : a ≠ b) : pairBlock a b (1 : Matrix ι ι K) = 1 := by
  rw [← pairMat_one hab, pairBlock_pairMat hab]

theorem pairBlock_pow (hab : a ≠ b) {M : Matrix ι ι K} (hM : BlockDiag {a, b} M) (k : ℕ) :
    pairBlock a b (M ^ k) = pairBlock a b M ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, pairBlock_one hab]
  | succ k ih => rw [pow_succ, pow_succ, pairBlock_mul hab (blockDiag_pow hM k), ih]

theorem three_pair_scalar [Finite K] (h3 : Nat.card K = 3) (hab : a ≠ b) {D Di : Matrix ι ι K}
    (hDDi : D * Di = 1) (hDiD : Di * D = 1) (hD : BlockDiag {a, b} D)
    (hodd : ∀ X Xi : Matrix (Fin 2) (Fin 2) K, X.det = 1 → X * Xi = 1 →
      ∃ k, Odd k ∧ (D * pairMat a b X * Di * pairMat a b Xi) ^ k = 1) :
    D a b = 0 ∧ D b a = 0 ∧ D a a = D b b := by
  have hDi := blockDiag_of_mul_eq_one hD hDDi hDiD
  set P := pairBlock a b D with hP
  set Pi := pairBlock a b Di with hPi
  have hPP : P * Pi = 1 := by
    rw [hP, hPi, ← pairBlock_mul hab hD, hDDi, pairBlock_one hab]
  have htr : ∀ X Xi : Matrix (Fin 2) (Fin 2) K, X.det = 1 → X * Xi = 1 →
      tr2 (P * X * Pi * Xi) = 2 := by
    intro X Xi hX hXXi
    obtain ⟨k, hk, hz⟩ := hodd X Xi hX hXXi
    have hpX := blockDiag_of_pairSupp (pairSupp_pairMat hab X)
    have hpXi := blockDiag_of_pairSupp (pairSupp_pairMat hab Xi)
    have hzd : BlockDiag {a, b} (D * pairMat a b X * Di * pairMat a b Xi) :=
      blockDiag_mul (blockDiag_mul (blockDiag_mul hD hpX) hDi) hpXi
    have hblk : pairBlock a b (D * pairMat a b X * Di * pairMat a b Xi) = P * X * Pi * Xi := by
      rw [pairBlock_mul hab (blockDiag_mul (blockDiag_mul hD hpX) hDi),
        pairBlock_mul hab (blockDiag_mul hD hpX), pairBlock_mul hab hD, pairBlock_pairMat hab,
        pairBlock_pairMat hab]
    have hXi : Xi * X = 1 := by
      have : X⁻¹ = Xi := Matrix.inv_eq_right_inv hXXi
      rw [← this, Matrix.nonsing_inv_mul _ (by rw [hX]; exact isUnit_one)]
    have hdet : (P * X * Pi * Xi).det = 1 := by
      have e1 := congrArg Matrix.det hPP
      have e2 := congrArg Matrix.det hXXi
      rw [det_mul, det_one] at e1 e2
      rw [det_mul, det_mul, det_mul]
      linear_combination X.det * Xi.det * e1 + e2
    refine trace_eq_two_of_odd h3 hdet hk ?_
    rw [← hblk, ← pairBlock_pow hab hzd, hz, pairBlock_one hab]
  have ht1 := htr !![1, 1; 0, 1] !![1, -1; 0, 1] (by simp [det_fin_two_of])
    (by ext s t; fin_cases s <;> fin_cases t <;> simp [Matrix.mul_apply, Fin.sum_univ_two])
  have ht2 := htr !![1, 0; 1, 1] !![1, 0; -1, 1] (by simp [det_fin_two_of])
    (by ext s t; fin_cases s <;> fin_cases t <;> simp [Matrix.mul_apply, Fin.sum_univ_two])
  have ht3 := htr !![0, 1; -1, 0] !![0, -1; 1, 0] (by simp [det_fin_two_of])
    (by ext s t; fin_cases s <;> fin_cases t <;> simp [Matrix.mul_apply, Fin.sum_univ_two])
  obtain ⟨h01, h10, h00⟩ := scalar_of_commutator_traces hPP ht1 ht2 ht3
  exact ⟨h01, h10, h00⟩

end Pair

variable {r : ℕ}

theorem exists_odd_pow_commutator [Finite K]
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {B : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range ≤
      B)
    {t : MulAut (StatedProj (StatedSp r K))} {D : gsp r K} (hy : conjAut r K D ∈ oddCoreIn B t)
    {g : StatedSp r K}
    (hg : conjProjH (StatedSp r K) g ∈
      centralizer ({t} : Set (MulAut (StatedProj (StatedSp r K))))) :
    ∃ k, Odd k ∧
      (conjSp r K D g * g⁻¹) ^ k ∈ (StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K) := by
  have hc := commutator_mem_oddCoreIn hy ⟨hB ⟨_, rfl⟩, hg⟩
  have hodd := odd_orderOf_of_mem_oddCoreIn hc
  change Odd (orderOf (conjAut r K D * conjProjH (StatedSp r K) g * (conjAut r K D)⁻¹ *
    (conjProjH (StatedSp r K) g)⁻¹)) at hodd
  refine ⟨_, hodd, ?_⟩
  have e : conjAut r K D * conjProjH (StatedSp r K) g * (conjAut r K D)⁻¹ *
      (conjProjH (StatedSp r K) g)⁻¹ = conjProjH (StatedSp r K) (conjSp r K D g * g⁻¹) := by
    rw [conjAut_mul_conjProjH, map_mul, map_inv]
  rw [e] at hodd ⊢
  have h1 : conjProjH (StatedSp r K) ((conjSp r K D g * g⁻¹) ^
      orderOf (conjProjH (StatedSp r K) (conjSp r K D g * g⁻¹))) = 1 := by
    rw [map_pow, pow_orderOf_eq_one]
  exact (QuotientGroup.eq_one_iff _).1 (hinj (by rw [map_one]; exact h1))

abbrev lrInvGsp (r : ℕ) (K : Type) [Field K] (i₀ : Fin r) : gsp r K :=
  ⟨lrInv K i₀, statedSp_le_gsp (lrInv K i₀).2⟩

theorem coe_lrInvGsp (i₀ : Fin r) : ((lrInvGsp r K i₀ : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (2 : K) • offInd K (lrPair i₀) - 1 :=
  coe_lrInv i₀

theorem offInd_mulVec_apply {ι : Type} [Fintype ι] [DecidableEq ι] (J : Finset ι)
    (v : ι → K) (x : ι) : (offInd K J *ᵥ v) x = if x ∈ J then 0 else v x := by
  rw [offInd, mulVec_diagonal]
  split_ifs <;> simp

theorem mem_VPl_lrInv (h2 : (2 : K) ≠ 0) (i₀ : Fin r) {v : Fin r ⊕ Fin r → K} :
    v ∈ VPl (lrInvGsp r K i₀) 1 ↔ ∀ x ∈ lrPair i₀, v x = 0 := by
  rw [mem_eigenPlus one_ne_zero, coe_lrInvGsp, one_smul, sub_mulVec, smul_mulVec, one_mulVec,
    sub_eq_iff_eq_add, ← two_smul K v]
  constructor
  · intro h x hx
    have := congrFun (smul_right_injective _ h2 h) x
    rw [offInd_mulVec_apply] at this
    simp only [hx, ↓reduceIte] at this
    exact this.symm
  · intro h
    congr 1
    ext x
    rw [offInd_mulVec_apply]
    split_ifs with hx
    · exact (h x hx).symm
    · rfl

theorem mem_VMl_lrInv (h2 : (2 : K) ≠ 0) (i₀ : Fin r) {v : Fin r ⊕ Fin r → K} :
    v ∈ VMl (lrInvGsp r K i₀) 1 ↔ ∀ x, x ∉ lrPair i₀ → v x = 0 := by
  rw [mem_eigenMinus one_ne_zero, coe_lrInvGsp, sub_mulVec, smul_mulVec, one_mulVec, neg_smul,
    one_smul, sub_eq_neg_self, smul_eq_zero, or_iff_right h2]
  constructor
  · intro h x hx
    have := congrFun h x
    rw [offInd_mulVec_apply] at this
    simpa only [hx, ↓reduceIte, Pi.zero_apply] using this
  · intro h
    ext x
    rw [offInd_mulVec_apply, Pi.zero_apply]
    split_ifs with hx
    · rfl
    · exact h x hx

theorem mulVec_eq_of_pairBlock {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ι} (hab : a ≠ b)
    {D : Matrix ι ι K} (hD : BlockDiag {a, b} D) (h1 : D a b = 0) (h2 : D b a = 0)
    (h3 : D a a = D b b) {v : ι → K} (hv : ∀ x, x ∉ ({a, b} : Finset ι) → v x = 0) :
    D *ᵥ v = D a a • v := by
  have h0 := blockDiag_iff.1 hD
  ext x
  rw [mulVec, dotProduct, Finset.sum_eq_add a b hab (fun y _ hy => by
    rw [hv y (by simp [hy.1, hy.2]), mul_zero]) (by simp) (by simp), Pi.smul_apply, smul_eq_mul]
  by_cases hxa : x = a
  · subst hxa
    rw [h1, zero_mul, add_zero]
  · by_cases hxb : x = b
    · subst hxb
      rw [h2, zero_mul, zero_add, h3]
    · have hx : x ∉ ({a, b} : Finset ι) := by simp [hxa, hxb]
      rw [h0 x a (iff_of_false hx (by simp)), h0 x b (iff_of_false hx (by simp)), hv x hx]
      ring

theorem conjAut_statedSp (g : StatedSp r K) :
    conjAut r K ⟨g, statedSp_le_gsp g.2⟩ = conjProjH (StatedSp r K) g := by
  ext x
  obtain ⟨h, rfl⟩ := proj_surjective x
  rw [conjAut_proj]
  change proj r K (conjSp r K ⟨g, statedSp_le_gsp g.2⟩ h) = proj r K g * proj r K h *
    (proj r K g)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem commute_offInd_of_pairSupp {ι : Type} [Fintype ι] [DecidableEq ι] {J J' : Finset ι}
    (hJJ' : Disjoint J J') {M : Matrix ι ι K} (hM : PairSupp J M) :
    M * offInd K J' = offInd K J' * M := by
  have h0 := pairSupp_iff.1 hM
  ext x y
  rw [mul_offInd_apply, offInd_mul_apply]
  by_cases hxy : x ∈ J ∧ y ∈ J
  · have hx : x ∉ J' := Finset.disjoint_left.1 hJJ' hxy.1
    have hy : y ∉ J' := Finset.disjoint_left.1 hJJ' hxy.2
    simp [hx, hy]
  · rw [h0 x y (by tauto)]
    by_cases h : x = y
    · subst h
      rfl
    · simp [h]

theorem pairSupp_pow {ι : Type} [Fintype ι] [DecidableEq ι] {J : Finset ι} {M : Matrix ι ι K}
    (hM : PairSupp J M) (k : ℕ) : PairSupp J (M ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact pairSupp_one J
  | succ k ih => rw [pow_succ]; exact pairSupp_mul ih hM

theorem eq_one_of_scalar_pairSupp {ι : Type} [Fintype ι] [DecidableEq ι] {J : Finset ι} {x : ι}
    (hx : x ∉ J) {c : K} (h : PairSupp J (c • (1 : Matrix ι ι K))) : c = 1 := by
  have := pairSupp_iff.1 h x x (Or.inl hx)
  simpa using this

theorem exists_ne_index (hr : 2 ≤ r) (i₀ : Fin r) : ∃ j : Fin r, j ≠ i₀ := by
  by_cases h : i₀ = ⟨0, by omega⟩
  · exact ⟨⟨1, by omega⟩, by rw [h]; simp [Fin.ext_iff]⟩
  · exact ⟨⟨0, by omega⟩, Ne.symm h⟩

theorem lrPair_scalar_three [Finite K] (h3 : Nat.card K = 3) (hr : 2 ≤ r)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {B : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range ≤
      B)
    {t : MulAut (StatedProj (StatedSp r K))} {D : gsp r K} (hy : conjAut r K D ∈ oddCoreIn B t)
    (j : Fin r)
    (hD : BlockDiag (lrPair j)
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    (ht : ∀ X : SL(2, K), conjProjH (StatedSp r K) (lam j X) ∈
      centralizer ({t} : Set (MulAut (StatedProj (StatedSp r K))))) :
    ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
        (Sum.inl j) (Sum.inr j) = 0 ∧
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
        (Sum.inr j) (Sum.inl j) = 0 ∧
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
        (Sum.inl j) (Sum.inl j) =
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
        (Sum.inr j) (Sum.inr j) := by
  obtain ⟨j', hj'⟩ := exists_ne_index hr j
  have hx : (Sum.inl j' : Fin r ⊕ Fin r) ∉ lrPair j := by simp [hj']
  set M := ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  set Mi := (((D : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hMi
  have hMMi : M * Mi = 1 := by rw [hM, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMiM : Mi * M = 1 := by rw [hM, hMi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine three_pair_scalar h3 Sum.inl_ne_inr hMMi hMiM hD fun X Xi hX hXXi => ?_
  obtain ⟨x, hxX⟩ : ∃ x : SL(2, K), (x : Matrix (Fin 2) (Fin 2) K) = X := ⟨⟨X, hX⟩, rfl⟩
  have hxi : ((x⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = Xi := by
    have h1 : X * ((x⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← hxX, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have h2 : Xi * X = 1 := by
      have : X⁻¹ = Xi := Matrix.inv_eq_right_inv hXXi
      rw [← this, Matrix.nonsing_inv_mul _ (by rw [hX]; exact isUnit_one)]
    calc ((x⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
        (Xi * X) * ((x⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) := by rw [h2, Matrix.one_mul]
      _ = Xi := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  obtain ⟨k, hk, hz⟩ := exists_odd_pow_commutator hinj hB hy (ht x)
  refine ⟨k, hk, ?_⟩
  obtain ⟨c, hc⟩ := hz
  have hmat : (((conjSp r K D (lam j x) * (lam j x)⁻¹) ^ k : StatedSp r K) :
      GL (Fin r ⊕ Fin r) K).val = (M * pairMat (Sum.inl j) (Sum.inr j) X * Mi *
        pairMat (Sum.inl j) (Sum.inr j) Xi) ^ k := by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_mul, Units.val_mul, coe_conjSp,
      Units.val_mul, Units.val_mul, coe_lam, ← map_inv, coe_lam, hxX, hxi]
  have hS : PairSupp (lrPair j) ((M * pairMat (Sum.inl j) (Sum.inr j) X * Mi *
      pairMat (Sum.inl j) (Sum.inr j) Xi) ^ k) :=
    pairSupp_pow (pairSupp_mul (pairSupp_conj hMMi hMiM hD (pairSupp_pairMat Sum.inl_ne_inr X))
      (pairSupp_pairMat Sum.inl_ne_inr Xi)) k
  have hc' : (GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c : GL (Fin r ⊕ Fin r) K).val =
      (M * pairMat (Sum.inl j) (Sum.inr j) X * Mi * pairMat (Sum.inl j) (Sum.inr j) Xi) ^ k := by
    rw [← hmat]
    exact congrArg Units.val hc
  rw [GeneralLinearGroup.coe_scalar, scalar_apply, ← Matrix.smul_one_eq_diagonal] at hc'
  rw [← hc'] at hS ⊢
  rw [eq_one_of_scalar_pairSupp hx hS, one_smul]

theorem lrInv_mul_self (i₀ : Fin r) : lrInv K i₀ * lrInv K i₀ = 1 := by
  rw [lrInv, ← map_mul, ← map_mul, neg_one_mul, neg_neg, map_one, map_one]

theorem lrInv_apply_inl (i₀ j : Fin r) :
    (((lrInv K i₀ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (Sum.inl j) (Sum.inl j) =
      if j = i₀ then -1 else 1 := by
  rw [coe_lrInv, Matrix.sub_apply, Matrix.smul_apply, offInd_apply, one_apply_eq]
  by_cases hj : j = i₀
  · simp [hj, lrPair]
  · simp [hj, lrPair]
    norm_num

theorem lam_commute_lrInv {i₀ j : Fin r} (hj : j ≠ i₀) (X : SL(2, K)) :
    lam j X * lrInv K i₀ = lrInv K i₀ * lam j X := by
  apply statedSp_ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_lrInv, coe_lam, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul, commute_offInd_of_pairSupp (J := lrPair j) ?_
      (pairSupp_pairMat Sum.inl_ne_inr _)]
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [lrPair, Finset.mem_insert, Finset.mem_singleton] at hx hx'
  rcases hx with rfl | rfl <;> rcases hx' with h | h <;> simp_all

theorem lrInv_oddCoreIn_eq_bot_three [Finite K] (h3 : Nat.card K = 3) (hr : 2 ≤ r)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {B : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range ≤
      B) (i₀ : Fin r) :
    oddCoreIn B (conjAut r K (lrInvGsp r K i₀)) = ⊥ := by
  have : Fintype K := Fintype.ofFinite K
  have hp3 : (Nat.card K).Prime := by rw [h3]; norm_num
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_three h3
  have hK : ringChar K ≠ 2 := fun h => h2 (by
    have := ringChar.spec K 2
    exact_mod_cast (this.2 (by rw [h])))
  set U := ((lrInvGsp r K i₀ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    with hU
  have hUU : U * U = ((1 : K) ^ 2) • 1 := by
    rw [one_pow, one_smul]
    change (((lrInv K i₀ * lrInv K i₀ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1
    rw [lrInv_mul_self]
    rfl
  have hUJ : Uᵀ * formJ r K * U = ((1 : K) ^ 2) • formJ r K := by
    rw [one_pow, one_smul]
    exact mem_statedSp_iff.1 (lrInv K i₀).2
  obtain ⟨j₀, hj₀⟩ := exists_ne_index hr i₀
  have hAns : ∀ c : Kˣ, (lrInvGsp r K i₀ : GL (Fin r ⊕ Fin r) K) ≠
      GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
    intro c hc
    have e1 := congrArg (fun g : GL (Fin r ⊕ Fin r) K => (g : Matrix (Fin r ⊕ Fin r)
      (Fin r ⊕ Fin r) K) (Sum.inl i₀) (Sum.inl i₀)) hc
    have e2 := congrArg (fun g : GL (Fin r ⊕ Fin r) K => (g : Matrix (Fin r ⊕ Fin r)
      (Fin r ⊕ Fin r) K) (Sum.inl j₀) (Sum.inl j₀)) hc
    simp only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq] at e1 e2
    change (((lrInv K i₀ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (Sum.inl i₀) (Sum.inl i₀) = _ at e1
    change (((lrInv K i₀ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (Sum.inl j₀) (Sum.inl j₀) = _ at e2
    rw [lrInv_apply_inl] at e1 e2
    simp only [hj₀, ↓reduceIte] at e1 e2
    exact h2 (by linear_combination e2 - e1)
  have ht : conjAut r K (lrInvGsp r K i₀) = conjProjH (StatedSp r K) (lrInv K i₀) :=
    conjAut_statedSp _
  have hcent : ∀ j : Fin r, (∀ X : SL(2, K), lam j X * lrInv K i₀ = lrInv K i₀ * lam j X) →
      ∀ X : SL(2, K), conjProjH (StatedSp r K) (lam j X) ∈
        centralizer ({conjAut r K (lrInvGsp r K i₀)} : Set _) := by
    intro j hj X
    rw [mem_centralizer_singleton_iff, ht, ← map_mul, ← map_mul, hj X]
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  have hoddy := odd_orderOf_of_mem_oddCoreIn hy
  have hyt := commute_of_mem_oddCoreIn hy
  obtain ⟨D, τ, rfl⟩ := CatalogueBSymplecticRepresentation.automorphism_standard hK hr y
  have hτ : τ = 1 := ringEquiv_eq_one_of_prime_card hp3 τ
  subst hτ
  rw [map_one, mul_one] at hy hoddy hyt ⊢
  obtain ⟨D', -, hD'D, hD'U⟩ := exists_commute_of_odd (by omega) one_ne_zero
    (by rw [← hU]; simpa using hUU) hyt hoddy
  rw [← hD'D] at hy hoddy ⊢
  set Dm := ((D' : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hDm
  have hbd : BlockDiag (lrPair i₀) Dm := blockDiag_of_commute_lrInv h2 i₀ hD'U
  obtain ⟨p1, p2, p3⟩ := lrPair_scalar_three h3 hr hinj hB hy i₀ hbd
    (hcent i₀ fun X => longRoot_commute i₀ _ ⟨X, rfl⟩)
  have hMe : ∀ v ∈ VMl (lrInvGsp r K i₀) 1, ∃ μ : K, Dm *ᵥ v = μ • v := fun v hv =>
    ⟨_, mulVec_eq_of_pairBlock Sum.inl_ne_inr hbd p1 p2 p3 ((mem_VMl_lrInv h2 i₀).1 hv)⟩
  have hPe : ∀ v ∈ VPl (lrInvGsp r K i₀) 1, ∃ μ : K, Dm *ᵥ v = μ • v := by
    rcases Nat.lt_or_ge r 3 with hr3 | hr3
    ·
      have hcompl : ∀ x : Fin r ⊕ Fin r, x ∈ lrPair j₀ ↔ x ∉ lrPair i₀ := by
        have hk : ∀ k : Fin r, k = i₀ ∨ k = j₀ := by
          intro k
          by_contra h
          push Not at h
          have h1 := Fin.val_ne_of_ne h.1
          have h2' := Fin.val_ne_of_ne h.2
          have h3' := Fin.val_ne_of_ne hj₀
          have := k.2
          have := i₀.2
          have := j₀.2
          omega
        intro x
        rcases x with k | k <;> rcases hk k with rfl | rfl <;> simp [lrPair, hj₀, Ne.symm hj₀]
      have hbd' : BlockDiag (lrPair j₀) Dm := by
        rw [blockDiag_iff] at hbd ⊢
        intro x y hxy
        exact hbd x y (by rw [hcompl, hcompl] at hxy; tauto)
      obtain ⟨q1, q2, q3⟩ := lrPair_scalar_three h3 hr hinj hB hy j₀ hbd'
        (hcent j₀ fun X => lam_commute_lrInv hj₀ X)
      intro v hv
      refine ⟨_, mulVec_eq_of_pairBlock Sum.inl_ne_inr hbd' q1 q2 q3 fun x hx => ?_⟩
      exact (mem_VPl_lrInv h2 i₀).1 hv x (by rw [hcompl] at hx; tauto)
    ·
      have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
      have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
      have hJA : Uᵀ * formJ r K = formJ r K * U :=
        transpose_mul_formJ (by norm_num) hUJ hUU
      have hAA' := linA_mul_self hUU
      have hTB : ∀ v w, pairedSympForm K r (invSMulOp 1 ((linA (lrInvGsp r K i₀) :
          LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
            Module.End K (Fin r ⊕ Fin r → K)) v)
          (invSMulOp 1 ((linA (lrInvGsp r K i₀) : LinearMap.GeneralLinearGroup K
            (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) w) =
            pairedSympForm K r v w := by
        intro v w
        simp only [invSMulOp, inv_one, one_smul, linA_apply]
        rw [form_similitude hUJ, one_pow, one_mul]
      have hAns' : ∀ c : K, ((linA (lrInvGsp r K i₀) : LinearMap.GeneralLinearGroup K
          (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) ≠ c • 1 :=
        CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hAns
      obtain ⟨hPne, -⟩ := UnitaryHigher.eigen_ne_bot h2 one_ne_zero hAA' hAns'
      obtain ⟨horth, haltP, -, hndP, -, e, he⟩ := UnitaryHigher.exists_bilin_split_equiv h2
        pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate one_ne_zero hAA' hTB
      set Ψ := (spCentEquiv (lrInvGsp r K i₀)).trans e with hΨ
      have hres : ∀ g : spCent r K (lrInvGsp r K i₀), (Ψ g).2 = 1 ↔
          ∀ v ∈ VMl (lrInvGsp r K i₀) 1, (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
            Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v = v := by
        intro g
        change (e (spCentEquiv _ g)).2 = 1 ↔ _
        rw [← OneMemClass.coe_eq_one, glW_eq_one_iff (he (spCentEquiv _ g)).2]
        simp only [spCentEquiv_apply]
      have hc := UnitaryHigher.isCompl_ker_sub_one_ker_add_one h2
        (UnitaryHigher.invSMulOp_mul_self one_ne_zero hAA')
      have hsum : Module.finrank K (VPl (lrInvGsp r K i₀) 1) +
          Module.finrank K (VMl (lrInvGsp r K i₀) 1) = 2 * r := by
        have := Submodule.finrank_add_eq_of_isCompl hc
        rw [finrank_standard] at this
        exact this
      have hMle : Module.finrank K (VMl (lrInvGsp r K i₀) 1) ≤ 2 := by
        set b : Fin 2 → (Fin r ⊕ Fin r → K) :=
          ![Pi.single (Sum.inl i₀) 1, Pi.single (Sum.inr i₀) 1] with hb
        have hle : VMl (lrInvGsp r K i₀) 1 ≤ Submodule.span K (Set.range b) := by
          intro v hv
          have hv' := (mem_VMl_lrInv h2 i₀).1 hv
          have hvs : v = v (Sum.inl i₀) • b 0 + v (Sum.inr i₀) • b 1 := by
            ext x
            simp only [hb, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply,
              Pi.smul_apply, smul_eq_mul, Pi.single_apply]
            by_cases hxa : x = Sum.inl i₀
            · subst hxa
              simp
            · by_cases hxb : x = Sum.inr i₀
              · subst hxb
                simp
              · rw [hv' x (by simp [lrPair, hxa, hxb])]
                simp [hxa, hxb]
          rw [hvs]
          exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
            (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
        calc Module.finrank K (VMl (lrInvGsp r K i₀) 1) ≤
            Module.finrank K (Submodule.span K (Set.range b)) := Submodule.finrank_mono hle
          _ ≤ Fintype.card (Fin 2) := finrank_range_le_card b
          _ = 2 := Fintype.card_fin 2
      have hPx : Module.finrank K (VPl (lrInvGsp r K i₀) 1) ≠ 2 ∨ Nat.card K ≠ 3 := by
        left
        omega
      have hqP : IsQuasisimple (fixSub r K (lrInvGsp r K i₀) (VMl (lrInvGsp r K i₀) 1)) :=
        isQuasisimple_fixSub_of_equiv Ψ hres
          (LocalCores.isQuasisimple_of_mulEquiv
            (CatalogueBSymplecticB.sesqUnitaryIsometryEquiv _).symm
            (CatalogueBAlternatingIsometry.isometry_quasisimple _ haltP hndP
              (CatalogueBSymplecticB.two_le_finrank_of_ne_bot hPne _ haltP hndP) hodd hPx))
      have hTP : ∀ v ∈ VPl (lrInvGsp r K i₀) 1, ∀ c,
          transvSp v c ∈ fixSub r K (lrInvGsp r K i₀) (VMl (lrInvGsp r K i₀) 1) := by
        intro v hv c
        refine ⟨transvSp_mem_spCent hJA ((mem_eigenPlus one_ne_zero).1 hv) c, fun w hw => ?_⟩
        rw [coe_transvSp, add_mulVec, one_mulVec, smul_mulVec, transvN_mulVec, horth v hv w hw,
          zero_smul, smul_zero, add_zero]
      have hy' : conjAut r K D' * fieldAut r K 1 ∈ oddCoreIn B (conjAut r K (lrInvGsp r K i₀)) := by
        rw [map_one, mul_one]
        exact hy
      exact (eigen_of_transvSp_mem hinj hB (fixSub_le _ _)
        (fun f hf q hq => conj_mem_fixSub (fun g hg v hv => mulVec_mem_VMl one_ne_zero hg hv) hf
          hq) hqP hTP hy').2
  exact splitSelf_conclude hK hr hAns one_ne_zero hUU hUJ hoddy hPe hMe

end CFSG.ComponentClassification.Burgoyne.Sp

