module

public import CFSG.LocalAnalysis.Mason73.L4SylowTransport
public import CFSG.LocalAnalysis.Mason73.L4SL2Witness
public import CFSG.ClassicalInvolution.Phan.Blocks
public import CFSG.Adapters.LieModelOrders

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.Open CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped Matrix

namespace LinearWitness

section Proj

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem eq_one_of_mem_statedScalars {A : GL ι K} (hA : A ∈ StatedScalars ι K) {a : ι}
    (ha : (A : Matrix ι ι K) a a = 1) : A = 1 := by
  obtain ⟨c, rfl⟩ := hA
  have hc : c = 1 := Units.ext (by
    simpa only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, Units.val_one] using ha)
  rw [hc, map_one]

theorem orderOf_mk_of_forall {H : Subgroup (GL ι K)} {g : GL ι K} (hg : g ∈ H)
    (hs : ∀ m : ℕ, g ^ m ∈ StatedScalars ι K → g ^ m = 1) :
    orderOf (QuotientGroup.mk ⟨g, hg⟩ : StatedProj H) = orderOf g := by
  have hpow : ∀ m : ℕ, (((⟨g, hg⟩ : H) ^ m : H) : GL ι K) = g ^ m := fun m =>
    Subgroup.coe_pow _ _ m
  rw [← Subgroup.orderOf_mk (H := H) g hg]
  refine orderOf_eq_orderOf_iff.2 fun m => ?_
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hpow]
  refine ⟨fun h => Subtype.ext ?_, fun h => ?_⟩
  · rw [hpow, Subgroup.coe_one]
    exact hs m h
  · rw [← hpow, h, Subgroup.coe_one]
    exact one_mem _

end Proj

section Inverted

variable {G : Type} [Group G] [Finite G] {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  {K : Type} [Field K]

theorem false_of_inverted_of_l4Sylow_of_statedProj (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) {H : Subgroup (GL ι K)}
    (e : G ≃* StatedProj H) {R S : GL ι K} (hRH : R ∈ H) (hSH : S ∈ H) {k j : ℕ}
    (hR : orderOf R = 2 ^ k) (hS : S ^ 2 ^ j = 1)
    (hRs : ∀ m : ℕ, R ^ m ∈ StatedScalars ι K → R ^ m = 1) (hSR : S * R * S⁻¹ = R⁻¹)
    (hk : n < k) : False := by
  let π : H →* StatedProj H := QuotientGroup.mk' _
  have hSj : (⟨S, hSH⟩ : H) ^ 2 ^ j = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hS)
  have hπS : π ⟨S, hSH⟩ ^ 2 ^ j = 1 := by rw [← map_pow, hSj, map_one]
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hπS)
  have hSR' : (⟨S, hSH⟩ : H) * ⟨R, hRH⟩ * (⟨S, hSH⟩ : H)⁻¹ = (⟨R, hRH⟩ : H)⁻¹ := Subtype.ext hSR
  exact false_of_inverted_of_l4Sylow_of_mulEquiv hn P hP e (R := π ⟨R, hRH⟩) (S := π ⟨S, hSH⟩)
    ((orderOf_mk_of_forall hRH hRs).trans hR) hi
    (by simpa only [map_mul, map_inv] using congrArg π hSR') hk

end Inverted

section Blocks

variable {K : Type} [Field K] {m : ℕ}

theorem mul_blockMat_apply_of_not_mem {k i : ℕ} (M : Matrix (Fin m) (Fin m) K)
    (B : Matrix (Fin k) (Fin k) K) (a : Fin m) {b : Fin m}
    (hb : ¬ (i ≤ b.val ∧ b.val < i + k)) : (M * blockMat m i B) a b = M a b := by
  rw [Matrix.mul_apply]
  simp_rw [fun l => blockMat_apply_of_not_mem_right B l hb]
  simp [Matrix.one_apply]

theorem blockMat_mul_apply_of_not_mem {k i : ℕ} (B : Matrix (Fin k) (Fin k) K)
    (M : Matrix (Fin m) (Fin m) K) {a : Fin m} (ha : ¬ (i ≤ a.val ∧ a.val < i + k))
    (b : Fin m) : (blockMat m i B * M) a b = M a b := by
  rw [Matrix.mul_apply]
  simp_rw [blockMat_apply_of_not_mem_left B ha]
  simp [Matrix.one_apply]

theorem blockGL_injective {k i : ℕ} (h : i + k ≤ m) :
    Function.Injective (blockGL (F := K) m i h) := by
  intro A B hAB
  have hM := congrArg Units.val hAB
  rw [coe_blockGL, coe_blockGL] at hM
  exact Units.ext (blockMat_injective h hM)

theorem blockGL_eq_one_of_mem_statedScalars {k i : ℕ} (h : i + k ≤ m) {a : Fin m}
    (ha : ¬ (i ≤ a.val ∧ a.val < i + k)) {g : GL (Fin k) K}
    (hg : blockGL m i h g ∈ StatedScalars (Fin m) K) : blockGL m i h g = 1 :=
  eq_one_of_mem_statedScalars hg (by
    rw [coe_blockGL, blockMat_apply_of_not_mem_left _ ha, Matrix.one_apply_eq])

theorem blockGL_two_pow_eq_one_of_mem (hm : 3 ≤ m) (g : GL (Fin 2) K) (j : ℕ)
    (hg : blockGL m 0 (by omega) g ^ j ∈ StatedScalars (Fin m) K) :
    blockGL m 0 (by omega) g ^ j = 1 := by
  rw [← map_pow] at hg ⊢
  exact blockGL_eq_one_of_mem_statedScalars (by omega) (a := ⟨m - 1, by omega⟩)
    (by show ¬ (0 ≤ m - 1 ∧ m - 1 < 0 + 2); omega) hg

end Blocks

section Pair

variable {K : Type} [Field K]

theorem commute_blockGL_zero_two (a b : GL (Fin 2) K) :
    Commute (blockGL 5 0 (by norm_num) a) (blockGL 5 2 (by norm_num) b) :=
  Units.ext (blockMat_comm (Or.inl (by norm_num)) _ _)

@[expose] def pairGL : GL (Fin 2) K × GL (Fin 2) K →* GL (Fin 5) K :=
  (blockGL 5 0 (by norm_num)).noncommCoprod (blockGL 5 2 (by norm_num)) commute_blockGL_zero_two

theorem coe_pairGL (a b : GL (Fin 2) K) :
    ((pairGL (a, b) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      blockMat 5 0 (a : Matrix (Fin 2) (Fin 2) K) *
        blockMat 5 2 (b : Matrix (Fin 2) (Fin 2) K) := by
  rw [pairGL, MonoidHom.noncommCoprod_apply, Units.val_mul, coe_blockGL, coe_blockGL]

theorem coe_pairGL_apply_four (a b : GL (Fin 2) K) :
    ((pairGL (a, b) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 4 4 = 1 := by
  have h2 : ¬ (2 ≤ (4 : Fin 5).val ∧ (4 : Fin 5).val < 2 + 2) := by decide
  have h0 : ¬ (0 ≤ (4 : Fin 5).val ∧ (4 : Fin 5).val < 0 + 2) := by decide
  rw [coe_pairGL, mul_blockMat_apply_of_not_mem _ _ _ h2, blockMat_apply_of_not_mem_left _ h0,
    Matrix.one_apply_eq]

theorem pairGL_injective : Function.Injective (pairGL (K := K)) := by
  refine (injective_iff_map_eq_one _).2 ?_
  rintro ⟨a, b⟩ hab
  have hM : blockMat 5 0 (a : Matrix (Fin 2) (Fin 2) K) *
      blockMat 5 2 (b : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← coe_pairGL, hab, Units.val_one]
  have h0 : 0 + 2 ≤ 5 := by norm_num
  have h2 : 2 + 2 ≤ 5 := by norm_num
  refine Prod.mk_eq_one.2 ⟨Units.ext ?_, Units.ext ?_⟩
  · ext x y
    have hy : ¬ (2 ≤ (blockIdx 0 h0 y).val ∧ (blockIdx 0 h0 y).val < 2 + 2) := by
      rw [blockIdx_val]
      have := y.isLt
      omega
    have := congrFun (congrFun hM (blockIdx 0 h0 x)) (blockIdx 0 h0 y)
    rw [mul_blockMat_apply_of_not_mem _ _ _ hy, blockMat_apply_blockIdx] at this
    rw [this]
    simp [Matrix.one_apply, (blockIdx_injective h0).eq_iff]
  · ext x y
    have hx : ¬ (0 ≤ (blockIdx 2 h2 x).val ∧ (blockIdx 2 h2 x).val < 0 + 2) := by
      rw [blockIdx_val]
      omega
    have := congrFun (congrFun hM (blockIdx 2 h2 x)) (blockIdx 2 h2 y)
    rw [blockMat_mul_apply_of_not_mem _ _ hx, blockMat_apply_blockIdx] at this
    rw [this]
    simp [Matrix.one_apply, (blockIdx_injective h2).eq_iff]

theorem orderOf_pairGL_inv (x : GL (Fin 2) K) : orderOf (pairGL (x, x⁻¹)) = orderOf x := by
  rw [orderOf_injective _ pairGL_injective, Prod.orderOf_mk, orderOf_inv, Nat.lcm_self]

theorem pairGL_pow_eq_one_of_mem (ab : GL (Fin 2) K × GL (Fin 2) K) (j : ℕ)
    (h : pairGL ab ^ j ∈ StatedScalars (Fin 5) K) : pairGL ab ^ j = 1 := by
  rw [← map_pow] at h ⊢
  exact eq_one_of_mem_statedScalars h (coe_pairGL_apply_four (ab ^ j).1 (ab ^ j).2)

theorem det_coe_pairGL_inv (x : GL (Fin 2) K) :
    ((pairGL (x, x⁻¹) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det = 1 := by
  rw [coe_pairGL, Matrix.det_mul, det_blockMat (show 0 + 2 ≤ 5 by norm_num),
    det_blockMat (show 2 + 2 ≤ 5 by norm_num), ← Matrix.det_mul, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, Matrix.det_one]

@[expose] def blockSwapPerm : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 1 3

theorem blockSwapPerm_mul_self : blockSwapPerm * blockSwapPerm = 1 := by decide

variable (K) in
@[expose] def blockSwapMat : Matrix (Fin 5) (Fin 5) K := blockSwapPerm.permMatrix K

theorem blockSwapMat_mul_self : blockSwapMat K * blockSwapMat K = 1 := by
  rw [blockSwapMat, ← Matrix.permMatrix_mul, blockSwapPerm_mul_self, Matrix.permMatrix_one]

theorem det_blockSwapMat : (blockSwapMat K).det = 1 := by
  rw [blockSwapMat, Matrix.det_permutation, blockSwapPerm, Equiv.Perm.sign_mul]
  simp [Equiv.Perm.sign_swap']

theorem transpose_blockSwapMat_mul_self : (blockSwapMat K)ᵀ * blockSwapMat K = 1 := by
  rw [blockSwapMat, Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel,
    Matrix.permMatrix_one]

theorem blockSwapMat_map_pow {q : ℕ} (hq : q ≠ 0) :
    (blockSwapMat K).map (· ^ q) = blockSwapMat K := by
  ext a b
  simp only [Matrix.map_apply, blockSwapMat, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  split_ifs <;> simp [zero_pow hq]

variable (K) in
@[expose] def blockSwapGL : GL (Fin 5) K :=
  ⟨blockSwapMat K, blockSwapMat K, blockSwapMat_mul_self, blockSwapMat_mul_self⟩

theorem blockSwapGL_sq : blockSwapGL K ^ 2 ^ 1 = 1 :=
  Units.ext (by rw [pow_one, sq, Units.val_mul]; exact blockSwapMat_mul_self)

theorem blockSwapMat_mul_blockSel_zero :
    blockSwapMat K * blockSel K 5 2 0 = blockSel K 5 2 2 * (1 : Matrix (Fin 2) (Fin 2) K) := by
  have key : ∀ a : Fin 5, ∀ j : Fin 2,
      ((blockSwapPerm a).val = 0 + j.val ↔ a.val = 2 + j.val) := by decide
  rw [Matrix.mul_one, blockSwapMat, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  ext a j
  simp only [Matrix.submatrix_apply, blockSel_apply, id, key a j]

theorem blockSwapMat_mul_blockSel_two :
    blockSwapMat K * blockSel K 5 2 2 = blockSel K 5 2 0 * (1 : Matrix (Fin 2) (Fin 2) K) := by
  have key : ∀ a : Fin 5, ∀ j : Fin 2,
      ((blockSwapPerm a).val = 2 + j.val ↔ a.val = 0 + j.val) := by decide
  rw [Matrix.mul_one, blockSwapMat, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  ext a j
  simp only [Matrix.submatrix_apply, blockSel_apply, id, key a j]

theorem blockSel_two_transpose_mul_blockSwapMat :
    (blockSel K 5 2 2)ᵀ * blockSwapMat K =
      (1 : Matrix (Fin 2) (Fin 2) K) * (blockSel K 5 2 0)ᵀ := by
  have key : ∀ a : Fin 5, ∀ j : Fin 2,
      ((blockSwapPerm.symm a).val = 2 + j.val ↔ a.val = 0 + j.val) := by decide
  rw [Matrix.one_mul, blockSwapMat, Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv]
  ext j a
  simp only [Matrix.submatrix_apply, Matrix.transpose_apply, blockSel_apply, id, key a j]

theorem blockSel_zero_transpose_mul_blockSwapMat :
    (blockSel K 5 2 0)ᵀ * blockSwapMat K =
      (1 : Matrix (Fin 2) (Fin 2) K) * (blockSel K 5 2 2)ᵀ := by
  have key : ∀ a : Fin 5, ∀ j : Fin 2,
      ((blockSwapPerm.symm a).val = 0 + j.val ↔ a.val = 2 + j.val) := by decide
  rw [Matrix.one_mul, blockSwapMat, Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv]
  ext j a
  simp only [Matrix.submatrix_apply, Matrix.transpose_apply, blockSel_apply, id, key a j]

theorem blockSwapMat_conj_zero (A : Matrix (Fin 2) (Fin 2) K) :
    blockSwapMat K * blockMat 5 0 A * blockSwapMat K = blockMat 5 2 A := by
  simpa only [Matrix.one_mul, Matrix.mul_one] using
    conj_blockMat_of_intertwine blockSwapMat_mul_self (Matrix.mul_one 1)
      blockSwapMat_mul_blockSel_zero blockSel_two_transpose_mul_blockSwapMat A

theorem blockSwapMat_conj_two (A : Matrix (Fin 2) (Fin 2) K) :
    blockSwapMat K * blockMat 5 2 A * blockSwapMat K = blockMat 5 0 A := by
  simpa only [Matrix.one_mul, Matrix.mul_one] using
    conj_blockMat_of_intertwine blockSwapMat_mul_self (Matrix.mul_one 1)
      blockSwapMat_mul_blockSel_two blockSel_zero_transpose_mul_blockSwapMat A

theorem blockSwapGL_conj_pairGL (a b : GL (Fin 2) K) :
    blockSwapGL K * pairGL (a, b) * (blockSwapGL K)⁻¹ = pairGL (b, a) := by
  apply Units.ext
  show blockSwapMat K * ((pairGL (a, b) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
    blockSwapMat K = _
  rw [coe_pairGL, coe_pairGL]
  have e : blockSwapMat K * (blockMat 5 0 (a : Matrix (Fin 2) (Fin 2) K) *
      blockMat 5 2 (b : Matrix (Fin 2) (Fin 2) K)) * blockSwapMat K =
      (blockSwapMat K * blockMat 5 0 (a : Matrix (Fin 2) (Fin 2) K) * blockSwapMat K) *
        (blockSwapMat K * blockMat 5 2 (b : Matrix (Fin 2) (Fin 2) K) * blockSwapMat K) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (blockSwapMat K) (blockSwapMat K), blockSwapMat_mul_self,
      Matrix.one_mul]
  rw [e, blockSwapMat_conj_zero, blockSwapMat_conj_two]
  exact blockMat_comm (Or.inr (by norm_num)) _ _

theorem blockSwapGL_conj_pairGL_inv (x : GL (Fin 2) K) :
    blockSwapGL K * pairGL (x, x⁻¹) * (blockSwapGL K)⁻¹ = (pairGL (x, x⁻¹))⁻¹ := by
  rw [blockSwapGL_conj_pairGL, ← map_inv, Prod.inv_mk, inv_inv]

theorem conjTr_pair_mul_self (σ : K ≃+* K) {a b : Matrix (Fin 2) (Fin 2) K}
    (ha : conjTr σ a * a = 1) (hb : conjTr σ b * b = 1) :
    conjTr σ (blockMat 5 0 a * blockMat 5 2 b) * (blockMat 5 0 a * blockMat 5 2 b) = 1 := by
  rw [conjTr_mul, conjTr_blockMat, conjTr_blockMat]
  calc blockMat 5 2 (conjTr σ b) * blockMat 5 0 (conjTr σ a) * (blockMat 5 0 a * blockMat 5 2 b)
      = blockMat 5 2 (conjTr σ b) * blockMat 5 0 (conjTr σ a * a) * blockMat 5 2 b := by
        rw [blockMat_mul (show 0 + 2 ≤ 5 by norm_num)]
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [ha, blockMat_one, Matrix.mul_one, ← blockMat_mul (show 2 + 2 ≤ 5 by norm_num), hb,
          blockMat_one]

theorem conjTr_inv_mul_self_of_unitary (σ : K ≃+* K) {x : GL (Fin 2) K}
    (hx : conjTr σ (x : Matrix (Fin 2) (Fin 2) K) * x = 1) :
    conjTr σ ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
  have h1 : (x : Matrix (Fin 2) (Fin 2) K) * ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : conjTr σ ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      conjTr σ (x : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← conjTr_mul, h1, conjTr_one]
  calc conjTr σ ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = conjTr σ ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
          (conjTr σ (x : Matrix (Fin 2) (Fin 2) K) * x) *
            ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
        rw [hx, Matrix.mul_one]
    _ = (conjTr σ ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
          conjTr σ (x : Matrix (Fin 2) (Fin 2) K)) *
          ((x : Matrix (Fin 2) (Fin 2) K) * ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, h2, Matrix.mul_one]

end Pair

end LinearWitness

open LinearWitness

variable {G : Type} [Group G] [Finite G] {n p f : ℕ}

theorem false_of_lieModel_psl_four_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : CFSG.Blueprint.LieModel G .PSL 4 p f) (hq : p ^ f % 4 = 3) : False := by
  have h2 := factorization_two_card_of_l4Sylow (by omega) P hP
  rw [hL.card_eq_lieOrd (by norm_num),
    show CFSG.EvenSmallLie.CatalogOrders.lieOrd .PSL 4 (p ^ f) = Open.ordA 3 (p ^ f) from rfl,
    factorization_two_ordA_three_of_three hq] at h2
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL.statedClassicalModel (by decide)
  obtain ⟨R, S, hR, hS, hSR⟩ := exists_sl2_inverted_pair (F := K)
    (by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow)
  rw [hK] at hR
  have h4 : 0 + 2 ≤ 4 := by norm_num
  let ψ : Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 4) K :=
    (blockGL 4 0 h4).comp Matrix.SpecialLinearGroup.toGL
  have hψ : Function.Injective ψ :=
    (blockGL_injective h4).comp Matrix.SpecialLinearGroup.toGL_injective
  have hmem : ∀ A, ψ A ∈ StatedSL 4 K := fun A => Subgroup.subset_closure (by
    show (blockMat 4 0 ((A : Matrix (Fin 2) (Fin 2) K))).det = 1
    rw [det_blockMat h4, A.2])
  refine false_of_inverted_of_l4Sylow_of_statedProj hn P hP e (hmem R) (hmem S)
    (k := ((p ^ f) ^ 2 - 1).factorization 2 - 1) (j := 2) ?_ ?_ ?_ ?_ ?_
  · rw [orderOf_injective ψ hψ, hR]
  · rw [← map_pow, show (2 : ℕ) ^ 2 = orderOf S by rw [hS]; norm_num, pow_orderOf_eq_one,
      map_one]
  · intro j hj
    exact blockGL_two_pow_eq_one_of_mem (m := 4) (by norm_num)
      (Matrix.SpecialLinearGroup.toGL R) j hj
  · simpa only [map_mul, map_inv] using congrArg ψ hSR
  · omega

theorem false_of_lieModel_psu_four_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (hp2 : p ≠ 2)
    (hL : CFSG.Blueprint.LieModel G .PSU 4 p f) (hq : p ^ f % 4 = 1) : False := by
  obtain ⟨hp, hf, -⟩ := hL.admissible
  have h2 := factorization_two_card_of_l4Sylow (by omega) P hP
  rw [hL.card_eq_lieOrd (by norm_num),
    show CFSG.EvenSmallLie.CatalogOrders.lieOrd .PSU 4 (p ^ f) = Open.ordTwistedA 3 (p ^ f)
      from rfl,
    factorization_two_ordTwistedA_three_of_one hq (Nat.one_lt_pow (by omega) hp.one_lt)] at h2
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL.statedClassicalModel (by decide)
  obtain ⟨R, S, hR, hS, hSR⟩ := exists_su2_inverted_pair hp hp2 (by omega) hK
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (f := f * 2) (by
    rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have h4 : 0 + 2 ≤ 4 := by norm_num
  let ψ : StatedSU 2 (p ^ f) K →* GL (Fin 4) K :=
    (blockGL 4 0 h4).comp (StatedSU 2 (p ^ f) K).subtype
  have hψ : Function.Injective ψ := (blockGL_injective h4).comp Subtype.val_injective
  have hmem : ∀ A, ψ A ∈ StatedSU 4 (p ^ f) K := fun A => by
    have hA : (A : GL (Fin 2) K) ∈ SUid (unitaryInvolution K p f) 2 := by
      rw [SUid_eq_statedSU hK]
      exact A.2
    have := blockGL_mem_SUid (unitaryInvolution K p f) h4 hA
    rw [SUid_eq_statedSU hK] at this
    exact this
  refine false_of_inverted_of_l4Sylow_of_statedProj hn P hP e (hmem R) (hmem S)
    (k := ((p ^ f) ^ 2 - 1).factorization 2 - 1) (j := 2) ?_ ?_ ?_ ?_ ?_
  · rw [orderOf_injective ψ hψ, hR]
  · rw [← map_pow, show (2 : ℕ) ^ 2 = orderOf S by rw [hS]; norm_num, pow_orderOf_eq_one,
      map_one]
  · intro j hj
    exact blockGL_two_pow_eq_one_of_mem (m := 4) (by norm_num) (R : GL (Fin 2) K) j hj
  · simpa only [map_mul, map_inv] using congrArg ψ hSR
  · omega

theorem false_of_lieModel_psl_five_of_l4Sylow_of_mod_four_three (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n))
    (hL : CFSG.Blueprint.LieModel G .PSL 5 p f) (hq : p ^ f % 4 = 3) : False := by
  have h2 := factorization_two_card_of_l4Sylow (by omega) P hP
  rw [hL.card_eq_lieOrd (by norm_num),
    show CFSG.EvenSmallLie.CatalogOrders.lieOrd .PSL 5 (p ^ f) = Open.ordA 4 (p ^ f) from rfl,
    factorization_two_ordA_four_of_three hq] at h2
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL.statedClassicalModel (by decide)
  obtain ⟨x, hx⟩ := exists_gl2_orderOf_two_pow (F := K) (by rw [hK]; exact hq)
  rw [hK] at hx
  refine false_of_inverted_of_l4Sylow_of_statedProj hn P hP e
    (R := pairGL (x, x⁻¹)) (S := blockSwapGL K)
    (Subgroup.subset_closure (det_coe_pairGL_inv x))
    (Subgroup.subset_closure (det_blockSwapMat (K := K)))
    (k := ((p ^ f) ^ 2 - 1).factorization 2) (j := 1)
    ((orderOf_pairGL_inv x).trans hx) blockSwapGL_sq (pairGL_pow_eq_one_of_mem _)
    (blockSwapGL_conj_pairGL_inv x) (by omega)

theorem false_of_lieModel_psu_five_of_l4Sylow_of_mod_four_one (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n))
    (hL : CFSG.Blueprint.LieModel G .PSU 5 p f) (hq : p ^ f % 4 = 1) : False := by
  obtain ⟨hp, hf, -⟩ := hL.admissible
  have h2 := factorization_two_card_of_l4Sylow (by omega) P hP
  rw [hL.card_eq_lieOrd (by norm_num),
    show CFSG.EvenSmallLie.CatalogOrders.lieOrd .PSU 5 (p ^ f) = Open.ordTwistedA 4 (p ^ f)
      from rfl,
    factorization_two_ordTwistedA_four_of_one hq (Nat.one_lt_pow (by omega) hp.one_lt)] at h2
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL.statedClassicalModel (by decide)
  obtain ⟨x, hxu, hx⟩ := exists_unitary_two_orderOf_two_pow hp hK hq
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (f := f * 2) (by
    rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have hq0 : p ^ f ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hσ : ∀ {k : ℕ} (A : Matrix (Fin k) (Fin k) K),
      conjTr (unitaryInvolution K p f) A = (A.map (· ^ (p ^ f)))ᵀ := fun A => by
    ext i j
    simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply, unitaryInvolution_apply]
  have hxσ : conjTr (unitaryInvolution K p f) (x : Matrix (Fin 2) (Fin 2) K) * x = 1 := by
    rw [hσ]
    exact hxu
  have hXH : pairGL (x, x⁻¹) ∈ StatedSU 5 (p ^ f) K := by
    refine Subgroup.subset_closure ⟨det_coe_pairGL_inv x, ?_⟩
    show (((pairGL (x, x⁻¹) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).map (· ^ (p ^ f)))ᵀ *
      ((pairGL (x, x⁻¹) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = 1
    rw [← hσ, coe_pairGL]
    exact conjTr_pair_mul_self _ hxσ (conjTr_inv_mul_self_of_unitary _ hxσ)
  have hWH : blockSwapGL K ∈ StatedSU 5 (p ^ f) K := by
    refine Subgroup.subset_closure ⟨det_blockSwapMat, ?_⟩
    show ((blockSwapMat K).map (· ^ (p ^ f)))ᵀ * blockSwapMat K = 1
    rw [blockSwapMat_map_pow hq0, transpose_blockSwapMat_mul_self]
  exact false_of_inverted_of_l4Sylow_of_statedProj hn P hP e hXH hWH
    (k := ((p ^ f) ^ 2 - 1).factorization 2) (j := 1)
    ((orderOf_pairGL_inv x).trans hx) blockSwapGL_sq (pairGL_pow_eq_one_of_mem _)
    (blockSwapGL_conj_pairGL_inv x) (by omega)

end CFSG.LocalAnalysis.Mason73
