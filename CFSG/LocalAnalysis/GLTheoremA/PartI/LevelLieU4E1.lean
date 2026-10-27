module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Blocks
public import CFSG.Fischer.Classification.Recognition.Basic
public import CFSG.HardMathSupport.Timmesfeld.Proving.OmegaPiGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieU4E

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 (SU4 μ3 torusSU4 Dstd)
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48
open scoped commutatorElement
open Matrix
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV (torusSnoc torusSnoc_castSucc torusSnoc_last)
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K hK card_K card_units_K)

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

theorem le_ker_of_perfect {G H : Type} [Group G] [CommGroup H] (φ : G →* H) {T : Subgroup G}
    (hT : ⁅T, T⁆ = T) : T ≤ φ.ker := by
  rw [← hT, Subgroup.commutator_le]
  intro a ha b hb
  rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_inv, map_inv]
  simp [mul_comm, mul_assoc, mul_left_comm]

theorem eq_of_perfect_of_subnormal {X : Type} [Group X] {Q K : Subgroup X}
    (hQ : CFSG.Open.IsQuasisimple Q) (hKQ : CFSG.Open.IsSubnormal K Q) (hK : ⁅K, K⁆ = K)
    (hK1 : K ≠ ⊥) : K = Q := by
  rcases CFSG.Fischer.Classification.Recognition.IsSubnormal.eq_or_le_center hKQ hQ with h | h
  · exact h
  · exfalso
    apply hK1
    rw [← hK, Subgroup.commutator_eq_bot_iff_le_centralizer.mpr]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp (h ha)
    rw [Subgroup.mem_center_iff] at hz
    have := congrArg Subtype.val (hz ⟨b, hKQ.le hb⟩)
    simpa using this

theorem pSimple_equiv_of_simple {G : Type} [Group G] [Finite G] (K : Subgroup G) [IsSimpleGroup K]
    (hnc : ¬ IsMulCommutative K) (h3 : 3 ∣ Nat.card K) : Nonempty (PSimple 3 K ≃* K) := by
  have hO : GLAPPrimeCore 3 K = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Proving.glaPPrimeCore_eq_bot_of_isSimpleGroup
      Nat.prime_three h3
  let pq0 : PQuot 3 K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  have hZK : Subgroup.center K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
    · exact h
    · exfalso
      apply hnc
      refine ⟨⟨fun a b => ?_⟩⟩
      have ha : a ∈ Subgroup.center K := by
        rw [h]
        exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.1 ha b).symm
  have hZP : Subgroup.center (PQuot 3 K) = ⊥ := by
    have h1 := Subgroup.map_center_eq pq0
    rw [hZK] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ pq0.injective).1 h1
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZP).trans (QuotientGroup.quotientBot.trans pq0)⟩

theorem centralizer_conj_eq {G : Type} [Group G] (h s : G) :
    Subgroup.centralizer {h * s * h⁻¹} =
      (Subgroup.centralizer {s}).map (MulAut.conj h).toMonoidHom := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map]
  constructor
  · intro hx
    refine ⟨h⁻¹ * x * h, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc h⁻¹ * x * h * s = h⁻¹ * (x * (h * s * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * s * h⁻¹) * x) * h := by rw [hx]
        _ = s * (h⁻¹ * x * h) := by group
    · change h * (h⁻¹ * x * h) * h⁻¹ = x
      group
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    change h * y * h⁻¹ * (h * s * h⁻¹) = (h * s * h⁻¹) * (h * y * h⁻¹)
    calc h * y * h⁻¹ * (h * s * h⁻¹) = h * (y * s) * h⁻¹ := by group
      _ = h * (s * y) * h⁻¹ := by rw [hy]
      _ = h * s * h⁻¹ * (h * y * h⁻¹) := by group

theorem glaPComponent_conj {G : Type} [Group G] [Finite G] {p : ℕ} {X L : Subgroup G}
    (hL : GLAPComponent p X L) (h : G) :
    GLAPComponent p (X.map (MulAut.conj h).toMonoidHom) (L.map (MulAut.conj h).toMonoidHom) := by
  have := glaPComponent_gLBConj hL h⁻¹
  simpa [GLBConj] using this

open CFSG.LocalAnalysis.GLTheoremA.CatB.U48
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K hK card_K card_units_K)
open Matrix
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV (torusSnoc torusSnoc_castSucc torusSnoc_last)

@[expose] def mat (x : SU4) : Matrix (Fin 4) (Fin 4) K := ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)

theorem mat_mul (x y : SU4) : mat (x * y) = mat x * mat y := by
  unfold mat; rw [Subgroup.coe_mul, Units.val_mul]

theorem mat_pow (x : SU4) (n : ℕ) : mat (x ^ n) = mat x ^ n := by
  unfold mat; rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]

theorem mat_one : mat 1 = 1 := by
  unfold mat; rw [Subgroup.coe_one, Units.val_one]

@[expose] def canonB (a b c d : Fin 3) : Bool :=
  decide ((a, b, c, d) = (0, 0, 0, 0)) || decide ((a, b, c, d) = (1, 1, 1, 0)) ||
    decide ((a, b, c, d) = (2, 2, 2, 0)) || decide ((a, b, c, d) = (0, 0, 1, 2)) ||
    decide ((a, b, c, d) = (1, 1, 2, 2))

theorem exists_perm_canon : ∀ a b c d : Fin 3, (a.val + b.val + c.val + d.val) % 3 = 0 →
    ∃ σ : Equiv.Perm (Fin 4), canonB (![a, b, c, d] (σ 0)) (![a, b, c, d] (σ 1))
      (![a, b, c, d] (σ 2)) (![a, b, c, d] (σ 3)) = true := by
  decide

theorem permMatrix_mul_diagonal (π : Equiv.Perm (Fin 4)) (lam c : Fin 4 → K)
    (h : ∀ i, lam (π i) = c i) :
    Equiv.Perm.permMatrix K π * diagonal lam = diagonal c * Equiv.Perm.permMatrix K π := by
  ext i j
  have hP : ∀ a b : Fin 4, Equiv.Perm.permMatrix K π a b = if π a = b then 1 else 0 := by
    intro a b
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hP]
  by_cases hi : π i = j
  · subst hi
    simp [h i]
  · simp [hi]

theorem permMatrix_mem (π : Equiv.Perm (Fin 4)) :
    (TauCeti.permutationGL (k := K) π⁻¹ : GL (Fin 4) K) ∈ LieType.Universal.Unitary.SUid σ4 4 := by
  rw [LieType.Universal.Unitary.mem_SUid, TauCeti.permutationGL_coe, inv_inv]
  have hP : ∀ a b : Fin 4, Equiv.Perm.permMatrix K π a b = if π a = b then 1 else 0 := by
    intro a b
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  constructor
  · rw [Matrix.det_permutation]
    have hs : ((Equiv.Perm.sign π : ℤˣ) : K) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h
      · rw [h]; simp
      · rw [h]
        simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
        exact CharTwo.neg_eq (1 : K)
    rw [hs]
  · have hmap : (Equiv.Perm.permMatrix K π).map σ4 = Equiv.Perm.permMatrix K π := by
      ext a b
      rw [Matrix.map_apply, hP]
      split_ifs <;> simp
    rw [LieType.Universal.Unitary.conjTr, hmap, Matrix.transpose_permMatrix,
      ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

@[expose] noncomputable def pSU (π : Equiv.Perm (Fin 4)) : SU4 :=
  ⟨TauCeti.permutationGL (k := K) π⁻¹, permMatrix_mem π⟩

theorem mat_pSU (π : Equiv.Perm (Fin 4)) : mat (pSU π) = Equiv.Perm.permMatrix K π := by
  unfold mat pSU
  change ((TauCeti.permutationGL (k := K) π⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = _
  rw [TauCeti.permutationGL_coe, inv_inv]

@[expose] noncomputable def dz (ζ : K) (κ : Fin 4 → Fin 3) : Matrix (Fin 4) (Fin 4) K :=
  diagonal fun i => ζ ^ (κ i : ℕ)

theorem normal_form_matrix (s : SU4) (hs : s ^ 3 = 1) (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    ∃ h : SU4, ∃ κ : Fin 4 → Fin 3, canonB (κ 0) (κ 1) (κ 2) (κ 3) = true ∧
      mat (h * s) = dz ζ κ * mat h := by
  have hcomm : ∀ x ∈ Subgroup.zpowers s, ∀ y ∈ Subgroup.zpowers s, x * y = y * x := by
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    exact (((Commute.refl s).zpow_left m).zpow_right n).eq
  have hpow : ∀ x ∈ Subgroup.zpowers s, x ^ 3 = 1 := by
    rintro _ ⟨m, rfl⟩
    have h3 : (s ^ m) ^ (3 : ℕ) = (s ^ (3 : ℤ)) ^ m := by
      rw [← zpow_natCast (s ^ m) 3, ← _root_.zpow_mul, ← _root_.zpow_mul]
      congr 1
      ring
    rw [h3, show (s ^ (3 : ℤ)) = 1 by rw [zpow_ofNat]; exact hs, _root_.one_zpow]
  obtain ⟨g, hg⟩ := exists_conj_isDiag hcomm hpow
  set D : Matrix (Fin 4) (Fin 4) K := mat (g * s * g⁻¹) with hD
  have hDdiag : D.IsDiag := hg s (Subgroup.mem_zpowers s)
  set lam : Fin 4 → K := D.diag with hlam
  have hDeq : D = diagonal lam := hDdiag.diagonal_diag.symm
  have hD3 : D ^ 3 = 1 := by
    have h1 : (g * s * g⁻¹ : SU4) ^ 3 = 1 := by
      rw [conj_pow, hs, mul_one, mul_inv_cancel]
    rw [hD, ← mat_pow, h1, mat_one]
  have hlam3 : ∀ i, lam i ^ 3 = 1 := by
    intro i
    have h := congrFun (congrFun (hDeq ▸ hD3 : (diagonal lam) ^ 3 = 1) i) i
    rw [Matrix.diagonal_pow] at h
    simpa [Matrix.diagonal_apply] using h
  have hdet : ∏ i, lam i = 1 := by
    have h1 : D.det = 1 := by
      have := (g * s * g⁻¹ : SU4).2
      rw [LieType.Universal.Unitary.mem_SUid] at this
      exact this.1
    rw [hDeq, Matrix.det_diagonal] at h1
    exact h1
  have hex : ∀ i, ∃ k : Fin 3, ζ ^ (k : ℕ) = lam i := by
    intro i
    obtain ⟨k, hk, hk'⟩ := hζ.eq_pow_of_pow_eq_one (hlam3 i)
    exact ⟨⟨k, hk⟩, hk'⟩
  choose e he using hex
  have hsum : (∑ i, (e i : ℕ)) % 3 = 0 := by
    have h1 : ∏ i, lam i = ζ ^ (∑ i, (e i : ℕ)) := by
      calc ∏ i, lam i = ∏ i, ζ ^ (e i : ℕ) := Finset.prod_congr rfl (fun i _ => (he i).symm)
        _ = ζ ^ (∑ i, (e i : ℕ)) := Finset.prod_pow_eq_pow_sum _ _ _
    rw [h1] at hdet
    exact Nat.mod_eq_zero_of_dvd ((hζ.pow_eq_one_iff_dvd _).mp hdet)
  have hfun : ∀ k : Fin 4, ![e 0, e 1, e 2, e 3] k = e k := by
    intro k; fin_cases k <;> rfl
  obtain ⟨σ, hσ⟩ := exists_perm_canon (e 0) (e 1) (e 2) (e 3)
    (by simpa [Fin.sum_univ_four] using hsum)
  set κ : Fin 4 → Fin 3 := fun i => e (σ i) with hκ
  have hκcan : canonB (κ 0) (κ 1) (κ 2) (κ 3) = true := by
    simp only [hfun] at hσ
    exact hσ
  refine ⟨pSU σ * g, κ, hκcan, ?_⟩
  have hPD : Equiv.Perm.permMatrix K σ * diagonal lam = dz ζ κ * Equiv.Perm.permMatrix K σ := by
    apply permMatrix_mul_diagonal
    intro i
    exact (he (σ i)).symm
  have hDG : D * mat g = mat g * mat s := by
    have h2 : (g * s * g⁻¹ * g : SU4) = g * s := by group
    rw [hD, ← mat_mul, h2, mat_mul]
  rw [mat_mul, mat_mul, mat_pSU]
  calc Equiv.Perm.permMatrix K σ * mat g * mat s
      = Equiv.Perm.permMatrix K σ * (mat g * mat s) := by simp only [Matrix.mul_assoc]
    _ = Equiv.Perm.permMatrix K σ * (D * mat g) := by rw [hDG]
    _ = (Equiv.Perm.permMatrix K σ * D) * mat g := by simp only [Matrix.mul_assoc]
    _ = (Equiv.Perm.permMatrix K σ * diagonal lam) * mat g := by rw [hDeq]
    _ = (dz ζ κ * Equiv.Perm.permMatrix K σ) * mat g := by rw [hPD]
    _ = dz ζ κ * (Equiv.Perm.permMatrix K σ * mat g) := by simp only [Matrix.mul_assoc]

@[expose] noncomputable def zetaU (ζ : K) (hζ : IsPrimitiveRoot ζ 3) : μ3 :=
  ⟨Units.mk0 ζ (hζ.ne_zero (by norm_num)), by
    rw [mem_rootsOfUnity]
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    exact hζ.pow_eq_one⟩

theorem zetaU_val (ζ : K) (hζ : IsPrimitiveRoot ζ 3) : ((zetaU ζ hζ : Kˣ) : K) = ζ := by
  unfold zetaU; rfl

@[expose] noncomputable def c211 (ζ : K) (hζ : IsPrimitiveRoot ζ 3) : SU4 :=
  torusSU4 ![1, 1, zetaU ζ hζ]

@[expose] noncomputable def c022 (ζ : K) (hζ : IsPrimitiveRoot ζ 3) : SU4 :=
  torusSU4 ![zetaU ζ hζ, zetaU ζ hζ, zetaU ζ hζ ^ 2]

theorem mat_eq_of_mat_eq {x y : SU4} (h : mat x = mat y) : x = y :=
  Subtype.ext (Units.ext h)

theorem mat_yStd (t : μ3) :
    mat (yStd t) = diagonal fun k => if k = 3 then 1 else ((t : Kˣ) : K) := by
  unfold mat
  exact coe_yStd t

theorem torusSnoc3 (x : Fin 3 → Kˣ) (k : Fin 4) :
    torusSnoc 3 x k = ![x 0, x 1, x 2, (x 0 * x 1 * x 2)⁻¹] k := by
  fin_cases k
  · exact torusSnoc_castSucc 3 x 0
  · exact torusSnoc_castSucc 3 x 1
  · exact torusSnoc_castSucc 3 x 2
  · show torusSnoc 3 x (Fin.last 3) = _
    rw [torusSnoc_last, Fin.prod_univ_three]
    rfl

theorem mat_torusSU4 (a : Fin 3 → μ3) :
    mat (torusSU4 a) = diagonal ![((a 0 : Kˣ) : K), ((a 1 : Kˣ) : K), ((a 2 : Kˣ) : K),
      (((a 0 : Kˣ) * (a 1 : Kˣ) * (a 2 : Kˣ))⁻¹ : Kˣ)] := by
  unfold mat
  rw [coe_torusSU4]
  congr 1
  funext k
  rw [torusSnoc3]
  fin_cases k <;> rfl

theorem inv_zeta (ζ : K) (hζ : IsPrimitiveRoot ζ 3) : (ζ * ζ * ζ ^ 2)⁻¹ = ζ ^ 2 := by
  have h3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have h4 : ζ * ζ * ζ ^ 2 = ζ := by
    calc ζ * ζ * ζ ^ 2 = ζ ^ 4 := by ring
      _ = ζ := by rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, h3, one_mul, pow_one]
  rw [h4]
  apply inv_eq_of_mul_eq_one_right
  calc ζ * ζ ^ 2 = ζ ^ 3 := by ring
    _ = 1 := h3

theorem inv_zeta' (ζ : K) (hζ : IsPrimitiveRoot ζ 3) : ζ⁻¹ = ζ ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  calc ζ * ζ ^ 2 = ζ ^ 3 := by ring
    _ = 1 := hζ.pow_eq_one

theorem mat_c211 (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    mat (c211 ζ hζ) = diagonal ![1, 1, ζ, ζ ^ 2] := by
  unfold c211
  rw [mat_torusSU4]
  congr 1
  funext k
  fin_cases k <;> simp [zetaU_val, inv_zeta' ζ hζ]

theorem inv_c022 (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    (((zetaU ζ hζ : μ3) : Kˣ) * ((zetaU ζ hζ : μ3) : Kˣ) * ((zetaU ζ hζ ^ 2 : μ3) : Kˣ))⁻¹ =
      ((zetaU ζ hζ ^ 2 : μ3) : Kˣ) := by
  apply Units.ext
  simp only [Units.val_inv_eq_inv_val, Units.val_mul, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  rw [zetaU_val]
  exact inv_zeta ζ hζ

theorem mat_c022 (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    mat (c022 ζ hζ) = diagonal ![ζ, ζ, ζ ^ 2, ζ ^ 2] := by
  unfold c022
  rw [mat_torusSU4]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  rw [inv_c022 ζ hζ]
  congr 1

theorem mat_yStd_zetaU (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    mat (yStd (zetaU ζ hζ)) = diagonal ![ζ, ζ, ζ, 1] := by
  rw [mat_yStd]
  congr 1
  funext k
  fin_cases k <;> simp [zetaU_val]

theorem mat_yStd_zetaU2 (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    mat (yStd (zetaU ζ hζ ^ 2)) = diagonal ![ζ ^ 2, ζ ^ 2, ζ ^ 2, 1] := by
  rw [mat_yStd]
  congr 1
  funext k
  fin_cases k <;> simp [zetaU_val, Subgroup.coe_pow, Units.val_pow_eq_pow_val]

theorem dz_zero (ζ : K) : dz ζ ![0, 0, 0, 0] = 1 := by
  unfold dz
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]

theorem dz_yStd (ζ : K) (hζ : IsPrimitiveRoot ζ 3) : dz ζ ![1, 1, 1, 0] = mat (yStd (zetaU ζ hζ)) := by
  rw [mat_yStd_zetaU ζ hζ]
  unfold dz
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]

theorem dz_yStd2 (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    dz ζ ![2, 2, 2, 0] = mat (yStd (zetaU ζ hζ ^ 2)) := by
  rw [mat_yStd_zetaU2 ζ hζ]
  unfold dz
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]

theorem dz_c211 (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    dz ζ ![0, 0, 1, 2] = mat (c211 ζ hζ) := by
  rw [mat_c211 ζ hζ]
  unfold dz
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]

theorem dz_c022 (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    dz ζ ![1, 1, 2, 2] = mat (c022 ζ hζ) := by
  rw [mat_c022 ζ hζ]
  unfold dz
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]

theorem normal_form (s : SU4) (hs : s ^ 3 = 1) (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    ∃ h : SU4, h * s * h⁻¹ = 1 ∨ h * s * h⁻¹ = yStd (zetaU ζ hζ) ∨
      h * s * h⁻¹ = yStd (zetaU ζ hζ ^ 2) ∨ h * s * h⁻¹ = c211 ζ hζ ∨ h * s * h⁻¹ = c022 ζ hζ := by
  obtain ⟨h, κ, hκ, hmat⟩ := normal_form_matrix s hs ζ hζ
  refine ⟨h, ?_⟩
  have key : ∀ c : SU4, mat c = dz ζ κ → h * s * h⁻¹ = c := by
    intro c hc
    rw [mul_inv_eq_iff_eq_mul]
    apply mat_eq_of_mat_eq
    rw [hmat, mat_mul, hc]
  have hκeq : ∀ v : Fin 4 → Fin 3, κ 0 = v 0 → κ 1 = v 1 → κ 2 = v 2 → κ 3 = v 3 → κ = v := by
    intro v a b c d
    ext k
    fin_cases k <;> simp_all
  simp only [canonB, Bool.or_eq_true, decide_eq_true_eq, Prod.mk.injEq] at hκ
  rcases hκ with ((((⟨a0, a1, a2, a3⟩) | ⟨a0, a1, a2, a3⟩) | ⟨a0, a1, a2, a3⟩) | ⟨a0, a1, a2, a3⟩) |
    ⟨a0, a1, a2, a3⟩
  · left
    apply key 1
    rw [mat_one]
    have hv : κ = ![0, 0, 0, 0] := hκeq _ a0 a1 a2 a3
    rw [hv, dz_zero]
  · right; left
    apply key (yStd (zetaU ζ hζ))
    have hv : κ = ![1, 1, 1, 0] := hκeq _ a0 a1 a2 a3
    rw [hv, dz_yStd ζ hζ]
  · right; right; left
    apply key (yStd (zetaU ζ hζ ^ 2))
    have hv : κ = ![2, 2, 2, 0] := hκeq _ a0 a1 a2 a3
    rw [hv, dz_yStd2 ζ hζ]
  · right; right; right; left
    apply key (c211 ζ hζ)
    have hv : κ = ![0, 0, 1, 2] := hκeq _ a0 a1 a2 a3
    rw [hv, dz_c211 ζ hζ]
  · right; right; right; right
    apply key (c022 ζ hζ)
    have hv : κ = ![1, 1, 2, 2] := hκeq _ a0 a1 a2 a3
    rw [hv, dz_c022 ζ hζ]


end CFSG.LocalAnalysis.GLTheoremA.LevelLieU4E
