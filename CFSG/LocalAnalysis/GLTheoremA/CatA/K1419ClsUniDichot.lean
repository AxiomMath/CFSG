module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsUniBlock
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsUniCentre
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsUniNu
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsLinField
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniComp
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Open.StatedAPI Matrix
open CFSG.LieType.SemisimpleCentralizers.Held (heldGU heldSU)

private lemma three_dvd_four_pow_sub_one (m : ℕ) : 3 ∣ 4 ^ m - 1 := by
  have h4mod : (4 : ℕ) ≡ 1 [MOD 3] := by decide
  have hpow : (4 : ℕ) ^ m ≡ 1 [MOD 3] := by simpa using h4mod.pow m
  exact hpow.symm.dvd'

private lemma three_dvd_sq_two_pow_sub_one (j : ℕ) : 3 ∣ (2 ^ j) ^ 2 - 1 := by
  have h : (2 ^ j) ^ 2 = 4 ^ j := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [h]
  exact three_dvd_four_pow_sub_one j

private lemma three_dvd_two_pow_mul_sub_one (j e : ℕ) : 3 ∣ (2 ^ j) ^ (2 * e) - 1 := by
  have h : (2 ^ j) ^ (2 * e) = 4 ^ (j * e) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [h]
  exact three_dvd_four_pow_sub_one (j * e)

private lemma exists_cube_root_unity_of_three_dvd {L : Type} [Field L] [Finite L]
    (h : 3 ∣ Nat.card L - 1) : ∃ w : L, w ^ 3 = 1 ∧ w ≠ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h3u : 3 ∣ Nat.card Lˣ := by rwa [Nat.card_units]
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Lˣ) 3 h3u
  have hω3 : ω ^ 3 = 1 := by simpa [hω] using pow_orderOf_eq_one ω
  have hωne : ω ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hω
    omega
  exact ⟨(ω : L), by simpa using congrArg (fun u : Lˣ => (u : L)) hω3,
    fun h1 => hωne (Units.ext h1)⟩

private lemma dvd_X_pow_three_sub_C_of_aeval_mulVec_eq_zero {L : Type} [Field L] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) L) {P : Polynomial L} (hirr : Irreducible P) {x : Fin n → L}
    (hx : x ≠ 0) {c : L} (hP : Polynomial.aeval A P *ᵥ x = 0)
    (hA3 : A ^ 3 = c • (1 : Matrix (Fin n) (Fin n) L)) :
    P ∣ Polynomial.X ^ 3 - Polynomial.C c := by
  have hCc : Polynomial.aeval A (Polynomial.X ^ 3 - Polynomial.C c) = 0 := by
    rw [Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, hA3,
      Algebra.algebraMap_eq_smul_one, sub_self]
  by_contra hndvd
  have hcop : IsCoprime P (Polynomial.X ^ 3 - Polynomial.C c) :=
    hirr.coprime_iff_not_dvd.mpr hndvd
  obtain ⟨u, v, huv⟩ := hcop
  have key : Polynomial.aeval A (u * P + v * (Polynomial.X ^ 3 - Polynomial.C c)) *ᵥ x = 0 := by
    rw [Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_mul, Matrix.add_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hP, hCc]
    simp
  rw [huv, Polynomial.aeval_one, Matrix.one_mulVec] at key
  exact hx key

private lemma natDegree_eq_one_of_irreducible_of_root_mem_range {L : Type} [Field L]
    {P : Polynomial L} (hirr : Irreducible P)
    (hmem : AdjoinRoot.root P ∈ (algebraMap L (AdjoinRoot P)).range) :
    P.natDegree = 1 := by
  haveI : Fact (Irreducible P) := ⟨hirr⟩
  obtain ⟨a₀, ha₀⟩ := hmem
  have hPne : P ≠ 0 := hirr.ne_zero
  have hmin := AdjoinRoot.minpoly_root (K := L) hPne
  rw [← ha₀, minpoly.eq_X_sub_C] at hmin
  have hCne : (Polynomial.C P.leadingCoeff⁻¹ : Polynomial L) ≠ 0 :=
    Polynomial.C_ne_zero.mpr (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hPne))
  have := congrArg Polynomial.natDegree hmin
  rw [Polynomial.natDegree_X_sub_C, Polynomial.natDegree_mul hPne hCne,
    Polynomial.natDegree_C, add_zero] at this
  exact this.symm

private lemma natDegree_eq_one_of_irreducible_of_dvd {L : Type} [Field L] [Finite L]
    {P : Polynomial L} (hirr : Irreducible P) {c : L}
    (hdvd : P ∣ Polynomial.X ^ 3 - Polynomial.C c)
    (hω : ∃ w : L, w ^ 3 = 1 ∧ w ≠ 1) (h3 : ¬ 3 ∣ P.natDegree) : P.natDegree = 1 := by
  haveI : Fact (Irreducible P) := ⟨hirr⟩
  have hPne : P ≠ 0 := hirr.ne_zero
  haveI : FiniteDimensional L (AdjoinRoot P) := (AdjoinRoot.powerBasis hPne).finite
  have ha3 : (AdjoinRoot.root P) ^ 3 ∈ (algebraMap L (AdjoinRoot P)).range := by
    refine ⟨c, ?_⟩
    have h := AdjoinRoot.mk_eq_zero.mpr hdvd
    rw [← AdjoinRoot.aeval_eq] at h
    rw [Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C] at h
    exact (sub_eq_zero.mp h).symm
  by_cases hmem : AdjoinRoot.root P ∈ (algebraMap L (AdjoinRoot P)).range
  · exact natDegree_eq_one_of_irreducible_of_root_mem_range hirr hmem
  · exfalso
    have h3dvd : 3 ∣ Module.finrank L (AdjoinRoot P) :=
      k1419ClsLinField_dvd_finrank hω hmem ha3
    rw [show Module.finrank L (AdjoinRoot P) = P.natDegree by
      rw [(AdjoinRoot.powerBasis hPne).finrank, AdjoinRoot.powerBasis_dim hPne]] at h3dvd
    exact h3 h3dvd

private lemma exists_eigenvalue_of_natDegree_eq_one {L : Type} [Field L] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) L} {P : Polynomial L} (hP1 : P.natDegree = 1)
    {X : Submodule L (Fin n → L)} (hPX : ∀ x ∈ X, Polynomial.aeval A P *ᵥ x = 0) :
    ∃ p : L, ∀ x ∈ X, A *ᵥ x = p • x := by
  obtain ⟨u, hu0, v, huv⟩ := Polynomial.natDegree_eq_one.mp hP1
  refine ⟨-(v / u), fun x hx => ?_⟩
  have h := hPX x hx
  rw [← huv] at h
  have h' : u • (A *ᵥ x) + v • x = 0 := by
    simpa [Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul, Matrix.add_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec] using h
  have h1 : u • (A *ᵥ x) = (-v) • x := by
    have h2 := h'
    rw [add_eq_zero_iff_eq_neg] at h2
    rw [h2, neg_smul]
  have h2 : u • ((-(v / u)) • x) = (-v) • x := by
    rw [smul_smul]
    congr 1
    field_simp
  exact (smul_right_inj hu0).mp (h1.trans h2.symm)

private lemma pow_three_eq_of_eigenvalue {L : Type} [Field L] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) L} {c p : L}
    (hA3 : A ^ 3 = c • (1 : Matrix (Fin n) (Fin n) L)) {x : Fin n → L} (hx : x ≠ 0)
    (hpx : A *ᵥ x = p • x) : p ^ 3 = c := by
  have hk : ∀ k : ℕ, A ^ k *ᵥ x = p ^ k • x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hpx, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
  have h : A ^ 3 *ᵥ x = c • x := by rw [hA3, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h2 : (p ^ 3 - c) • x = 0 := by
    rw [sub_smul, ← hk 3, h, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hx)

private lemma splits_X_pow_three_sub_C {L : Type} [Field L] {c p ω : L}
    (hω3 : ω ^ 3 = 1) (hωne : ω ≠ 1) (hp3 : p ^ 3 = c) :
    (Polynomial.X ^ 3 - Polynomial.C c : Polynomial L).Splits := by
  have hζ : IsPrimitiveRoot ω 3 := by
    rw [IsPrimitiveRoot.iff_orderOf]
    have h : orderOf ω ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hω3
    rcases Nat.prime_three.eq_one_or_self_of_dvd (orderOf ω) h with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hωne
    · exact h3
  exact X_pow_sub_C_splits_of_isPrimitiveRoot hζ hp3

private lemma scalar_unitary_eq {L : Type} [Field L] {n : ℕ} {τ : L ≃+* L}
    (hτ : ∀ x, τ (τ x) = x) (hn : 1 ≤ n) (c : Lˣ)
    (h : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ heldGU n L τ hτ) : τ (c : L) * c = 1 := by
  have hzu := CFSG.LieType.SemisimpleCentralizers.Held.mem_heldGU.mp h
  have hval : ((Matrix.GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) L) :
      Matrix (Fin n) (Fin n) L) = (c : L) • (1 : Matrix (Fin n) (Fin n) L) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.val_scalar_gl c
  rw [hval] at hzu
  have hmap : ((c : L) • (1 : Matrix (Fin n) (Fin n) L)).map τ =
      τ (c : L) • (1 : Matrix (Fin n) (Fin n) L) := by
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, hij]
  rw [hmap, Matrix.transpose_smul, Matrix.transpose_one] at hzu
  have hmul : (τ (c : L) • (1 : Matrix (Fin n) (Fin n) L)) * ((c : L) • 1) =
      (τ (c : L) * (c : L)) • 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul]
    rw [smul_smul]
  have h2 : (τ (c : L) * (c : L)) • (1 : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← hmul]
    exact hzu
  have := congrFun (congrFun h2 ⟨0, hn⟩) ⟨0, hn⟩
  simpa using this

private lemma three_dvd_Q_add_one_of_scalar_unitary {L : Type} [Field L] [Finite L] {n Q : ℕ}
    {τ : L ≃+* L} (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ Q) (hn : 1 ≤ n)
    {c : Lˣ} (hcGU : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ heldGU n L τ hτ)
    (hc3 : (c : L) ^ 3 = 1) (hcne : (c : L) ≠ 1) : 3 ∣ Q + 1 := by
  have hsc : τ (c : L) * c = 1 := scalar_unitary_eq hτ hn c hcGU
  have hQp1 : (c : L) ^ (Q + 1) = 1 := by
    rw [pow_succ, ← hτQ (c : L)]
    exact hsc
  have hc3u : c ^ 3 = 1 := Units.ext (by simpa using hc3)
  have hcne1 : c ≠ 1 := fun h => hcne (by simp [h])
  have hord3 : orderOf c = 3 := by
    have h : orderOf c ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hc3u
    rcases Nat.prime_three.eq_one_or_self_of_dvd (orderOf c) h with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hcne1
    · exact h3
  have hQp1u : c ^ (Q + 1) = 1 := Units.ext (by simpa using hQp1)
  have h : orderOf c ∣ Q + 1 := orderOf_dvd_iff_pow_eq_one.mpr hQp1u
  rwa [hord3] at h

private lemma three_dvd_Q_add_one_of_scalar_central {L : Type} [Field L] [Finite L] {n Q : ℕ}
    {τ : L ≃+* L} (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ Q) (hn : 1 ≤ n)
    {z : GL (Fin n) L} (hzGU : z ∈ heldGU n L τ hτ) {c : Lˣ}
    (hzc : z = Matrix.GeneralLinearGroup.scalar (Fin n) c) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    3 ∣ Q + 1 := by
  have hc3 : (c : L) ^ 3 = 1 := by
    have h : (Matrix.GeneralLinearGroup.scalar (Fin n) c) ^ 3 = 1 := by rw [← hzc]; exact hz3
    have h4 := congrArg (fun x : GL (Fin n) L => (x : Matrix (Fin n) (Fin n) L)) h
    rw [Units.val_pow_eq_pow_val, Units.val_one,
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.val_scalar_gl,
      ← Algebra.algebraMap_eq_smul_one, ← map_pow, Algebra.algebraMap_eq_smul_one] at h4
    have := congrFun (congrFun h4 ⟨0, hn⟩) ⟨0, hn⟩
    simpa using this
  have hcne : (c : L) ≠ 1 := by
    intro hc1
    apply hz1
    rw [hzc]
    apply Units.ext
    simp [CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.val_scalar_gl, hc1]
  exact three_dvd_Q_add_one_of_scalar_unitary hτ hτQ hn (by rw [← hzc]; exact hzGU) hc3 hcne

private lemma exists_central_order_three_of_equiv {K : Type} [Field K] {E : Type} [Field E]
    {m a : ℕ} {M : Subgroup (GL (Fin m) K)} {H : Subgroup (GL (Fin a) E)}
    (eM : ↥M ≃* ↥H) {z₀ : GL (Fin a) E} (hz₀H : z₀ ∈ H) (hz₀ne : z₀ ≠ 1)
    (hz₀3 : z₀ ^ 3 = 1) (hz₀cen : ∀ y ∈ H, z₀ * y = y * z₀) :
    ∃ z : GL (Fin m) K, z ∈ M ∧ z ≠ 1 ∧ z ^ 3 = 1 ∧ (∀ y ∈ M, z * y = y * z) := by
  let zM : ↥M := eM.symm ⟨z₀, hz₀H⟩
  refine ⟨(zM : GL (Fin m) K), zM.2, ?_, ?_, ?_⟩
  · intro h
    apply hz₀ne
    have h' : zM = 1 := Subtype.ext h
    have h2 : (⟨z₀, hz₀H⟩ : ↥H) = 1 := by
      calc (⟨z₀, hz₀H⟩ : ↥H) = eM zM := (MulEquiv.apply_symm_apply eM _).symm
        _ = eM 1 := by rw [h']
        _ = 1 := map_one eM
    simpa using congrArg (fun w : ↥H => (w : GL (Fin a) E)) h2
  · have hz0H3 : (⟨z₀, hz₀H⟩ : ↥H) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hz₀3
    have h : zM ^ 3 = 1 := by rw [← map_pow, hz0H3, map_one]
    simpa using congrArg (fun w : ↥M => (w : GL (Fin m) K)) h
  · intro y hy
    have h : zM * ⟨y, hy⟩ = ⟨y, hy⟩ * zM := by
      apply eM.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext (hz₀cen (eM ⟨y, hy⟩) (eM ⟨y, hy⟩).2)
    simpa using congrArg (fun w : ↥M => (w : GL (Fin m) K)) h


theorem k1419ClsUniDichot {L : Type} [Field L] [Finite L] {n Q : ℕ} {τ : L ≃+* L}
    (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ Q) (hL : Nat.card L = Q ^ 2)
    (hQ : ∃ j : ℕ, Q = 2 ^ j) (hn : 1 ≤ n) (A : GL (Fin n) L) (hA : A ∈ heldGU n L τ hτ)
    (hA3 : ∃ c : L, ((A ^ 3 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      c • (1 : Matrix (Fin n) (Fin n) L))
    (hAns : ∀ c : L, (A : Matrix (Fin n) (Fin n) L) ≠ c • (1 : Matrix (Fin n) (Fin n) L))
    (M : Subgroup (GL (Fin n) L))
    (hM : CFSG.Open.IsComponentOf M
      (Subgroup.centralizer ({A} : Set (GL (Fin n) L)) ⊓ heldSU n L τ hτ)) :
    (∃ (a dd : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ' : E ≃+* E)
        (hτ' : ∀ x, τ' (τ' x) = x), 2 ≤ a ∧ (∀ x : E, τ' x = x ^ (Q ^ dd)) ∧
        Nat.card E = (Q ^ dd) ^ 2 ∧
        Nonempty (M ⧸ Subgroup.center M ≃* heldSU a E τ' hτ' ⧸ Subgroup.center (heldSU a E τ' hτ')) ∧
        (3 ∣ dd ∨ ((3 ∣ a ∧ 3 ∣ Q ^ dd + 1) →
          ∃ z : GL (Fin n) L, z ∈ M ∧ z ≠ 1 ∧ z ^ 3 = 1 ∧ (∀ y ∈ M, z * y = y * z) ∧
            z ∉ StatedScalars (Fin n) L))) ∨
    (∃ (b e : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ b ∧ Nat.card E = Q ^ (2 * e) ∧
        Nonempty (M ⧸ Subgroup.center M ≃* StatedProj (StatedSL b E)) ∧
        (3 ∣ e ∨ (3 ∣ b →
          ∃ z : GL (Fin n) L, z ∈ M ∧ z ≠ 1 ∧ z ^ 3 = 1 ∧ (∀ y ∈ M, z * y = y * z) ∧
            z ∉ StatedScalars (Fin n) L))) := by
  obtain ⟨j, hQj⟩ := hQ
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h2 : (2 : L) = 0 :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.two_eq_zero_of_card (K := L) (n := j)
      (by rw [hL, hQj])
  obtain ⟨c, hc⟩ := hA3
  have hodd : Odd (orderOf A) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.odd_orderOf_of_pow_scalar h2 hn A
      (by norm_num : Odd 3) hc
  have hord : ((orderOf A : ℕ) : L) ≠ 0 :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.cast_orderOf_ne_zero_of_odd h2 A hodd
  have hA3mat : (A : Matrix (Fin n) (Fin n) L) ^ 3 = c • (1 : Matrix (Fin n) (Fin n) L) := by
    rw [← Units.val_pow_eq_pow_val]
    exact hc
  have hMgu : CFSG.Open.IsComponentOf M
      (Subgroup.centralizer ({A} : Set (GL (Fin n) L)) ⊓ heldGU n L τ hτ) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.isComponentOf_centralizer_gu_of_su hτ A hM
  obtain ⟨W, U, hWU, hWne, hfix, htype⟩ :=
    k1419ClsUniBlock hτ hτQ hL A hA hord M hMgu
  have h3L : 3 ∣ Nat.card L - 1 := by
    rw [hL, hQj]
    exact three_dvd_sq_two_pow_sub_one j
  have hω : ∃ w : L, w ^ 3 = 1 ∧ w ≠ 1 := exists_cube_root_unity_of_three_dvd h3L
  rcases htype with ⟨a, dd, E, hEfld, hEfin, τ', hτ', P, ha2, hτ'Q, hEcard, ⟨eM⟩, hirrP,
      hPdeg, hPkill⟩ | ⟨b, e, E, hEfld, hEfin, X, Y, P, P', hb2, hEcard, ⟨eM⟩, hWXY,
      hXne, hYne, hXi, hYi, hirrP, hPdeg, hirrP', hPkill, hP'kill⟩
  · left
    refine ⟨a, dd, E, hEfld, hEfin, τ', hτ', ha2, hτ'Q, hEcard, ?_, ?_⟩
    · exact ⟨QuotientGroup.congr (Subgroup.center M) (Subgroup.center (heldSU a E τ' hτ'))
        eM (Subgroup.map_center_eq eM)⟩
    · by_cases hdd : 3 ∣ dd
      · exact Or.inl hdd
      · right
        rintro ⟨ha3, hq3⟩
        letI : Field E := hEfld
        letI : Finite E := hEfin
        obtain ⟨z₀, hz₀SU, hz₀ne, hz₀3, hz₀cen⟩ :=
          k1419ClsUniCentreSU (q := Q ^ dd) ⟨j * dd, by rw [hQj, pow_mul]⟩ τ' hτ' hτ'Q
            hEcard ha2 ha3 hq3
        obtain ⟨z, hzM, hz1, hz3, hzcen⟩ :=
          exists_central_order_three_of_equiv (K := L) (E := E) eM hz₀SU hz₀ne hz₀3 hz₀cen
        refine ⟨z, hzM, hz1, hz3, hzcen, ?_⟩
        intro hzS
        rw [StatedScalars, MonoidHom.mem_range] at hzS
        obtain ⟨c₀, hc₀⟩ := hzS
        have hzc : (z : Matrix (Fin n) (Fin n) L) = c₀.1 • 1 := by
          rw [← hc₀]
          exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.val_scalar_gl c₀
        have hzGU : z ∈ heldGU n L τ hτ := (Subgroup.mem_inf.mp (hM.1 hzM).2).1
        by_cases hU : U = ⊥
        · have hWtop : W = ⊤ := by
            have h := hWU
            rw [hU] at h
            exact eq_top_of_isCompl_bot h
          have hP0 : Polynomial.aeval (A : Matrix (Fin n) (Fin n) L) P = 0 := by
            ext i k
            have hx : (Polynomial.aeval (A : Matrix (Fin n) (Fin n) L) P) *ᵥ
                (Pi.single k (1 : L)) = 0 := by
              apply hPkill
              rw [hWtop]
              exact Submodule.mem_top
            have := congrFun hx i
            simpa [Matrix.mulVec_single_one, Matrix.col_apply] using this
          let x₀ : Fin n → L := Pi.single (⟨0, hn⟩ : Fin n) (1 : L)
          have hx0 : x₀ ≠ 0 := by
            intro h
            have h1 : (1 : L) = 0 := by
              have := congrFun h ⟨0, hn⟩
              simpa [x₀] using this
            exact one_ne_zero h1
          have hdvd : P ∣ Polynomial.X ^ 3 - Polynomial.C c :=
            dvd_X_pow_three_sub_C_of_aeval_mulVec_eq_zero (A : Matrix (Fin n) (Fin n) L)
              hirrP hx0 (by rw [hP0]; simp) hA3mat
          have hP1 : P.natDegree = 1 :=
            natDegree_eq_one_of_irreducible_of_dvd hirrP hdvd hω (by rw [hPdeg]; exact hdd)
          have hm_dvd : minpoly L (A : Matrix (Fin n) (Fin n) L) ∣ P :=
            minpoly.dvd L (A : Matrix (Fin n) (Fin n) L) hP0
          have hm_le : (minpoly L (A : Matrix (Fin n) (Fin n) L)).natDegree ≤ 1 := by
            have := Polynomial.natDegree_le_of_dvd hm_dvd hirrP.ne_zero
            rwa [hP1] at this
          have hm_pos : 0 < (minpoly L (A : Matrix (Fin n) (Fin n) L)).natDegree :=
            minpoly.natDegree_pos (IsIntegral.of_finite L (A : Matrix (Fin n) (Fin n) L))
          have hm_eq : (minpoly L (A : Matrix (Fin n) (Fin n) L)).natDegree = 1 := by omega
          obtain ⟨c', hc'⟩ := (minpoly.natDegree_eq_one_iff (A := L)
            (B := Matrix (Fin n) (Fin n) L)).mp hm_eq
          exact hAns c' (by rw [← hc', Algebra.algebraMap_eq_smul_one])
        · obtain ⟨v, hvU, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
          have hzv : (z : Matrix (Fin n) (Fin n) L) *ᵥ v = v := hfix z hzM v hvU
          rw [hzc, Matrix.smul_mulVec, Matrix.one_mulVec] at hzv
          obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
          have hvi : c₀.1 * v i = v i := congrFun hzv i
          have hc1 : c₀.1 = 1 := by
            have hvi' : c₀.1 * v i = 1 * v i := by rw [hvi, one_mul]
            exact mul_right_cancel₀ hi hvi'
          exact hz1 (by
            apply Units.ext
            simp [hzc, hc1])
  · right
    refine ⟨b, e, E, hEfld, hEfin, hb2, hEcard, ?_, ?_⟩
    · exact CFSG.LieType.SemisimpleCentralizers.Held.nonempty_quotientCenter_equiv_statedProj eM
    · by_cases he : 3 ∣ e
      · exact Or.inl he
      · right
        intro hb3
        letI : Field E := hEfld
        letI : Finite E := hEfin
        have h3E : 3 ∣ Nat.card E - 1 := by
          rw [hEcard, hQj]
          exact three_dvd_two_pow_mul_sub_one j e
        obtain ⟨z₀, hz₀SL, hz₀ne, hz₀3, hz₀cen⟩ := k1419ClsUniCentreSL hb2 hb3 h3E
        obtain ⟨z, hzM, hz1, hz3, hzcen⟩ :=
          exists_central_order_three_of_equiv (K := L) (E := E) eM hz₀SL hz₀ne hz₀3 hz₀cen
        refine ⟨z, hzM, hz1, hz3, hzcen, ?_⟩
        intro hzS
        rw [StatedScalars, MonoidHom.mem_range] at hzS
        obtain ⟨c₀, hc₀⟩ := hzS
        have hzc : (z : Matrix (Fin n) (Fin n) L) = c₀.1 • 1 := by
          rw [← hc₀]
          exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.val_scalar_gl c₀
        have hzGU : z ∈ heldGU n L τ hτ := (Subgroup.mem_inf.mp (hM.1 hzM).2).1
        by_cases hU : U = ⊥
        · have hWtop : W = ⊤ := by
            have h := hWU
            rw [hU] at h
            exact eq_top_of_isCompl_bot h
          have hXY : X ⊔ Y = ⊤ := by rw [← hWXY, hWtop]
          obtain ⟨x, hxX, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hXne
          obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hYne
          have hdvdP : P ∣ Polynomial.X ^ 3 - Polynomial.C c :=
            dvd_X_pow_three_sub_C_of_aeval_mulVec_eq_zero (A : Matrix (Fin n) (Fin n) L)
              hirrP hx0 (hPkill x hxX) hA3mat
          have hP1 : P.natDegree = 1 :=
            natDegree_eq_one_of_irreducible_of_dvd hirrP hdvdP hω (by rw [hPdeg]; exact he)
          obtain ⟨p, hp⟩ := exists_eigenvalue_of_natDegree_eq_one hP1 hPkill
          have hp3 : p ^ 3 = c := pow_three_eq_of_eigenvalue hA3mat hx0 (hp x hxX)
          obtain ⟨ω, hω3, hωne⟩ := hω
          have hsplit : (Polynomial.X ^ 3 - Polynomial.C c : Polynomial L).Splits :=
            splits_X_pow_three_sub_C hω3 hωne hp3
          have hdvdP' : P' ∣ Polynomial.X ^ 3 - Polynomial.C c :=
            dvd_X_pow_three_sub_C_of_aeval_mulVec_eq_zero (A : Matrix (Fin n) (Fin n) L)
              hirrP' hy0 (hP'kill y hyY) hA3mat
          have hsplitP' : P'.Splits :=
            hsplit.of_dvd (Polynomial.X_pow_sub_C_ne_zero (by norm_num : 0 < 3) c) hdvdP'
          have hP'1 : P'.natDegree = 1 := hsplitP'.natDegree_eq_one_of_irreducible hirrP'
          obtain ⟨q, hq⟩ := exists_eigenvalue_of_natDegree_eq_one hP'1 hP'kill
          have hpq : p ≠ q := by
            intro hpq
            apply hAns p
            have hact : ∀ v : Fin n → L, (A : Matrix (Fin n) (Fin n) L) *ᵥ v = p • v := by
              intro v
              have hv : v ∈ X ⊔ Y := by rw [hXY]; exact Submodule.mem_top
              obtain ⟨x', hx'X, y', hy'Y, hxy⟩ := Submodule.mem_sup.mp hv
              rw [← hxy, Matrix.mulVec_add, hp x' hx'X, hq y' hy'Y, hpq, ← smul_add]
            ext i k
            have hk := congrFun (hact (Pi.single k (1 : L))) i
            rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at hk
            rw [hk]
            by_cases hik : i = k
            · subst hik
              simp [Pi.single_eq_same, Matrix.smul_apply, Matrix.one_apply]
            · rw [Pi.single_eq_of_ne hik, mul_zero]
              simp [Matrix.smul_apply, Matrix.one_apply, hik]
          have hQ3 : Q % 3 = 1 :=
            k1419ClsUniNu hτ hτQ hL ⟨j, hQj⟩ A hA c hc X Y hXY hXne hYne hXi hYi p q hp hq
              hpq
          have hQp1 : 3 ∣ Q + 1 :=
            three_dvd_Q_add_one_of_scalar_central hτ hτQ hn hzGU hc₀.symm hz3 hz1
          have hQm1 : 3 ∣ Q - 1 := by
            have hdiv := Nat.div_add_mod Q 3
            rw [hQ3] at hdiv
            exact ⟨Q / 3, by omega⟩
          have h2 : 3 ∣ (Q + 1) - (Q - 1) := Nat.dvd_sub hQp1 hQm1
          have h3 : (Q + 1) - (Q - 1) = 2 := by omega
          rw [h3] at h2
          exact absurd h2 (by norm_num)
        · obtain ⟨v, hvU, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
          have hzv : (z : Matrix (Fin n) (Fin n) L) *ᵥ v = v := hfix z hzM v hvU
          rw [hzc, Matrix.smul_mulVec, Matrix.one_mulVec] at hzv
          obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
          have hvi : c₀.1 * v i = v i := congrFun hzv i
          have hc1 : c₀.1 = 1 := by
            have hvi' : c₀.1 * v i = 1 * v i := by rw [hvi, one_mul]
            exact mul_right_cancel₀ hi hvi'
          exact hz1 (by
            apply Units.ext
            simp [hzc, hc1])

end CFSG.LocalAnalysis.GLTheoremA.K1419
