module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwAct
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwFrob
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNGenFix

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.Timmesfeld.ExceptionalOrders (zpowMatrix zpowMatrix_apply zpowMatrix_zpowMatrix)
open scoped commutatorElement Matrix

section Matrices

theorem det_one_sub_smul_ne_zero_of_pow_eq_one {r : ℕ} (X : Matrix (Fin r) (Fin r) ℤ) {n : ℕ}
    (hn : n ≠ 0) (hX : X ^ n = 1) {q : ℕ} (hq : 2 ≤ q) : (1 - (q : ℤ) • X).det ≠ 0 := by
  intro h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, sub_eq_zero] at hv
  have iter : ∀ j : ℕ, v = ((q : ℤ) ^ j) • ((X ^ j) *ᵥ v) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc v = ((q : ℤ) ^ j) • ((X ^ j) *ᵥ v) := ih
        _ = ((q : ℤ) ^ j) • ((X ^ j) *ᵥ ((q : ℤ) • (X *ᵥ v))) := by rw [← hv]
        _ = ((q : ℤ) ^ (j + 1)) • ((X ^ (j + 1)) *ᵥ v) := by
          rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_succ, smul_smul, ← pow_succ]
  have h1 := iter n
  rw [hX, Matrix.one_mulVec] at h1
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.1 hv0
  have h2 : v i = ((q : ℤ) ^ n) * v i := by
    conv_lhs => rw [h1]
    rfl
  have h3 : ((q : ℤ) ^ n) = 1 := by
    have : ((q : ℤ) ^ n - 1) * v i = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hi
  have h4 : (1 : ℤ) < (q : ℤ) ^ n := one_lt_pow₀ (by omega) hn
  omega

end Matrices

section Torus

variable {τ : Tag} {L : Type} [Field L]

@[expose] def twPermMat {r : ℕ} (ρ : Equiv.Perm (Fin r)) : Matrix (Fin r) (Fin r) ℤ :=
  Matrix.of fun i j => if i = ρ.symm j then 1 else 0

theorem zpowMatrix_twPermMat {r : ℕ} (ρ : Equiv.Perm (Fin r)) (c : Fin r → Lˣ) :
    zpowMatrix (twPermMat ρ) c = fun j => c (ρ.symm j) := by
  funext j
  rw [zpowMatrix_apply, Finset.prod_eq_single (ρ.symm j)]
  · simp [twPermMat]
  · intro i _ hi
    simp [twPermMat, hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem zpowMatrix_smul_one {r : ℕ} (q : ℤ) (b : Fin r → Lˣ) :
    zpowMatrix (q • (1 : Matrix (Fin r) (Fin r) ℤ)) b = fun i => b i ^ q := by
  funext j
  rw [zpowMatrix_apply, Finset.prod_eq_single j]
  · simp
  · intro i _ hi
    simp [Matrix.smul_apply, Matrix.one_apply, hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem weylTuple_perm_pow (ρ : Equiv.Perm (Fin τ.rank)) (w : WeylGroup τ) (q : ℕ)
    (c : Fin τ.rank → Lˣ) :
    weylTuple w (fun i => (c (ρ.symm i)) ^ q) =
      zpowMatrix ((q : ℤ) • (twPermMat ρ * weylMat w⁻¹)) c := by
  have h1 : (fun i => (c (ρ.symm i)) ^ q) =
      zpowMatrix ((q : ℤ) • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)) (zpowMatrix (twPermMat ρ) c) := by
    rw [zpowMatrix_smul_one, zpowMatrix_twPermMat]
    funext i
    exact (zpow_natCast _ _).symm
  rw [h1, weylTuple_eq_zpowMatrix, zpowMatrix_zpowMatrix, zpowMatrix_zpowMatrix, Matrix.smul_mul,
    Matrix.one_mul, Matrix.mul_smul]

theorem twPermMat_mul_weylMat_inv_mul (t : TwistTag) (w : WeylGroup t.tag)
    {M : Matrix (Fin t.tag.rank) (Fin t.tag.rank) ℤ}
    (hv : ∀ x, w • permLattice t.perm x = M *ᵥ x) :
    (twPermMat t.perm * weylMat w⁻¹) * M = 1 := by
  refine Matrix.ext_iff_mulVec.2 fun x => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hv, weylMat_mulVec, inv_smul_smul,
    Matrix.one_mulVec]
  funext i
  simp only [Matrix.mulVec, dotProduct, twPermMat, Matrix.of_apply, permLattice,
    Function.comp_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (t.perm i)]
  · simp
  · intro j _ hj
    have : i ≠ t.perm.symm j := fun h => hj (by rw [h]; simp)
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem twPermMat_mul_weylMat_inv_pow (t : TwistTag) (w : WeylGroup t.tag)
    {M : Matrix (Fin t.tag.rank) (Fin t.tag.rank) ℤ}
    (hv : ∀ x, w • permLattice t.perm x = M *ᵥ x) {n : ℕ} (hn0 : n ≠ 0) (hpow : M ^ n = 1) :
    (twPermMat t.perm * weylMat w⁻¹) ^ n = 1 := by
  set N := twPermMat t.perm * weylMat w⁻¹ with hN
  have hNM : N * M = 1 := twPermMat_mul_weylMat_inv_mul t w hv
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hMm : M * M ^ m = 1 := by rw [← pow_succ']; exact hpow
  have hNe : N = M ^ m := by
    calc N = N * (M * M ^ m) := by rw [hMm, mul_one]
      _ = (N * M) * M ^ m := (mul_assoc N M (M ^ m)).symm
      _ = M ^ m := by rw [hNM, one_mul]
  rw [hNe, ← pow_mul, mul_comm, pow_mul, hpow, one_pow]

end Torus

section Lang

variable {t : TwistTag} {L : Type} [Field L] [IsAlgClosed L]

theorem exists_twFrob_correction (Fr : L →+* L) {q : ℕ} (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q)
    (w : WeylGroup t.tag) {M : Matrix (Fin t.tag.rank) (Fin t.tag.rank) ℤ}
    (hv : ∀ x, w • permLattice t.perm x = M *ᵥ x) {n : ℕ} (hn0 : n ≠ 0) (hpow : M ^ n = 1)
    (a : Fin t.tag.rank → Lˣ) :
    ∃ c : Fin t.tag.rank → Lˣ, rootDiagUnit t.tag c *
      (twFrob t (canonicalRep (coxeterSystem t.tag) L w) Fr (rootDiagUnit t.tag c))⁻¹ =
        rootDiagUnit t.tag a := by
  have hdet := det_one_sub_smul_ne_zero_of_pow_eq_one (twPermMat t.perm * weylMat w⁻¹) hn0
    (twPermMat_mul_weylMat_inv_pow t w hv hn0 hpow) hq
  obtain ⟨c, hc⟩ := exists_zpowMatrix_eq _ hdet a
  refine ⟨c, ?_⟩
  rw [twFrob_rootDiagUnit]
  have hmap : (fun i => Units.map Fr.toMonoidHom (c (t.perm.symm i))) =
      fun i => (c (t.perm.symm i)) ^ q := by
    funext i
    exact CTTorus.map_units_eq_pow hFr _
  rw [hmap, weylTuple_perm_pow, rootDiagUnit_inv, ← rootDiagUnit_mul]
  congr 1
  rw [← hc, zpowMatrix_sub, CFSG.Timmesfeld.ExceptionalOrders.zpowMatrix_one]

theorem exists_twFrob_lift (Fr : L →+* L) {q : ℕ} (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q)
    (w : WeylGroup t.tag) {M : Matrix (Fin t.tag.rank) (Fin t.tag.rank) ℤ}
    (hv : ∀ x, w • permLattice t.perm x = M *ᵥ x) {n : ℕ} (hn0 : n ≠ 0) (hpow : M ^ n = 1)
    {u : WeylGroup t.tag} (hu : w * weylTwist t u = u * w) :
    ∃ t₁ ∈ torusGroup t.tag L,
      twFrob t (canonicalRep (coxeterSystem t.tag) L w) Fr
          (t₁ * canonicalRep (coxeterSystem t.tag) L u) =
        t₁ * canonicalRep (coxeterSystem t.tag) L u := by
  set n₀ := canonicalRep (coxeterSystem t.tag) L w with hn₀
  set nu := canonicalRep (coxeterSystem t.tag) L u with hnu
  set s : ModGL t.tag L := n₀ * twistHom t L Fr nu * n₀⁻¹ * nu⁻¹ with hs
  have hΦ : twistHom t L Fr nu = canonicalRep (coxeterSystem t.tag) L (weylTwist t u) :=
    twistHom_canonicalRep t L Fr u
  have hsm : s ∈ monomialSubgroup t.tag L := by
    rw [hs, hΦ]
    exact mul_mem (mul_mem (mul_mem (canonicalRep_mem_monomialSubgroup L w)
      (canonicalRep_mem_monomialSubgroup L _)) (inv_mem (canonicalRep_mem_monomialSubgroup L w)))
      (inv_mem (canonicalRep_mem_monomialSubgroup L u))
  have hs1 : MapsRootLines s 1 := by
    have h := (((mapsRootLines_canonicalRep (R := L) w).mul
      (mapsRootLines_canonicalRep (R := L) (weylTwist t u))).mul
        (mapsRootLines_canonicalRep (R := L) w).inv).mul
      (mapsRootLines_canonicalRep (R := L) u).inv
    have e : w * weylTwist t u * w⁻¹ * u⁻¹ = 1 := by
      rw [hu, mul_inv_cancel_right, mul_inv_cancel]
    rw [e] at h
    rw [hs, hΦ]
    exact h
  have hstor : s ∈ torusGroup t.tag L :=
    CFSG.LieType.Chevalley.mem_torusGroup_of_mapsRootLines_one hsm hs1
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hstor
  obtain ⟨c, hc⟩ := exists_twFrob_correction Fr hq hFr w hv hn0 hpow a
  rw [← ha] at hc
  have hF : twFrob t n₀ Fr (rootDiagUnit t.tag c) ∈ torusGroup t.tag L := by
    rw [twFrob_rootDiagUnit]
    exact rootDiagUnit_mem_torusGroup _
  have hcomm := torusGroup_mul_comm (rootDiagUnit_mem_torusGroup c) (inv_mem hF)
  refine ⟨rootDiagUnit t.tag c, rootDiagUnit_mem_torusGroup c, ?_⟩
  have e1 : twFrob t n₀ Fr nu = s * nu := by
    rw [twFrob_apply, hs]
    group
  rw [map_mul, e1, ← mul_assoc]
  congr 1
  rw [← hc]
  calc twFrob t n₀ Fr (rootDiagUnit t.tag c) *
        (rootDiagUnit t.tag c * (twFrob t n₀ Fr (rootDiagUnit t.tag c))⁻¹)
      = twFrob t n₀ Fr (rootDiagUnit t.tag c) *
        ((twFrob t n₀ Fr (rootDiagUnit t.tag c))⁻¹ * rootDiagUnit t.tag c) := by rw [hcomm]
    _ = rootDiagUnit t.tag c := by group

theorem twActsAs_lift {t₁ : ModGL t.tag L} (ht₁ : t₁ ∈ torusGroup t.tag L) (u : WeylGroup t.tag) :
    TwActsAs (t₁ * canonicalRep (coxeterSystem t.tag) L u) u :=
  (twActsAs_canonicalRep u).torus_mul ht₁

theorem lift_mem_monomialSubgroup {t₁ : ModGL t.tag L} (ht₁ : t₁ ∈ torusGroup t.tag L)
    (u : WeylGroup t.tag) :
    t₁ * canonicalRep (coxeterSystem t.tag) L u ∈ monomialSubgroup t.tag L :=
  mul_mem (torusGroup_le_monomialSubgroup' ht₁) (canonicalRep_mem_monomialSubgroup L u)

end Lang

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
