module

public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21

public section

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.ComponentClassification
open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

variable {n : ℕ} {K : Type*} [Field K]

theorem vv_mul_vv_of_dot (w ψ w' ψ' : Fin n → K) (h : ψ ⬝ᵥ w' = 0) :
    vecMulVec w ψ * vecMulVec w' ψ' = 0 := by
  rw [vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero]

theorem isNilpotent_smul_one_iff [NeZero n] {c : K} :
    IsNilpotent (c • (1 : Matrix (Fin n) (Fin n) K)) ↔ c = 0 := by
  constructor
  · rintro ⟨k, hk⟩
    have h := congrFun (congrFun hk 0) 0
    have h2 : (c • (1 : Matrix (Fin n) (Fin n) K)) ^ k = (c ^ k) • (1 : Matrix (Fin n) (Fin n) K) := by
      rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one, map_pow]
    rw [h2] at h
    exact (by simpa using h : c = 0 ∧ ¬ k = 0).1
  · rintro rfl
    exact ⟨1, by simp⟩

theorem eq_one_of_smul_one_add_nilpotent [NeZero n] {z y : Matrix (Fin n) (Fin n) K} {ζ : K}
    (hz : IsNilpotent z) (hy : IsNilpotent y) (h : ζ • (1 + z) = 1 + y) : ζ = 1 := by
  have hy' : y = (ζ - 1) • (1 : Matrix (Fin n) (Fin n) K) + ζ • z := by
    have : y = ζ • (1 + z) - 1 := by rw [h]; abel
    rw [this, smul_add, sub_smul, one_smul]; abel
  have hc : Commute y (ζ • z) := by
    rw [hy']
    refine Commute.add_left ?_ (Commute.refl _)
    exact (Commute.one_left _).smul_left _
  have hn : IsNilpotent (y - ζ • z) := hc.isNilpotent_sub hy (hz.smul ζ)
  have : y - ζ • z = (ζ - 1) • (1 : Matrix (Fin n) (Fin n) K) := by rw [hy']; abel
  rw [this, isNilpotent_smul_one_iff] at hn
  exact sub_eq_zero.1 hn

@[expose] def Wsp (N : Matrix (Fin n) (Fin n) K) : Submodule K (Fin n → K) :=
  LinearMap.ker N.mulVecLin ⊓ LinearMap.range N.mulVecLin

@[expose] def Fsp (N : Matrix (Fin n) (Fin n) K) : Submodule K (Fin n → K) :=
  LinearMap.ker N.vecMulLinear

theorem mem_Wsp {N : Matrix (Fin n) (Fin n) K} {w : Fin n → K} :
    w ∈ Wsp N ↔ N *ᵥ w = 0 ∧ ∃ v, N *ᵥ v = w := by
  simp [Wsp]

theorem mem_Fsp {N : Matrix (Fin n) (Fin n) K} {ψ : Fin n → K} :
    ψ ∈ Fsp N ↔ ψ ᵥ* N = 0 := by
  simp [Fsp]

theorem dot_eq_zero_of_mem {N : Matrix (Fin n) (Fin n) K} {w ψ : Fin n → K} (hw : w ∈ Wsp N)
    (hψ : ψ ∈ Fsp N) : ψ ⬝ᵥ w = 0 := by
  obtain ⟨-, v, rfl⟩ := mem_Wsp.1 hw
  rw [dotProduct_mulVec, mem_Fsp.1 hψ, zero_dotProduct]

theorem matrix_eq_zero_of_mulVec {M : Matrix (Fin n) (Fin n) K} (h : ∀ v, M *ᵥ v = 0) : M = 0 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa using this

theorem matrix_eq_zero_of_vecMul {M : Matrix (Fin n) (Fin n) K} (h : ∀ v, v ᵥ* M = 0) : M = 0 := by
  ext i j
  have := congrFun (h (Pi.single i 1)) j
  simpa using this

theorem exists_pow_ne_zero_pow_succ_eq_zero [NeZero n] {N : Matrix (Fin n) (Fin n) K}
    (hN : IsNilpotent N) (hN0 : N ≠ 0) : ∃ k, 1 ≤ k ∧ N ^ k ≠ 0 ∧ N ^ (k + 1) = 0 := by
  classical
  have hex : ∃ m, N ^ m = 0 := hN
  set m := Nat.find hex with hm
  have hm0 : N ^ m = 0 := Nat.find_spec hex
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have : m = 0 ∨ m = 1 := by omega
    rcases this with h | h
    · rw [h, pow_zero] at hm0; exact one_ne_zero hm0
    · rw [h, pow_one] at hm0; exact hN0 hm0
  refine ⟨m - 1, by omega, ?_, ?_⟩
  · exact Nat.find_min hex (by omega)
  · rw [show m - 1 + 1 = m by omega]; exact hm0

theorem exists_ne_zero_mem_Wsp [NeZero n] {N : Matrix (Fin n) (Fin n) K} (hN : IsNilpotent N)
    (hN0 : N ≠ 0) : ∃ w, w ≠ 0 ∧ w ∈ Wsp N := by
  obtain ⟨k, hk1, hk, hk2⟩ := exists_pow_ne_zero_pow_succ_eq_zero hN hN0
  by_contra hcon
  push Not at hcon
  apply hk
  apply matrix_eq_zero_of_mulVec
  intro v
  by_contra hv
  refine hv ?_
  have hw : N ^ k *ᵥ v ∈ Wsp N := by
    rw [mem_Wsp]
    refine ⟨?_, N ^ (k - 1) *ᵥ v, ?_⟩
    · rw [mulVec_mulVec, ← pow_succ', hk2, zero_mulVec]
    · rw [mulVec_mulVec, ← pow_succ']; congr 2; omega
  by_contra h
  exact hcon _ h hw

theorem exists_ne_zero_mem_Fsp [NeZero n] {N : Matrix (Fin n) (Fin n) K} (hN : IsNilpotent N)
    (hN0 : N ≠ 0) : ∃ ψ, ψ ≠ 0 ∧ ψ ∈ Fsp N := by
  obtain ⟨k, hk1, hk, hk2⟩ := exists_pow_ne_zero_pow_succ_eq_zero hN hN0
  by_contra hcon
  push Not at hcon
  apply hk
  apply matrix_eq_zero_of_vecMul
  intro v
  by_contra hv
  have hw : v ᵥ* N ^ k ∈ Fsp N := by
    rw [mem_Fsp, vecMul_vecMul, ← pow_succ, hk2, vecMul_zero]
  exact hcon _ hv hw

theorem rank_one_eq {a b w ψ : Fin n → K} (hw : w ≠ 0) (hψ : ψ ≠ 0)
    (h : vecMulVec a ψ = vecMulVec w b) : ∃ c : K, a = c • w ∧ b = c • ψ := by
  obtain ⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by
    by_contra h'; push Not at h'; exact hw (funext h')
  obtain ⟨j0, hj0⟩ : ∃ j, ψ j ≠ 0 := by
    by_contra h'; push Not at h'; exact hψ (funext h')
  have hent : ∀ i j, a i * ψ j = w i * b j := fun i j => by
    have := congrFun (congrFun h i) j
    simpa [vecMulVec_apply] using this
  refine ⟨a i0 / w i0, ?_, ?_⟩
  · funext i
    have h1 := hent i j0
    have h2 := hent i0 j0
    have key : a i * w i0 = w i * a i0 := by
      apply mul_right_cancel₀ hj0
      linear_combination w i0 * h1 - w i * h2
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination key
  · funext j
    have h1 := hent i0 j
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination -h1

theorem vecMulVec_ne_zero {w ψ : Fin n → K} (hw : w ≠ 0) (hψ : ψ ≠ 0) : vecMulVec w ψ ≠ 0 := by
  obtain ⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by
    by_contra h'; push Not at h'; exact hw (funext h')
  obtain ⟨j0, hj0⟩ : ∃ j, ψ j ≠ 0 := by
    by_contra h'; push Not at h'; exact hψ (funext h')
  intro h
  have := congrFun (congrFun h i0) j0
  simp [vecMulVec_apply] at this
  tauto

theorem dual_apply_eq_dot (f : Module.Dual K (Fin n → K)) (v : Fin n → K) :
    f v = (fun i => f (Pi.single i 1)) ⬝ᵥ v := by
  rw [LinearMap.pi_apply_eq_sum_univ f v, dotProduct, Finset.sum_congr rfl]
  intro i _
  rw [mul_comm, smul_eq_mul]
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

theorem mulVec_mem_range_of_vecMul_eq_zero {N B : Matrix (Fin n) (Fin n) K}
    (hB : ∀ ψ ∈ Fsp N, ψ ᵥ* B = 0) (y : Fin n → K) : ∃ v, N *ᵥ v = B *ᵥ y := by
  by_contra hno
  have hnot : B *ᵥ y ∉ LinearMap.range N.mulVecLin := by
    rintro ⟨v, hv⟩
    exact hno ⟨v, hv⟩
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  set ψ : Fin n → K := fun i => f (Pi.single i 1) with hψ
  have hψF : ψ ∈ Fsp N := by
    rw [mem_Fsp]
    funext j
    have h1 : f (N *ᵥ Pi.single j 1) = 0 := by
      have : f (N *ᵥ Pi.single j 1) ∈ Submodule.map f (LinearMap.range N.mulVecLin) :=
        Submodule.mem_map_of_mem ⟨Pi.single j 1, rfl⟩
      rw [hmap] at this
      simpa using this
    rw [dual_apply_eq_dot f, dotProduct_mulVec] at h1
    simpa using h1
  have := hB ψ hψF
  apply hf
  rw [dual_apply_eq_dot f]
  show ψ ⬝ᵥ B *ᵥ y = 0
  rw [dotProduct_mulVec, this, zero_dotProduct]

theorem exists_mul_eq_of_mulVec_mem_range {N B : Matrix (Fin n) (Fin n) K}
    (h : ∀ y, ∃ v, N *ᵥ v = B *ᵥ y) : ∃ C : Matrix (Fin n) (Fin n) K, N * C = B := by
  choose c hc using fun j : Fin n => h (Pi.single j 1)
  refine ⟨Matrix.of fun i j => c j i, ?_⟩
  ext i j
  have := congrFun (hc j) i
  simp only [mulVec_single_one] at this
  have h2 : (N * Matrix.of fun i j => c j i) i j = (N *ᵥ c j) i := by
    simp [mul_apply, mulVec, dotProduct]
  rw [h2, this]
  rfl

theorem pow_eq_pow_mul_pow_of_commute {N B C : Matrix (Fin n) (Fin n) K} (hNC : N * C = B)
    (hc : Commute B N) (j : ℕ) : B ^ j = N ^ j * C ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', ih]
    calc B * (N ^ j * C ^ j) = (B * N ^ j) * C ^ j := by rw [mul_assoc]
      _ = (N ^ j * B) * C ^ j := by rw [(hc.pow_right j).eq]
      _ = N ^ j * (N * C) * C ^ j := by rw [hNC]
      _ = N ^ (j + 1) * C ^ (j + 1) := by rw [pow_succ N j, pow_succ' C j]; simp only [mul_assoc]

theorem exists_nilpotent_sub_smul_one [NeZero n] {N A Ainv : Matrix (Fin n) (Fin n) K}
    (hN : IsNilpotent N) (hN0 : N ≠ 0) (hAinv : A * Ainv = 1) (hAN : A * N = N * A)
    (hAz : ∀ w ∈ Wsp N, ∀ ψ ∈ Fsp N, A * vecMulVec w ψ = vecMulVec w ψ * A) :
    ∃ c : K, c ≠ 0 ∧ IsNilpotent (A - c • (1 : Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨w0, hw0, hw0W⟩ := exists_ne_zero_mem_Wsp hN hN0
  obtain ⟨ψ0, hψ0, hψ0F⟩ := exists_ne_zero_mem_Fsp hN hN0
  have pair : ∀ w ∈ Wsp N, w ≠ 0 → ∀ ψ ∈ Fsp N, ψ ≠ 0 →
      ∃ c : K, A *ᵥ w = c • w ∧ ψ ᵥ* A = c • ψ := by
    intro w hw hwne ψ hψ hψne
    have h := hAz w hw ψ hψ
    rw [mul_vecMulVec, vecMulVec_mul] at h
    exact rank_one_eq hwne hψne h
  obtain ⟨c0, hc0w, hc0ψ⟩ := pair w0 hw0W hw0 ψ0 hψ0F hψ0
  have hW : ∀ w ∈ Wsp N, A *ᵥ w = c0 • w := by
    intro w hw
    by_cases hwz : w = 0
    · simp [hwz]
    · obtain ⟨c, hcw, hcψ⟩ := pair w hw hwz ψ0 hψ0F hψ0
      have : c = c0 := smul_left_injective K hψ0 (hcψ.symm.trans hc0ψ)
      rw [hcw, this]
  have hF : ∀ ψ ∈ Fsp N, ψ ᵥ* A = c0 • ψ := by
    intro ψ hψ
    by_cases hψz : ψ = 0
    · simp [hψz]
    · obtain ⟨c, hcw, hcψ⟩ := pair w0 hw0W hw0 ψ hψ hψz
      have : c = c0 := smul_left_injective K hw0 (hcw.symm.trans hc0w)
      rw [hcψ, this]
  set B : Matrix (Fin n) (Fin n) K := A - c0 • 1 with hBdef
  have hB : ∀ ψ ∈ Fsp N, ψ ᵥ* B = 0 := by
    intro ψ hψ
    rw [hBdef, vecMul_sub, hF ψ hψ, vecMul_smul, vecMul_one, sub_self]
  obtain ⟨C, hC⟩ := exists_mul_eq_of_mulVec_mem_range (mulVec_mem_range_of_vecMul_eq_zero hB)
  have hBN : Commute B N := by
    show B * N = N * B
    rw [hBdef, sub_mul, mul_sub, hAN]
    simp
  obtain ⟨k, hk⟩ := hN
  have hBnil : IsNilpotent B := ⟨k, by rw [pow_eq_pow_mul_pow_of_commute hC hBN k, hk, zero_mul]⟩
  refine ⟨c0, ?_, hBnil⟩
  rintro rfl
  have hA : A = B := by simp [hBdef]
  rw [hA] at hAinv
  obtain ⟨m, hm⟩ := hBnil
  have hcomm : Commute B Ainv := by
    show B * Ainv = Ainv * B
    rw [hAinv]; exact (mul_eq_one_comm.1 hAinv).symm
  have : (B * Ainv) ^ m = 1 := by rw [hAinv, one_pow]
  rw [hcomm.mul_pow, hm, zero_mul] at this
  exact zero_ne_one this

@[expose] def tvSL (w ψ : Fin n → K) (h : ψ ⬝ᵥ w = 0) : Matrix.SpecialLinearGroup (Fin n) K :=
  ⟨1 + vecMulVec w ψ, by
    rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, h, add_zero]⟩

@[simp] theorem coe_tvSL (w ψ : Fin n → K) (h : ψ ⬝ᵥ w = 0) :
    (tvSL w ψ h : Matrix (Fin n) (Fin n) K) = 1 + vecMulVec w ψ := rfl

theorem coe_inv_of_mul_eq_one (s : Matrix.SpecialLinearGroup (Fin n) K) {M : Matrix (Fin n) (Fin n) K}
    (h : (s : Matrix (Fin n) (Fin n) K) * M = 1) :
    ((s⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = M := by
  have h1 : ((s⁻¹ * s : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [inv_mul_cancel]; rfl
  rw [Matrix.SpecialLinearGroup.coe_mul] at h1
  calc ((s⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
      = (s⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) * ((s : Matrix (Fin n) (Fin n) K) * M) := by
        rw [h, mul_one]
    _ = M := by rw [← mul_assoc, h1, one_mul]

theorem exists_smul_of_proj_eq {s s' : Matrix.SpecialLinearGroup (Fin n) K}
    (h : proj n K s' = proj n K s) :
    ∃ c : K, (s' : Matrix (Fin n) (Fin n) K) = c • (s : Matrix (Fin n) (Fin n) K) := by
  have h1 := proj_eq_proj_iff.1 h.symm
  obtain ⟨c, -, hc⟩ := mem_scalars.1 h1
  refine ⟨(c : K), ?_⟩
  have h2 : s' = s * (s⁻¹ * s') := by group
  rw [h2, Matrix.SpecialLinearGroup.coe_mul, hc, scalar_apply, ← smul_one_eq_diagonal, mul_smul_comm,
    mul_one]

theorem exists_pow_prime_pow_ge {p m : ℕ} (hp : 1 < p) : ∃ e : ℕ, m ≤ p ^ e :=
  ⟨m, (Nat.lt_pow_self hp).le⟩

theorem add_smul_one_pow_prime_pow [NeZero n] {p : ℕ} [Fact p.Prime] [CharP K p]
    {B : Matrix (Fin n) (Fin n) K} (hB : IsNilpotent B) (c : K) :
    ∃ e : ℕ, (c • (1 : Matrix (Fin n) (Fin n) K) + B) ^ p ^ e =
      (c ^ p ^ e) • (1 : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨m, hm⟩ := hB
  obtain ⟨e, he⟩ := exists_pow_prime_pow_ge (m := m) (Fact.out : p.Prime).one_lt
  refine ⟨e, ?_⟩
  rw [add_pow_char_pow_of_commute (R := Matrix (Fin n) (Fin n) K) p e
    ((Commute.one_left _).smul_left c), pow_eq_zero_of_le he hm, add_zero]
  rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one, map_pow]

theorem det_one_add_smul_of_isNilpotent [NeZero n] {p : ℕ} [Fact p.Prime] [CharP K p]
    {N : Matrix (Fin n) (Fin n) K} (hN : IsNilpotent N) (t : K) : (1 + t • N).det = 1 := by
  have hnil : IsNilpotent (t • N) := hN.smul t
  obtain ⟨e, he⟩ := add_smul_one_pow_prime_pow (p := p) hnil 1
  rw [one_smul, one_pow, one_smul] at he
  have h1 : (1 + t • N).det ^ p ^ e = 1 := by
    rw [← det_pow, he, det_one]
  have h2 : ((1 + t • N).det - 1) ^ p ^ e = 0 := by
    rw [sub_pow_char_pow, h1, one_pow, sub_self]
  exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) |>.1 h2)

@[expose] def uniSL {p : ℕ} [Fact p.Prime] [CharP K p] [NeZero n] (N : Matrix (Fin n) (Fin n) K)
    (hN : IsNilpotent N) (t : K) : Matrix.SpecialLinearGroup (Fin n) K :=
  ⟨1 + t • N, det_one_add_smul_of_isNilpotent (p := p) hN t⟩

@[simp] theorem coe_uniSL {p : ℕ} [Fact p.Prime] [CharP K p] [NeZero n]
    (N : Matrix (Fin n) (Fin n) K) (hN : IsNilpotent N) (t : K) :
    (uniSL (p := p) N hN t : Matrix (Fin n) (Fin n) K) = 1 + t • N := rfl

@[expose] noncomputable def autSL (A : GL (Fin n) K) (σ : K ≃+* K) (ε : ℕ) (s : Matrix.SpecialLinearGroup (Fin n) K) :
    Matrix.SpecialLinearGroup (Fin n) K :=
  CatalogueBHigherLinearAction.slConjugation n K A
    (Matrix.SpecialLinearGroup.map σ.toRingHom (if ε = 0 then s else (s⁻¹).transpose))

theorem aut_apply_proj (A : GL (Fin n) K) (σ : K ≃+* K) {ε : ℕ} (hε : ε ≤ 1)
    (s : Matrix.SpecialLinearGroup (Fin n) K) :
    (conjAut n K A * fieldAut n K σ * dualAut n K ^ ε) (proj n K s) = proj n K (autSL A σ ε s) := by
  interval_cases ε
  · simp [autSL, MulAut.mul_apply, conjAut_proj, fieldAut_proj]
  · simp [autSL, MulAut.mul_apply, conjAut_proj, fieldAut_proj, dualAut_proj]

theorem coe_autSL_zero (A : GL (Fin n) K) (σ : K ≃+* K) (s : Matrix.SpecialLinearGroup (Fin n) K) :
    (autSL A σ 0 s : Matrix (Fin n) (Fin n) K) =
      (A : Matrix (Fin n) (Fin n) K) * σ.toRingHom.mapMatrix (s : Matrix (Fin n) (Fin n) K) *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  simp [autSL, coe_slConjugation, Matrix.SpecialLinearGroup.map_apply_coe]

theorem coe_autSL_one (A : GL (Fin n) K) (σ : K ≃+* K) (s : Matrix.SpecialLinearGroup (Fin n) K) :
    (autSL A σ 1 s : Matrix (Fin n) (Fin n) K) =
      (A : Matrix (Fin n) (Fin n) K) *
        σ.toRingHom.mapMatrix ((s⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K)ᵀ * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  simp [autSL, coe_slConjugation, Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.SpecialLinearGroup.coe_transpose]

theorem mapMatrix_one_add_vecMulVec (σ : K →+* K) (w ψ : Fin n → K) :
    σ.mapMatrix (1 + vecMulVec w ψ) = 1 + vecMulVec (σ ∘ w) (σ ∘ ψ) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [vecMulVec_apply]
  · simp [vecMulVec_apply, h]

theorem conj_one_add {A Ainv : Matrix (Fin n) (Fin n) K} (hA : A * Ainv = 1)
    (X : Matrix (Fin n) (Fin n) K) : A * (1 + X) * Ainv = 1 + A * X * Ainv := by
  rw [mul_add, add_mul, mul_one, hA]

theorem isNilpotent_conj {A Ainv X : Matrix (Fin n) (Fin n) K} (hA : A * Ainv = 1)
    (hA' : Ainv * A = 1) (hX : IsNilpotent X) : IsNilpotent (A * X * Ainv) := by
  obtain ⟨m, hm⟩ := hX
  refine ⟨m, ?_⟩
  have : ∀ k : ℕ, (A * X * Ainv) ^ k = A * X ^ k * Ainv := by
    intro k
    induction k with
    | zero => simp [hA]
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      calc A * X ^ k * Ainv * (A * X * Ainv) = A * X ^ k * (Ainv * A) * X * Ainv := by
            simp only [mul_assoc]
        _ = A * (X ^ k * X) * Ainv := by rw [hA', mul_one]; simp only [mul_assoc]
  rw [this, hm]; simp

theorem conj_vecMulVec_eq_of_fix [NeZero n] {A Ainv : Matrix (Fin n) (Fin n) K}
    (hA : A * Ainv = 1) (hA' : Ainv * A = 1) (σ : K →+* K) {w ψ : Fin n → K} (h : ψ ⬝ᵥ w = 0)
    {ζ : K} (hζ : A * σ.mapMatrix (1 + vecMulVec w ψ) * Ainv = ζ • (1 + vecMulVec w ψ)) :
    A * vecMulVec (σ ∘ w) (σ ∘ ψ) * Ainv = vecMulVec w ψ := by
  rw [mapMatrix_one_add_vecMulVec, conj_one_add hA] at hζ
  have hz : IsNilpotent (vecMulVec w ψ) :=
    ⟨2, by rw [pow_two, vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero]⟩
  have hd : (σ ∘ ψ) ⬝ᵥ (σ ∘ w) = 0 := by
    rw [← RingHom.map_dotProduct, h, map_zero]
  have hy : IsNilpotent (A * vecMulVec (σ ∘ w) (σ ∘ ψ) * Ainv) :=
    isNilpotent_conj hA hA' ⟨2, by
      rw [pow_two, vecMulVec_mul_vecMulVec, hd, zero_smul, vecMulVec_zero]⟩
  have hζ1 : ζ = 1 := eq_one_of_smul_one_add_nilpotent hz hy hζ.symm
  rw [hζ1, one_smul] at hζ
  exact add_left_cancel hζ

theorem mapMatrix_eq_self {σ : K →+* K} (hσ : ∀ t, σ t = t) (M : Matrix (Fin n) (Fin n) K) :
    σ.mapMatrix M = M := by
  ext i j; simp [hσ]

theorem branch_zero {p : ℕ} [Fact p.Prime] [CharP K p] [NeZero n]
    {N : Matrix (Fin n) (Fin n) K} (hN : IsNilpotent N) (hN0 : N ≠ 0)
    (A : GL (Fin n) K) (σ : K ≃+* K)
    (hfixT : ∀ (s : Matrix.SpecialLinearGroup (Fin n) K) (t : K),
      (s : Matrix (Fin n) (Fin n) K) = 1 + t • N →
      ∃ ζ : K, (autSL A σ 0 s : Matrix (Fin n) (Fin n) K) = ζ • (s : Matrix (Fin n) (Fin n) K))
    (hfixG : ∀ (w ψ : Fin n → K) (h : ψ ⬝ᵥ w = 0), w ∈ Wsp N → ψ ∈ Fsp N →
      ∃ ζ : K, (autSL A σ 0 (tvSL w ψ h) : Matrix (Fin n) (Fin n) K) =
        ζ • (tvSL w ψ h : Matrix (Fin n) (Fin n) K)) :
    (∀ t, σ t = t) ∧ ∃ c : K, c ≠ 0 ∧ IsNilpotent ((A : Matrix (Fin n) (Fin n) K) - c • 1) := by
  set Ainv : Matrix (Fin n) (Fin n) K := ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hAinv
  have hA : (A : Matrix (Fin n) (Fin n) K) * Ainv = 1 := A.mul_inv
  have hA' : Ainv * (A : Matrix (Fin n) (Fin n) K) = 1 := A.inv_mul
  obtain ⟨w0, hw0, hw0W⟩ := exists_ne_zero_mem_Wsp hN hN0
  obtain ⟨ψ0, hψ0, hψ0F⟩ := exists_ne_zero_mem_Fsp hN hN0
  have hz : ∀ (w ψ : Fin n → K) (h : ψ ⬝ᵥ w = 0), w ∈ Wsp N → ψ ∈ Fsp N →
      (A : Matrix (Fin n) (Fin n) K) * vecMulVec (σ ∘ w) (σ ∘ ψ) * Ainv = vecMulVec w ψ := by
    intro w ψ h hw hψ
    obtain ⟨ζ, hζ⟩ := hfixG w ψ h hw hψ
    rw [coe_autSL_zero, coe_tvSL] at hζ
    exact conj_vecMulVec_eq_of_fix hA hA' σ.toRingHom h hζ
  have hσ : ∀ t, σ t = t := by
    intro t
    have e1 := hz w0 ψ0 (dot_eq_zero_of_mem hw0W hψ0F) hw0W hψ0F
    have hw' : t • w0 ∈ Wsp N := Submodule.smul_mem _ t hw0W
    have e2 := hz (t • w0) ψ0 (dot_eq_zero_of_mem hw' hψ0F) hw' hψ0F
    have hs : (σ ∘ (t • w0)) = σ t • (σ ∘ w0) := by
      funext i; simp
    rw [hs, smul_vecMulVec, Matrix.mul_smul, Matrix.smul_mul, e1, smul_vecMulVec] at e2
    exact smul_left_injective K (vecMulVec_ne_zero hw0 hψ0) e2
  have hmap : ∀ M : Matrix (Fin n) (Fin n) K, σ.toRingHom.mapMatrix M = M :=
    fun M => mapMatrix_eq_self (σ := σ.toRingHom) hσ M
  have hAz : ∀ w ∈ Wsp N, ∀ ψ ∈ Fsp N,
      (A : Matrix (Fin n) (Fin n) K) * vecMulVec w ψ = vecMulVec w ψ * (A : Matrix (Fin n) (Fin n) K) := by
    intro w hw ψ hψ
    have h := hz w ψ (dot_eq_zero_of_mem hw hψ) hw hψ
    have e1 : (σ ∘ w) = w := funext fun i => hσ _
    have e2 : (σ ∘ ψ) = ψ := funext fun i => hσ _
    rw [e1, e2] at h
    calc (A : Matrix (Fin n) (Fin n) K) * vecMulVec w ψ
        = (A * vecMulVec w ψ * Ainv) * A := by rw [mul_assoc _ Ainv, hA', mul_one]
      _ = vecMulVec w ψ * A := by rw [h]
  have hAN : (A : Matrix (Fin n) (Fin n) K) * N = N * (A : Matrix (Fin n) (Fin n) K) := by
    obtain ⟨ζ, hζ⟩ := hfixT (uniSL (p := p) N hN 1) 1 (by simp)
    rw [coe_autSL_zero, coe_uniSL, hmap, one_smul, conj_one_add hA] at hζ
    have hy : IsNilpotent ((A : Matrix (Fin n) (Fin n) K) * N * Ainv) :=
      isNilpotent_conj hA hA' hN
    have hζ1 : ζ = 1 := eq_one_of_smul_one_add_nilpotent hN hy hζ.symm
    rw [hζ1, one_smul] at hζ
    have h2 := add_left_cancel hζ
    calc (A : Matrix (Fin n) (Fin n) K) * N
        = (A * N * Ainv) * A := by rw [mul_assoc _ Ainv, hA', mul_one]
      _ = N * A := by rw [h2]
  exact ⟨hσ, exists_nilpotent_sub_smul_one hN hN0 hA hAN hAz⟩

theorem isNilpotent_map_transpose (σ : K →+* K) {X : Matrix (Fin n) (Fin n) K}
    (hX : IsNilpotent X) : IsNilpotent (σ.mapMatrix Xᵀ) := by
  obtain ⟨m, hm⟩ := hX
  exact ⟨m, by rw [← map_pow, ← transpose_pow, hm, transpose_zero, map_zero]⟩

theorem isNilpotent_inv_sub_one {N Y : Matrix (Fin n) (Fin n) K} (hN : IsNilpotent N) {t : K}
    (ht : t ≠ 0) (hY1 : (1 + t • N) * Y = 1) (hY2 : Y * (1 + t • N) = 1) :
    IsNilpotent (Y - 1) := by
  have hYN : Y * N = N * Y := by
    have h1 : t • (Y * N) = t • (N * Y) := by
      have : Y * (1 + t • N) = (1 + t • N) * Y := by rw [hY1, hY2]
      simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc] at this
      exact add_left_cancel this
    exact smul_right_injective _ ht h1
  have h : Y + t • (Y * N) = 1 := by
    have := hY2
    simpa only [mul_add, mul_one, mul_smul_comm] using this
  have : Y - 1 = -(t • (Y * N)) := by
    calc Y - 1 = (Y + t • (Y * N)) - 1 - t • (Y * N) := by abel
      _ = -(t • (Y * N)) := by rw [h]; abel
  rw [this]
  exact (((Commute.isNilpotent_mul_left (show Commute Y N from hYN) hN)).smul t).neg

theorem mapMatrix_transpose_one_add_smul (σ : K →+* K) (t : K) (X : Matrix (Fin n) (Fin n) K) :
    σ.mapMatrix (1 + t • X)ᵀ = 1 + σ t • σ.mapMatrix Xᵀ := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

theorem rel_of_fix_one [NeZero n] {p : ℕ} [Fact p.Prime] [CharP K p]
    {N : Matrix (Fin n) (Fin n) K} (hN : IsNilpotent N)
    (A : GL (Fin n) K) (σ : K ≃+* K) {t : K} (ht : t ≠ 0)
    (hfix : ∃ ζ : K, (autSL A σ 1 (uniSL (p := p) N hN t) : Matrix (Fin n) (Fin n) K) =
      ζ • ((uniSL (p := p) N hN t : Matrix.SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K)) :
    (1 + σ t • ((A : Matrix (Fin n) (Fin n) K) * σ.toRingHom.mapMatrix Nᵀ *
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) * (1 + t • N) = 1 := by
  have hA : (A : Matrix (Fin n) (Fin n) K) * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
    A.mul_inv
  have hA' : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1 :=
    A.inv_mul
  obtain ⟨ζ, hζ⟩ := hfix
  rw [coe_autSL_one, coe_uniSL] at hζ
  generalize ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Ainv at hA hA' hζ ⊢
  have hY1 : (1 + t • N) * ((uniSL (p := p) N hN t)⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) = 1 := by
    have : ((uniSL (p := p) N hN t * (uniSL (p := p) N hN t)⁻¹ :
        Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [mul_inv_cancel]; rfl
    rwa [Matrix.SpecialLinearGroup.coe_mul] at this
  have hY2 : (((uniSL (p := p) N hN t)⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) * (1 + t • N) = 1 := by
    have : (((uniSL (p := p) N hN t)⁻¹ * uniSL (p := p) N hN t :
        Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [inv_mul_cancel]; rfl
    rwa [Matrix.SpecialLinearGroup.coe_mul] at this
  generalize (((uniSL (p := p) N hN t)⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
    Matrix (Fin n) (Fin n) K) = Y at hY1 hY2 hζ
  have hYnil := isNilpotent_inv_sub_one hN ht hY1 hY2
  have hy : IsNilpotent ((A : Matrix (Fin n) (Fin n) K) * σ.toRingHom.mapMatrix (Y - 1)ᵀ * Ainv) :=
    isNilpotent_conj hA hA' (isNilpotent_map_transpose σ.toRingHom hYnil)
  have hP : (A : Matrix (Fin n) (Fin n) K) * σ.toRingHom.mapMatrix Yᵀ * Ainv =
      1 + (A : Matrix (Fin n) (Fin n) K) * σ.toRingHom.mapMatrix (Y - 1)ᵀ * Ainv := by
    rw [transpose_sub, transpose_one, map_sub, map_one, mul_sub, sub_mul, mul_one, hA]; abel
  have hζ1 : ζ = 1 := by
    refine eq_one_of_smul_one_add_nilpotent (hN.smul t) hy ?_
    rw [← hP, ← hζ]
  rw [hζ1, one_smul] at hζ
  have hQP : ((A : Matrix (Fin n) (Fin n) K) * σ.toRingHom.mapMatrix (1 + t • N)ᵀ * Ainv) *
      ((A : Matrix (Fin n) (Fin n) K) * σ.toRingHom.mapMatrix Yᵀ * Ainv) = 1 := by
    have h1 : σ.toRingHom.mapMatrix (1 + t • N)ᵀ * σ.toRingHom.mapMatrix Yᵀ = 1 := by
      rw [← map_mul, ← transpose_mul, hY2, transpose_one, map_one]
    calc ((A : Matrix (Fin n) (Fin n) K) * σ.toRingHom.mapMatrix (1 + t • N)ᵀ * Ainv) *
        ((A : Matrix (Fin n) (Fin n) K) * σ.toRingHom.mapMatrix Yᵀ * Ainv)
        = (A : Matrix (Fin n) (Fin n) K) * (σ.toRingHom.mapMatrix (1 + t • N)ᵀ * (Ainv * (A : Matrix (Fin n) (Fin n) K)) * σ.toRingHom.mapMatrix Yᵀ) * Ainv := by
          simp only [mul_assoc]
      _ = 1 := by rw [hA', mul_one, h1, mul_one, hA]
  rw [hζ, mapMatrix_transpose_one_add_smul, conj_one_add hA, Matrix.mul_smul, Matrix.smul_mul] at hQP
  exact hQP

theorem branch_one_nn [NeZero n] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {N : Matrix (Fin n) (Fin n) K} (hN : IsNilpotent N) (A : GL (Fin n) K) (σ : K ≃+* K)
    (hfixT : ∀ (s : Matrix.SpecialLinearGroup (Fin n) K) (t : K),
      (s : Matrix (Fin n) (Fin n) K) = 1 + t • N →
      ∃ ζ : K, (autSL A σ 1 s : Matrix (Fin n) (Fin n) K) = ζ • (s : Matrix (Fin n) (Fin n) K)) :
    N * N = 0 := by
  set M : Matrix (Fin n) (Fin n) K := (A : Matrix (Fin n) (Fin n) K) * σ.toRingHom.mapMatrix Nᵀ *
    ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM
  have h1 := rel_of_fix_one (p := p) hN A σ (one_ne_zero (α := K)) (hfixT _ 1 rfl)
  have h2 := rel_of_fix_one (p := p) hN A σ (neg_ne_zero.2 (one_ne_zero (α := K)))
    (hfixT _ (-1) rfl)
  rw [← hM] at h1 h2
  simp only [map_one, one_smul, map_neg, neg_smul] at h1 h2
  have e1 : M + N + M * N = 0 := by
    have : (1 + M) * (1 + N) - 1 = 0 := by rw [h1]; simp
    rw [← this]; noncomm_ring
  have e2 : -M - N + M * N = 0 := by
    have : (1 + -M) * (1 + -N) - 1 = 0 := by rw [h2]; simp
    rw [← this]; noncomm_ring
  have h2' : (2 : K) • (M * N) = 0 := by
    have : (2 : K) • (M * N) = (M + N + M * N) + (-M - N + M * N) := by module
    rw [this, e1, e2, add_zero]
  have h2K : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 this)
  have hMN : M * N = 0 := by
    rcases smul_eq_zero.1 h2' with h | h
    · exact absurd h h2K
    · exact h
  have hMneg : M = -N := by
    have : M + N = 0 := by rw [hMN, add_zero] at e1; exact e1
    exact eq_neg_of_add_eq_zero_left this
  rw [hMneg, neg_mul, neg_eq_zero] at hMN
  exact hMN

theorem mapMatrix_transpose_one_sub_vecMulVec (σ : K →+* K) (w ψ : Fin n → K) :
    σ.mapMatrix (1 - vecMulVec w ψ)ᵀ = 1 - vecMulVec (σ ∘ ψ) (σ ∘ w) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [vecMulVec_apply]
  · simp [vecMulVec_apply, Matrix.one_apply_ne h]

theorem conj_one_sub {A Ainv : Matrix (Fin n) (Fin n) K} (hA : A * Ainv = 1)
    (X : Matrix (Fin n) (Fin n) K) : A * (1 - X) * Ainv = 1 - A * X * Ainv := by
  rw [mul_sub, sub_mul, mul_one, hA]

theorem branch_one_pair [NeZero n] (A : GL (Fin n) K) (σ : K ≃+* K) {w ψ : Fin n → K}
    (h : ψ ⬝ᵥ w = 0) {ζ : K}
    (hζ : (autSL A σ 1 (tvSL w ψ h) : Matrix (Fin n) (Fin n) K) =
      ζ • (tvSL w ψ h : Matrix (Fin n) (Fin n) K)) (hw : w ≠ 0) (hψ : ψ ≠ 0) :
    ∃ c : K, w = c • ((A : Matrix (Fin n) (Fin n) K) *ᵥ (σ ∘ ψ)) := by
  have hA : (A : Matrix (Fin n) (Fin n) K) * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
    A.mul_inv
  have hA' : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1 :=
    A.inv_mul
  have hzz : vecMulVec w ψ * vecMulVec w ψ = 0 := by
    rw [vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero]
  have hinv : ((tvSL w ψ h)⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) =
      (1 - vecMulVec w ψ : Matrix (Fin n) (Fin n) K) := by
    apply coe_inv_of_mul_eq_one
    rw [coe_tvSL]
    calc (1 + vecMulVec w ψ) * (1 - vecMulVec w ψ) = 1 - vecMulVec w ψ * vecMulVec w ψ := by
          noncomm_ring
      _ = 1 := by rw [hzz, sub_zero]
  rw [coe_autSL_one, coe_tvSL, hinv, mapMatrix_transpose_one_sub_vecMulVec] at hζ
  generalize ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Ainv at hA hA' hζ
  rw [conj_one_sub hA] at hζ
  have hd : (σ.toRingHom ∘ ψ) ⬝ᵥ (σ.toRingHom ∘ w) = 0 := by
    rw [← RingHom.map_dotProduct, h, map_zero]
  have hy : IsNilpotent (-((A : Matrix (Fin n) (Fin n) K) *
      vecMulVec (σ.toRingHom ∘ ψ) (σ.toRingHom ∘ w) * Ainv)) :=
    (isNilpotent_conj hA hA' ⟨2, by
      rw [pow_two, vecMulVec_mul_vecMulVec, dotProduct_comm, hd, zero_smul, vecMulVec_zero]⟩).neg
  have hz : IsNilpotent (vecMulVec w ψ) := ⟨2, by rw [pow_two, hzz]⟩
  have hζ1 : ζ = 1 := by
    refine eq_one_of_smul_one_add_nilpotent hz hy ?_
    rw [← hζ, sub_eq_add_neg]
  rw [hζ1, one_smul] at hζ
  have h3 : vecMulVec ((A : Matrix (Fin n) (Fin n) K) *ᵥ (σ.toRingHom ∘ ψ))
      ((σ.toRingHom ∘ w) ᵥ* Ainv) = -vecMulVec w ψ := by
    rw [← vecMulVec_mul, ← mul_vecMulVec]
    have h5 := hζ
    rw [sub_eq_add_neg] at h5
    have h6 := add_left_cancel h5
    exact neg_eq_iff_eq_neg.1 h6
  have h4 : vecMulVec w ψ = vecMulVec ((A : Matrix (Fin n) (Fin n) K) *ᵥ (σ.toRingHom ∘ ψ))
      (-((σ.toRingHom ∘ w) ᵥ* Ainv)) := by
    ext i j
    have := congrFun (congrFun h3 i) j
    simp only [vecMulVec_apply, Matrix.neg_apply, Pi.neg_apply] at this ⊢
    linear_combination this
  have hane : (A : Matrix (Fin n) (Fin n) K) *ᵥ (σ.toRingHom ∘ ψ) ≠ 0 := by
    intro h0
    rw [h0] at h4
    have : vecMulVec (0 : Fin n → K) (-((σ.toRingHom ∘ w) ᵥ* Ainv)) = 0 := by
      ext i j; simp [vecMulVec_apply]
    rw [this] at h4
    exact vecMulVec_ne_zero hw hψ h4
  obtain ⟨c, hc, -⟩ := rank_one_eq hane hψ h4
  exact ⟨c, hc⟩

theorem two_le_finrank_Fsp (hn : 3 ≤ n) {N : Matrix (Fin n) (Fin n) K} (hNN : N * N = 0) :
    2 ≤ Module.finrank K (Fsp N) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker N.vecMulLinear
  have h2 := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  rw [Module.finrank_fin_fun] at h1 h2
  have hrank : Module.finrank K (LinearMap.range N.vecMulLinear) =
      Module.finrank K (LinearMap.range N.mulVecLin) := by
    have e : N.vecMulLinear = Nᵀ.mulVecLin := by
      ext ψ : 1
      simp
    rw [e]
    exact Matrix.rank_transpose N
  have hle : Module.finrank K (LinearMap.range N.mulVecLin) ≤
      Module.finrank K (LinearMap.ker N.mulVecLin) := by
    apply Submodule.finrank_mono
    rintro _ ⟨v, rfl⟩
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hNN,
      Matrix.zero_mulVec]
  have : Fsp N = LinearMap.ker N.vecMulLinear := rfl
  rw [this]
  omega

theorem no_branch_one [NeZero n] [Finite K] (hn : 3 ≤ n) {N : Matrix (Fin n) (Fin n) K}
    (hN : IsNilpotent N) (hN0 : N ≠ 0) (hNN : N * N = 0) (A : GL (Fin n) K) (σ : K ≃+* K)
    (hpair : ∀ (w ψ : Fin n → K) (h : ψ ⬝ᵥ w = 0), w ∈ Wsp N → ψ ∈ Fsp N → w ≠ 0 → ψ ≠ 0 →
      ∃ c : K, w = c • ((A : Matrix (Fin n) (Fin n) K) *ᵥ (σ ∘ ψ))) : False := by
  classical
  obtain ⟨w0, hw0, hw0W⟩ := exists_ne_zero_mem_Wsp hN hN0
  have hline : ∀ ψ : Fsp N, ∃ c : K,
      (A : Matrix (Fin n) (Fin n) K) *ᵥ (σ ∘ (ψ : Fin n → K)) = c • w0 := by
    intro ψ
    by_cases hψ0 : (ψ : Fin n → K) = 0
    · exact ⟨0, by simp [hψ0]⟩
    · obtain ⟨c, hc⟩ := hpair w0 ψ (dot_eq_zero_of_mem hw0W ψ.2) hw0W ψ.2 hw0 hψ0
      have hc0 : c ≠ 0 := by
        rintro rfl
        simp at hc
        exact hw0 hc
      refine ⟨c⁻¹, ?_⟩
      rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hA' : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1 :=
    A.inv_mul
  choose g hg using hline
  have hinj : Function.Injective g := by
    intro ψ1 ψ2 h
    have e : (A : Matrix (Fin n) (Fin n) K) *ᵥ (σ ∘ (ψ1 : Fin n → K)) =
        (A : Matrix (Fin n) (Fin n) K) *ᵥ (σ ∘ (ψ2 : Fin n → K)) := by
      rw [hg ψ1, hg ψ2, h]
    have e2 := congrArg (fun v => ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) e
    simp only [mulVec_mulVec, hA', one_mulVec] at e2
    exact Subtype.ext (funext fun i => σ.injective (congrFun e2 i))
  have hcard : Nat.card (Fsp N) ≤ Nat.card K := Nat.card_le_card_of_injective g hinj
  rw [Module.natCard_eq_pow_finrank (K := K) (V := Fsp N)] at hcard
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have h2 := two_le_finrank_Fsp hn hNN
  have h3 : Nat.card K ^ 2 ≤ Nat.card K ^ Module.finrank K (Fsp N) :=
    Nat.pow_le_pow_right (by omega) h2
  nlinarith

theorem conjAut_eq_one_of_scalar (P : GL (Fin n) K) {c : K}
    (hP : (P : Matrix (Fin n) (Fin n) K) = c • (1 : Matrix (Fin n) (Fin n) K)) :
    conjAut n K P = 1 := by
  ext x
  obtain ⟨s, rfl⟩ := proj_surjective n K x
  rw [conjAut_proj]
  have hPP : (P : Matrix (Fin n) (Fin n) K) * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
    P.mul_inv
  have : CatalogueBHigherLinearAction.slConjugation n K P s = s := by
    apply Subtype.ext
    show ((CatalogueBHigherLinearAction.slConjugation n K P s : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (s : Matrix (Fin n) (Fin n) K)
    rw [coe_slConjugation]
    have hc : (P : Matrix (Fin n) (Fin n) K) * (s : Matrix (Fin n) (Fin n) K) =
        (s : Matrix (Fin n) (Fin n) K) * (P : Matrix (Fin n) (Fin n) K) := by
      rw [hP, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
    rw [hc, mul_assoc, hPP, mul_one]
  rw [this]; rfl

theorem uniq_model {p : ℕ} [Fact p.Prime] [CharP K p] [Finite K] (hp2 : p ≠ 2) (hn : 3 ≤ n)
    {N : Matrix (Fin n) (Fin n) K} (hN : IsNilpotent N) (hN0 : N ≠ 0)
    (α : MulAut (projectiveSL n K)) (hcop : (orderOf α).Coprime p)
    (hfixT : ∀ (s : Matrix.SpecialLinearGroup (Fin n) K) (t : K),
      (s : Matrix (Fin n) (Fin n) K) = 1 + t • N → α (proj n K s) = proj n K s)
    (hfixG : ∀ (w ψ : Fin n → K) (h : ψ ⬝ᵥ w = 0), w ∈ Wsp N → ψ ∈ Fsp N →
      α (proj n K (tvSL w ψ h)) = proj n K (tvSL w ψ h)) : α = 1 := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨A, σ, ε, hε, hα⟩ := (automorphism_generation (K := K) hn).2 α
  have hact' : ∀ s, α (proj n K s) = proj n K (autSL A σ ε s) := fun s => by
    rw [hα]; exact aut_apply_proj A σ hε s
  have hfix' : ∀ s : Matrix.SpecialLinearGroup (Fin n) K, α (proj n K s) = proj n K s →
      ∃ ζ : K, (autSL A σ ε s : Matrix (Fin n) (Fin n) K) = ζ • (s : Matrix (Fin n) (Fin n) K) :=
    fun s hs => exists_smul_of_proj_eq (by rw [← hact' s]; exact hs)
  interval_cases ε
  · obtain ⟨hσ, c, hc, hBn⟩ := branch_zero (p := p) hN hN0 A σ
      (fun s t hs => hfix' s (hfixT s t hs))
      (fun w ψ h hw hψ => hfix' _ (hfixG w ψ h hw hψ))
    have hσ1 : σ = 1 := RingEquiv.ext hσ
    have hαA : α = conjAut n K A := by
      rw [hα, hσ1, map_one, mul_one, pow_zero, mul_one]
    obtain ⟨e, he⟩ := add_smul_one_pow_prime_pow (p := p) hBn c
    rw [add_sub_cancel] at he
    have hconj : conjAut n K (A ^ p ^ e) = 1 :=
      conjAut_eq_one_of_scalar (A ^ p ^ e) (c := c ^ p ^ e) (by
        rw [Units.val_pow_eq_pow_val]; exact he)
    have hpow : α ^ p ^ e = 1 := by rw [hαA, ← map_pow, hconj]
    have hdvd : orderOf α ∣ p ^ e := orderOf_dvd_of_pow_eq_one hpow
    have h1 : orderOf α = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right e hcop) hdvd
    exact orderOf_eq_one_iff.1 h1
  · have hNN := branch_one_nn hp2 hN A σ (fun s t hs => hfix' s (hfixT s t hs))
    refine (no_branch_one hn hN hN0 hNN A σ ?_).elim
    intro w ψ h hw hψ hw0 hψ0
    obtain ⟨ζ, hζ⟩ := hfix' _ (hfixG w ψ h hw hψ)
    exact branch_one_pair A σ h hζ hw0 hψ0

theorem exists_nilpotent_of_orderOf_eq [NeZero n] {p : ℕ} [Fact p.Prime] [CharP K p] [Finite K]
    (g : projectiveSL n K) (hg : orderOf g = p) :
    ∃ (N : Matrix (Fin n) (Fin n) K) (hN : IsNilpotent N), N ≠ 0 ∧
      g = proj n K (uniSL (p := p) N hN 1) := by
  obtain ⟨s0, rfl⟩ := proj_surjective n K g
  have hpow : proj n K (s0 ^ p) = 1 := by
    rw [map_pow, ← hg]; exact pow_orderOf_eq_one _
  obtain ⟨c, hcn, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 hpow)
  rw [Matrix.SpecialLinearGroup.coe_pow, scalar_apply, ← smul_one_eq_diagonal] at hc
  obtain ⟨d, hd⟩ : ∃ d : K, d ^ p = (c : K) := by
    have hsurj : Function.Surjective (frobenius K p) :=
      Finite.surjective_of_injective (frobenius_inj K p)
    obtain ⟨d, hd⟩ := hsurj (c : K)
    exact ⟨d, by simpa [frobenius_def] using hd⟩
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_pow (Fact.out : p.Prime).ne_zero] at hd
    exact c.ne_zero hd.symm
  have hdn : d ^ n = 1 := by
    have h1 : (d ^ n - 1) ^ p = 0 := by
      rw [sub_pow_char, ← pow_mul, mul_comm, pow_mul, hd, ← Units.val_pow_eq_pow_val, hcn,
        Units.val_one, one_pow, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.1 h1)
  set N0 : Matrix (Fin n) (Fin n) K := (s0 : Matrix (Fin n) (Fin n) K) - d • 1 with hN0def
  have hN0 : IsNilpotent N0 := by
    refine ⟨p, ?_⟩
    rw [hN0def, sub_pow_char_of_commute p ((Commute.one_right _).smul_right d), hc, ← hd,
      ← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one, map_pow, sub_self]
  set N : Matrix (Fin n) (Fin n) K := d⁻¹ • N0 with hNdef
  have hN : IsNilpotent N := hN0.smul _
  have hmat : (1 : Matrix (Fin n) (Fin n) K) + (1 : K) • N = d⁻¹ • (s0 : Matrix (Fin n) (Fin n) K) := by
    rw [one_smul, hNdef, hN0def, smul_sub, smul_smul, inv_mul_cancel₀ hd0, one_smul]; abel
  have hs0 : s0 = uniSL (p := p) N hN 1 *
      scalarElement (n := n) (Units.mk0 d hd0) (Units.ext (by simpa using hdn)) := by
    apply Subtype.ext
    show (s0 : Matrix (Fin n) (Fin n) K) = ((uniSL (p := p) N hN 1 : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) * scalar (Fin n) d
    rw [coe_uniSL, hmat, scalar_apply, ← smul_one_eq_diagonal, Matrix.smul_mul, Matrix.mul_smul,
      mul_one, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  have hprojeq : proj n K s0 = proj n K (uniSL (p := p) N hN 1) := by
    rw [hs0, map_mul, (proj_eq_one_iff.2 (scalarElement_mem_scalars _ _)), mul_one]
  refine ⟨N, hN, ?_, hprojeq⟩
  intro hN0'
  have h1 : uniSL (p := p) N hN 1 = 1 := by
    apply Subtype.ext
    show (1 : Matrix (Fin n) (Fin n) K) + (1 : K) • N = 1
    rw [hN0', smul_zero, add_zero]
  rw [hprojeq, h1, map_one] at hg
  rw [orderOf_one] at hg
  exact (Fact.out : p.Prime).one_lt.ne hg

@[expose] def modelGen (n : ℕ) (K : Type*) [Field K] (N : Matrix (Fin n) (Fin n) K) :
    Set (projectiveSL n K) :=
  {q | ∃ (w ψ : Fin n → K) (h : ψ ⬝ᵥ w = 0), w ∈ Wsp N ∧ ψ ∈ Fsp N ∧ q = proj n K (tvSL w ψ h)}

@[expose] def modelT (n : ℕ) (K : Type*) [Field K] (N : Matrix (Fin n) (Fin n) K) :
    Set (projectiveSL n K) :=
  {q | ∃ (s : Matrix.SpecialLinearGroup (Fin n) K) (t : K),
    (s : Matrix (Fin n) (Fin n) K) = 1 + t • N ∧ q = proj n K s}

theorem mul_inv_coe (s : Matrix.SpecialLinearGroup (Fin n) K) :
    (s : Matrix (Fin n) (Fin n) K) * ((s⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]; rfl

theorem inv_mul_coe (s : Matrix.SpecialLinearGroup (Fin n) K) :
    ((s⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (s : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl

theorem commute_of_proj_commute [NeZero n] {p : ℕ} [Fact p.Prime] [CharP K p]
    {N : Matrix (Fin n) (Fin n) K} (hN : IsNilpotent N)
    {σ : Matrix.SpecialLinearGroup (Fin n) K}
    (h : proj n K σ * proj n K (uniSL (p := p) N hN 1) =
      proj n K (uniSL (p := p) N hN 1) * proj n K σ) :
    N * (σ : Matrix (Fin n) (Fin n) K) = (σ : Matrix (Fin n) (Fin n) K) * N := by
  rw [← map_mul, ← map_mul] at h
  obtain ⟨c, hc⟩ := exists_smul_of_proj_eq h.symm
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_uniSL] at hc
  set Yi : Matrix (Fin n) (Fin n) K := ((σ⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
    Matrix (Fin n) (Fin n) K) with hYi
  have hσY : (σ : Matrix (Fin n) (Fin n) K) * Yi = 1 := mul_inv_coe σ
  have hYσ : Yi * (σ : Matrix (Fin n) (Fin n) K) = 1 := inv_mul_coe σ
  have key : c • (1 + N) = 1 + Yi * N * (σ : Matrix (Fin n) (Fin n) K) := by
    have h1 : Yi * ((1 + (1 : K) • N) * (σ : Matrix (Fin n) (Fin n) K)) =
        c • (1 + N) := by
      rw [hc, Matrix.mul_smul, ← mul_assoc, hYσ, one_mul, one_smul]
    rw [← h1, one_smul, mul_assoc, add_mul, one_mul, mul_add, hYσ, ← mul_assoc]
  have hnil : IsNilpotent (Yi * N * (σ : Matrix (Fin n) (Fin n) K)) :=
    isNilpotent_conj hYσ hσY hN
  have hc1 : c = 1 := eq_one_of_smul_one_add_nilpotent hN hnil key
  rw [hc1, one_smul, one_smul] at hc
  simp only [add_mul, mul_add, one_mul, mul_one] at hc
  exact add_left_cancel hc

theorem Nz_eq_zero {N : Matrix (Fin n) (Fin n) K} {w ψ : Fin n → K} (hw : w ∈ Wsp N) :
    N * vecMulVec w ψ = 0 := by
  rw [mul_vecMulVec, (mem_Wsp.1 hw).1]
  ext i j; simp [vecMulVec_apply]

theorem zN_eq_zero {N : Matrix (Fin n) (Fin n) K} {w ψ : Fin n → K} (hψ : ψ ∈ Fsp N) :
    vecMulVec w ψ * N = 0 := by
  rw [vecMulVec_mul, mem_Fsp.1 hψ]
  ext i j; simp [vecMulVec_apply]

theorem uniSL_commute_modelT [NeZero n] {p : ℕ} [Fact p.Prime] [CharP K p]
    {N : Matrix (Fin n) (Fin n) K} (hN : IsNilpotent N)
    {s : Matrix.SpecialLinearGroup (Fin n) K} {t : K}
    (hs : (s : Matrix (Fin n) (Fin n) K) = 1 + t • N) :
    uniSL (p := p) N hN 1 * s = s * uniSL (p := p) N hN 1 := by
  apply Subtype.ext
  show ((uniSL (p := p) N hN 1 * s : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
    ((s * uniSL (p := p) N hN 1 : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hs, coe_uniSL]
  simp only [mul_add, add_mul, mul_one, one_mul, smul_mul_assoc, mul_smul_comm]
  module

theorem uniSL_commute_tvSL [NeZero n] {p : ℕ} [Fact p.Prime] [CharP K p]
    {N : Matrix (Fin n) (Fin n) K} (hN : IsNilpotent N) {w ψ : Fin n → K} (h : ψ ⬝ᵥ w = 0)
    (hw : w ∈ Wsp N) (hψ : ψ ∈ Fsp N) :
    uniSL (p := p) N hN 1 * tvSL w ψ h = tvSL w ψ h * uniSL (p := p) N hN 1 := by
  apply Subtype.ext
  show ((uniSL (p := p) N hN 1 * tvSL w ψ h : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) =
    ((tvSL w ψ h * uniSL (p := p) N hN 1 : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_tvSL, coe_uniSL]
  simp only [mul_add, add_mul, mul_one, one_mul, one_smul, Nz_eq_zero hw, zN_eq_zero hψ]
  abel

theorem one_add_pow_eq_of_mul_self_eq_zero {y : Matrix (Fin n) (Fin n) K} (hy : y * y = 0)
    (k : ℕ) : (1 + y) ^ k = 1 + k • y := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    simp only [mul_add, add_mul, mul_one, one_mul, smul_mul_assoc, hy, smul_zero, add_zero,
      succ_nsmul]
    abel

theorem inv_mul_comm_of_comm {S Yi N : Matrix (Fin n) (Fin n) K} (hSY : S * Yi = 1)
    (hYS : Yi * S = 1) (hc : N * S = S * N) : Yi * N = N * Yi := by
  calc Yi * N = Yi * N * (S * Yi) := by rw [hSY, mul_one]
    _ = Yi * (N * S) * Yi := by simp only [mul_assoc]
    _ = Yi * (S * N) * Yi := by rw [hc]
    _ = (Yi * S) * N * Yi := by simp only [mul_assoc]
    _ = N * Yi := by rw [hYS, one_mul]

section Framework

variable [NeZero n] {p : ℕ} [Fact p.Prime] [CharP K p] {N : Matrix (Fin n) (Fin n) K}
  (hN : IsNilpotent N)

theorem model_h1 (q : projectiveSL n K) (hq : q ∈ modelGen n K N ∪ modelT n K N) :
    proj n K (uniSL (p := p) N hN 1) * q = q * proj n K (uniSL (p := p) N hN 1) := by
  rcases hq with ⟨w, ψ, h, hw, hψ, rfl⟩ | ⟨s, t, hs, rfl⟩
  · rw [← map_mul, ← map_mul, uniSL_commute_tvSL hN h hw hψ]
  · rw [← map_mul, ← map_mul, uniSL_commute_modelT hN hs]

theorem model_hT (s q : projectiveSL n K)
    (hs : s * proj n K (uniSL (p := p) N hN 1) = proj n K (uniSL (p := p) N hN 1) * s)
    (hq : q ∈ modelT n K N) : s * q = q * s := by
  obtain ⟨s', t, hs', rfl⟩ := hq
  obtain ⟨σ, rfl⟩ := proj_surjective n K s
  have hc := commute_of_proj_commute hN hs
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  show ((σ * s' : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
    ((s' * σ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hs', mul_add, add_mul,
    mul_one, one_mul, mul_smul_comm, smul_mul_assoc, hc.symm]

theorem model_hGen (s q : projectiveSL n K)
    (hs : s * proj n K (uniSL (p := p) N hN 1) = proj n K (uniSL (p := p) N hN 1) * s)
    (hq : q ∈ modelGen n K N) : s * q * s⁻¹ ∈ modelGen n K N := by
  obtain ⟨w, ψ, h, hw, hψ, rfl⟩ := hq
  obtain ⟨σ, rfl⟩ := proj_surjective n K s
  have hc := commute_of_proj_commute hN hs
  set Yi : Matrix (Fin n) (Fin n) K := ((σ⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
    Matrix (Fin n) (Fin n) K) with hYi
  have hσY : (σ : Matrix (Fin n) (Fin n) K) * Yi = 1 := mul_inv_coe σ
  have hYσ : Yi * (σ : Matrix (Fin n) (Fin n) K) = 1 := inv_mul_coe σ
  have hYN : Yi * N = N * Yi := inv_mul_comm_of_comm hσY hYσ hc
  have hw' : (σ : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ Wsp N := by
    rw [mem_Wsp]
    obtain ⟨h0, v0, hv0⟩ := mem_Wsp.1 hw
    refine ⟨?_, (σ : Matrix (Fin n) (Fin n) K) *ᵥ v0, ?_⟩
    · rw [mulVec_mulVec, hc, ← mulVec_mulVec, h0, mulVec_zero]
    · rw [mulVec_mulVec, hc, ← mulVec_mulVec, hv0]
  have hψ' : ψ ᵥ* Yi ∈ Fsp N := by
    rw [mem_Fsp, vecMul_vecMul, hYN, ← vecMul_vecMul, mem_Fsp.1 hψ, zero_vecMul]
  have h' : (ψ ᵥ* Yi) ⬝ᵥ ((σ : Matrix (Fin n) (Fin n) K) *ᵥ w) = 0 := dot_eq_zero_of_mem hw' hψ'
  refine ⟨_, _, h', hw', hψ', ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  show ((σ * tvSL w ψ h * σ⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
    ((tvSL _ _ h' : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_tvSL, coe_tvSL]
  rw [← hYi, mul_add, mul_one, add_mul, hσY, mul_vecMulVec, vecMulVec_mul]

theorem model_hp3 [Finite K] (q : projectiveSL n K) (hq : q ∈ modelGen n K N)
    (q' : projectiveSL n K) (hq' : q' ∈ modelGen n K N) : (q' * q⁻¹) ^ p = 1 := by
  obtain ⟨w, ψ, h, hw, hψ, rfl⟩ := hq
  obtain ⟨w', ψ', h', hw', hψ', rfl⟩ := hq'
  rw [← map_inv, ← map_mul, ← map_pow]
  have hzz : vecMulVec w ψ * vecMulVec w ψ = 0 := vv_mul_vv_of_dot _ _ _ _ h
  have hz'z' : vecMulVec w' ψ' * vecMulVec w' ψ' = 0 := vv_mul_vv_of_dot _ _ _ _ h'
  have hz'z : vecMulVec w' ψ' * vecMulVec w ψ = 0 :=
    vv_mul_vv_of_dot _ _ _ _ (dot_eq_zero_of_mem hw hψ')
  have hzz' : vecMulVec w ψ * vecMulVec w' ψ' = 0 :=
    vv_mul_vv_of_dot _ _ _ _ (dot_eq_zero_of_mem hw' hψ)
  have hinv : ((tvSL w ψ h)⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) =
      (1 - vecMulVec w ψ : Matrix (Fin n) (Fin n) K) := by
    apply coe_inv_of_mul_eq_one
    rw [coe_tvSL]
    calc (1 + vecMulVec w ψ) * (1 - vecMulVec w ψ) = 1 - vecMulVec w ψ * vecMulVec w ψ := by
          noncomm_ring
      _ = 1 := by rw [hzz, sub_zero]
  have hmat : ((tvSL w' ψ' h' * (tvSL w ψ h)⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 + (vecMulVec w' ψ' - vecMulVec w ψ) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, hinv, coe_tvSL]
    calc (1 + vecMulVec w' ψ') * (1 - vecMulVec w ψ)
        = 1 + (vecMulVec w' ψ' - vecMulVec w ψ) - vecMulVec w' ψ' * vecMulVec w ψ := by
          noncomm_ring
      _ = _ := by rw [hz'z, sub_zero]
  have hy : (vecMulVec w' ψ' - vecMulVec w ψ) * (vecMulVec w' ψ' - vecMulVec w ψ) = 0 := by
    rw [sub_mul, mul_sub, mul_sub, hz'z', hz'z, hzz', hzz]; simp
  have : (tvSL w' ψ' h' * (tvSL w ψ h)⁻¹) ^ p = 1 := by
    apply Subtype.ext
    show (((tvSL w' ψ' h' * (tvSL w ψ h)⁻¹) ^ p : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1
    rw [Matrix.SpecialLinearGroup.coe_pow, hmat, one_add_pow_eq_of_mul_self_eq_zero hy,
      ← Nat.cast_smul_eq_nsmul K p, CharP.cast_eq_zero, zero_smul, add_zero]
  rw [this, map_one]

include hN in
theorem model_huniq [Finite K] (hp2 : p ≠ 2) (hn : 3 ≤ n) (hN0 : N ≠ 0)
    (α : MulAut (projectiveSL n K)) (hcop : (orderOf α).Coprime p)
    (hfix : ∀ q ∈ modelGen n K N ∪ modelT n K N, α q = q) : α = 1 :=
  uniq_model hp2 hn hN hN0 α hcop
    (fun s t hs => hfix _ (Or.inr ⟨s, t, hs, rfl⟩))
    (fun w ψ h hw hψ => hfix _ (Or.inl ⟨w, ψ, h, hw, hψ, rfl⟩))

end Framework

theorem center_eq_bot_of_simple {S : Type*} [Group S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  rcases (Subgroup.center S).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have : a ∈ Subgroup.center S := by rw [h]; trivial
    exact hab ((Subgroup.mem_center_iff.1 this b).symm)

section Abstract

variable {G : Type*} [Group G] [Finite G]

theorem conj_injective_of_center_eq_bot (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  have : a ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := congrArg (fun f : MulAut G => f y) (MonoidHom.mem_ker.1 ha)
    simp [MulAut.conj_apply] at this
    exact (by simpa [mul_inv_eq_iff_eq_mul] using this : a * y = y * a).symm
  rw [hZ] at this
  exact this

theorem mul_conj_mul_inv_eq (α : MulAut G) (q : G) :
    α * MulAut.conj q * α⁻¹ = MulAut.conj (α q) := by
  ext y
  simp [MulAut.conj_apply]

theorem conj_mem_gLAPPrimeCoreOf {M : Type*} [Group M] {p : ℕ} {X : Subgroup M} {a c : M}
    (ha : a ∈ GLAPPrimeCoreOf p X) (hc : c ∈ X) : c * a * c⁻¹ ∈ GLAPPrimeCoreOf p X := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 ha
  refine Subgroup.mem_map.2 ⟨(⟨c, hc⟩ : ↥X) * y * (⟨c, hc⟩ : ↥X)⁻¹,
    (GLAPPrimeCore.normal p ↥X).conj_mem y hy _, ?_⟩
  simp

theorem gLAPPrimeCoreOf_eq_bot_of_framework (hZ : Subgroup.center G = ⊥) {p : ℕ} (hp : p.Prime)
    (g : G) (Gen T : Set G)
    (h1 : ∀ q ∈ Gen ∪ T, g * q = q * g)
    (hT : ∀ s q, s * g = g * s → q ∈ T → s * q = q * s)
    (hGen : ∀ s q, s * g = g * s → q ∈ Gen → s * q * s⁻¹ ∈ Gen)
    (hp3 : ∀ q ∈ Gen, ∀ q' ∈ Gen, (q' * q⁻¹) ^ p = 1)
    (huniq : ∀ α : MulAut G, (orderOf α).Coprime p → (∀ q ∈ Gen ∪ T, α q = q) → α = 1)
    (H : Subgroup (MulAut G)) (hH : innerAut G ≤ H) (x : MulAut G) (hx : x = MulAut.conj g) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut G))) = ⊥ := by
  have hinj := conj_injective_of_center_eq_bot hZ
  set X := H ⊓ Subgroup.centralizer ({x} : Set (MulAut G)) with hX
  have hmemX : ∀ q ∈ Gen ∪ T, (MulAut.conj q : MulAut G) ∈ X := by
    intro q hq
    refine ⟨hH ⟨q, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [hx, ← map_mul, ← map_mul, h1 q hq]
  have hcop : ∀ d ∈ GLAPPrimeCoreOf p X, (orderOf d).Coprime p := fun d hd =>
    CFSG.HardMathSupport.Timmesfeld.Proving.orderOf_coprime_of_mem_GLAPPrimeCoreOf hp hd
  have stageA : ∀ s : G, (MulAut.conj s : MulAut G) ∈ GLAPPrimeCoreOf p X →
      (MulAut.conj s : MulAut G) = 1 := by
    intro s hs
    have hsX : (MulAut.conj s : MulAut G) ∈ X := by
      obtain ⟨y, -, hy⟩ := Subgroup.mem_map.1 hs
      rw [← hy]; exact y.2
    have hsg : s * g = g * s := by
      have h := (Subgroup.mem_centralizer_singleton_iff.1 hsX.2)
      rw [hx, ← map_mul, ← map_mul] at h
      exact hinj h
    have hfix : ∀ q ∈ Gen, s * q = q * s := by
      intro q hq
      have hq' : s * q * s⁻¹ ∈ Gen := hGen s q hsg hq
      have hcq := hmemX q (Or.inl hq)
      have h2 : (MulAut.conj q : MulAut G) * (MulAut.conj s)⁻¹ * (MulAut.conj q)⁻¹ ∈
          GLAPPrimeCoreOf p X := by
        have := conj_mem_gLAPPrimeCoreOf (inv_mem hs) hcq
        simpa [mul_assoc] using this
      have h3 := mul_mem hs h2
      have he : (MulAut.conj s : MulAut G) * ((MulAut.conj q : MulAut G) *
          (MulAut.conj s)⁻¹ * (MulAut.conj q)⁻¹) = MulAut.conj ((s * q * s⁻¹) * q⁻¹) := by
        simp only [map_mul, map_inv, mul_assoc]
      rw [he] at h3
      have hord := hcop _ h3
      have hpow : ((MulAut.conj ((s * q * s⁻¹) * q⁻¹) : MulAut G)) ^ p = 1 := by
        rw [← map_pow, hp3 q hq _ hq', map_one]
      have hdvd : orderOf (MulAut.conj ((s * q * s⁻¹) * q⁻¹) : MulAut G) ∣ p :=
        orderOf_dvd_of_pow_eq_one hpow
      have h1' : orderOf (MulAut.conj ((s * q * s⁻¹) * q⁻¹) : MulAut G) = 1 :=
        Nat.Coprime.eq_one_of_dvd hord hdvd
      have h4 : (MulAut.conj ((s * q * s⁻¹) * q⁻¹) : MulAut G) = 1 := orderOf_eq_one_iff.1 h1'
      have h5 : (s * q * s⁻¹) * q⁻¹ = 1 := hinj (by rw [h4, map_one])
      have h6 : s * q * s⁻¹ = q := by simpa [mul_inv_eq_one] using h5
      rw [mul_inv_eq_iff_eq_mul] at h6
      exact h6
    refine huniq _ (hcop _ hs) ?_
    rintro q (hq | hq)
    · simp [MulAut.conj_apply, hfix q hq]
    · simp [MulAut.conj_apply, hT s q hsg hq]
  rw [eq_bot_iff]
  intro α hα
  rw [Subgroup.mem_bot]
  refine huniq α (hcop α hα) ?_
  intro q hq
  have hcq := hmemX q hq
  have h2 : (MulAut.conj q : MulAut G) * α⁻¹ * (MulAut.conj q)⁻¹ ∈ GLAPPrimeCoreOf p X := by
    have := conj_mem_gLAPPrimeCoreOf (inv_mem hα) hcq
    simpa [mul_assoc] using this
  have h3 := mul_mem hα h2
  have he : α * ((MulAut.conj q : MulAut G) * α⁻¹ * (MulAut.conj q)⁻¹) =
      MulAut.conj (α q * q⁻¹) := by
    have := mul_conj_mul_inv_eq α q
    rw [map_mul, map_inv, ← this]
    group
  rw [he] at h3
  have h4 := stageA _ h3
  have h5 : α q * q⁻¹ = 1 := hinj (by rw [h4, map_one])
  simpa [mul_inv_eq_one] using h5

end Abstract

theorem defCharInnerCoreFreeFamA_of_two_le :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      ∀ idx : TauCeti.ValidLieTypeIndex, (∃ r q, idx.1 = .A r q ∧ 2 ≤ r) →
        Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
        ∀ p : ℕ, p.Prime → p ≠ 2 → idx.1.characteristic = p →
          ∀ x ∈ CFSG.HardMathSupport.Solomon.LocalBalance.innerAut S, orderOf x = p →
            ∀ H : Subgroup (MulAut S), CFSG.HardMathSupport.Solomon.LocalBalance.innerAut S ≤ H →
              CFSG.Open.GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) = ⊥ := by
  intro S _ _ hS hnab idx hidx hSL p hp hp2 hch x hx hxo H hH
  obtain ⟨r, q, hr, hr2⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e0⟩ := hSL
  have hpq : p = q.p := by simpa using hch.symm
  subst hpq
  let e : S ≃* LinearFlag.projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
    e0.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _))
  have hZ : Subgroup.center S = ⊥ := center_eq_bot_of_simple hS hnab
  obtain ⟨g, rfl⟩ := hx
  have hord : orderOf g = q.p := by
    rw [← orderOf_injective (MulAut.conj : S →* MulAut S) (conj_injective_of_center_eq_bot hZ) g]
    exact hxo
  have hord0 : orderOf (e g) = q.p := by rw [MulEquiv.orderOf_eq e g]; exact hord
  have hn : 3 ≤ r + 1 := by omega
  have : NeZero (r + 1) := ⟨by omega⟩
  obtain ⟨N, hN, hN0, hg0⟩ := exists_nilpotent_of_orderOf_eq (p := q.p) (e g) hord0
  refine gLAPPrimeCoreOf_eq_bot_of_framework hZ hp g
    {q' | e q' ∈ modelGen (r + 1) (GaloisField q.p q.exponent) N}
    {q' | e q' ∈ modelT (r + 1) (GaloisField q.p q.exponent) N} ?_ ?_ ?_ ?_ ?_ H hH _ rfl
  · intro q' hq'
    apply e.injective
    rw [map_mul, map_mul, hg0]
    exact model_h1 hN (e q') hq'
  · intro s q' hs hq'
    apply e.injective
    rw [map_mul, map_mul]
    refine model_hT hN (e s) (e q') ?_ hq'
    rw [← hg0, ← map_mul, ← map_mul, hs]
  · intro s q' hs hq'
    have hs' : e s * proj (r + 1) (GaloisField q.p q.exponent) (uniSL (p := q.p) N hN 1) =
        proj (r + 1) (GaloisField q.p q.exponent) (uniSL (p := q.p) N hN 1) * e s := by
      rw [← hg0, ← map_mul, ← map_mul, hs]
    have := model_hGen hN (e s) (e q') hs' hq'
    show e (s * q' * s⁻¹) ∈ modelGen (r + 1) (GaloisField q.p q.exponent) N
    rw [map_mul, map_mul, map_inv]
    exact this
  · intro q' hq' q'' hq''
    apply e.injective
    rw [map_pow, map_mul, map_inv, map_one]
    exact model_hp3 (p := q.p) (e q') hq' (e q'') hq''
  · intro α hα hfix
    have hcop : (orderOf (MulAut.congr e α)).Coprime q.p := by
      rw [MulEquiv.orderOf_eq (MulAut.congr e) α]; exact hα
    have h1 : MulAut.congr e α = 1 := by
      refine model_huniq hN hp2 hn hN0 _ hcop ?_
      intro q0 hq0
      have hmem : e.symm q0 ∈ {q' | e q' ∈ modelGen (r + 1) (GaloisField q.p q.exponent) N} ∪
          {q' | e q' ∈ modelT (r + 1) (GaloisField q.p q.exponent) N} := by
        rcases hq0 with h | h
        · exact Or.inl (by simpa using h)
        · exact Or.inr (by simpa using h)
      have := hfix _ hmem
      change e (α (e.symm q0)) = q0
      rw [this]; simp
    exact (MulAut.congr e).injective (by rw [h1, map_one])

end CFSG.HardMathSupport.Timmesfeld.DefChar
