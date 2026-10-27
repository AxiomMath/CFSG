module

public import Mathlib.LinearAlgebra.Projectivization.Action
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.LinearGroups

open Matrix
open scoped LinearAlgebra.Projectivization MatrixGroups

variable {K : Type*} [Field K]

@[expose] def pairDet (v w : Fin 2 → K) : K := v 0 * w 1 - v 1 * w 0

theorem exists_smul_eq_of_pairDet_eq_zero {v w : Fin 2 → K} (hv : v ≠ 0)
    (h : pairDet v w = 0) : ∃ c : K, w = c • v := by
  unfold pairDet at h
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨w 1 / v 1, ?_⟩
    have hw0 : w 0 = 0 := by
      rw [h0, zero_mul, zero_sub, neg_eq_zero] at h
      exact (mul_eq_zero.mp h).resolve_left h1
    funext i
    fin_cases i <;> simp [h0, hw0, h1]
  · refine ⟨w 0 / v 0, ?_⟩
    funext i
    fin_cases i
    · simp [h0]
    · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination h

theorem eq_zero_of_mulVec_eq_zero {M : Matrix (Fin 2) (Fin 2) K} {v w : Fin 2 → K}
    (hdet : pairDet v w ≠ 0) (hv : M *ᵥ v = 0) (hw : M *ᵥ w = 0) : M = 0 := by
  unfold pairDet at hdet
  have hv0 := congrFun hv 0
  have hv1 := congrFun hv 1
  have hw0 := congrFun hw 0
  have hw1 := congrFun hw 1
  simp only [mulVec, dotProduct, Fin.sum_univ_two, Pi.zero_apply] at hv0 hv1 hw0 hw1
  have k00 : M 0 0 * (v 0 * w 1 - v 1 * w 0) = 0 := by linear_combination w 1 * hv0 - v 1 * hw0
  have k01 : M 0 1 * (v 0 * w 1 - v 1 * w 0) = 0 := by linear_combination v 0 * hw0 - w 0 * hv0
  have k10 : M 1 0 * (v 0 * w 1 - v 1 * w 0) = 0 := by linear_combination w 1 * hv1 - v 1 * hw1
  have k11 : M 1 1 * (v 0 * w 1 - v 1 * w 0) = 0 := by linear_combination v 0 * hw1 - w 0 * hv1
  ext i j
  fin_cases i <;> fin_cases j
  · exact (mul_eq_zero.mp k00).resolve_right hdet
  · exact (mul_eq_zero.mp k01).resolve_right hdet
  · exact (mul_eq_zero.mp k10).resolve_right hdet
  · exact (mul_eq_zero.mp k11).resolve_right hdet

theorem exists_smul_eq_of_mulVec_eq_zero {M : Matrix (Fin 2) (Fin 2) K} (hM : M ≠ 0)
    {v w : Fin 2 → K} (hv0 : v ≠ 0) (hv : M *ᵥ v = 0) (hw : M *ᵥ w = 0) :
    ∃ c : K, w = c • v := by
  by_cases h : pairDet v w = 0
  · exact exists_smul_eq_of_pairDet_eq_zero hv0 h
  · exact (hM (eq_zero_of_mulVec_eq_zero h hv hw)).elim

theorem eq_of_mulVec_eq {A B : Matrix (Fin 2) (Fin 2) K} {v w : Fin 2 → K}
    (hdet : pairDet v w ≠ 0) (hv : A *ᵥ v = B *ᵥ v) (hw : A *ᵥ w = B *ᵥ w) : A = B := by
  rw [← sub_eq_zero]
  exact eq_zero_of_mulVec_eq_zero hdet (by rw [sub_mulVec, hv, sub_self])
    (by rw [sub_mulVec, hw, sub_self])

theorem mk_ne_mk_iff_pairDet_ne_zero {v w : Fin 2 → K} (hv : v ≠ 0) (hw : w ≠ 0) :
    Projectivization.mk K v hv ≠ Projectivization.mk K w hw ↔ pairDet v w ≠ 0 := by
  rw [not_iff_not, Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨a, rfl⟩
    simp only [pairDet, Pi.smul_apply, smul_eq_mul]
    ring
  · intro h
    have h' : pairDet w v = 0 := by
      unfold pairDet at h ⊢
      linear_combination -h
    obtain ⟨c, hc⟩ := exists_smul_eq_of_pairDet_eq_zero hw h'
    exact ⟨c, hc.symm⟩

theorem mk_smul_mk_eq_iff (g : GL (Fin 2) K) {v : Fin 2 → K} (hv : v ≠ 0) :
    (ProjGenLinGroup.mk g : PGL(Fin 2, K)) • Projectivization.mk K v hv =
        Projectivization.mk K v hv ↔ ∃ c : K, (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v = c • v := by
  rw [Projectivization.PGL.mk_smul_mk, Projectivization.mk_eq_mk_iff']
  exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

theorem pow_mulVec_eq_of_mulVec_eq {T : Matrix (Fin 2) (Fin 2) K} {v : Fin 2 → K} {a : K}
    (h : T *ᵥ v = a • v) (m : ℕ) : (T ^ m) *ᵥ v = a ^ m • v := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ← mulVec_mulVec, h, mulVec_smul, ih, smul_smul, pow_succ']

theorem det_sub_smul_one (T : Matrix (Fin 2) (Fin 2) K) (a : K) :
    (T - a • (1 : Matrix (Fin 2) (Fin 2) K)).det = a ^ 2 - T.trace * a + T.det := by
  simp only [det_fin_two, trace_fin_two, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  simp
  ring

theorem exists_det_sub_smul_one_eq_zero [IsAlgClosed K] (T : Matrix (Fin 2) (Fin 2) K) :
    ∃ a : K, (T - a • (1 : Matrix (Fin 2) (Fin 2) K)).det = 0 := by
  have hdeg : (Polynomial.X ^ 2 - Polynomial.C T.trace * Polynomial.X +
      Polynomial.C T.det).degree = 2 := by compute_degree!
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root _ (by rw [hdeg]; exact two_ne_zero)
  refine ⟨a, ?_⟩
  rw [det_sub_smul_one]
  simpa [Polynomial.IsRoot] using ha

theorem sub_smul_one_mul_sub_smul_one_eq_zero (T : Matrix (Fin 2) (Fin 2) K) (a : K)
    (ha : (T - a • (1 : Matrix (Fin 2) (Fin 2) K)).det = 0) :
    (T - a • (1 : Matrix (Fin 2) (Fin 2) K)) * (T - (T.trace - a) • 1) = 0 := by
  rw [det_sub_smul_one] at ha
  rw [det_fin_two, trace_fin_two] at ha
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, trace_fin_two, one_apply] <;>
    first
    | ring1
    | linear_combination -ha

theorem smul_one_add_pow_succ {N : Matrix (Fin 2) (Fin 2) K} (hN : N * N = 0) (a : K) (m : ℕ) :
    (a • (1 : Matrix (Fin 2) (Fin 2) K) + N) ^ (m + 1) =
      a ^ (m + 1) • (1 : Matrix (Fin 2) (Fin 2) K) + ((m + 1 : K) * a ^ m) • N := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hN, smul_zero,
      add_zero]
    rw [show a ^ (m + 1 + 1) = a ^ (m + 1) * a by ring]
    push_cast
    module

theorem det_sub_trace_sub_smul_one (T : Matrix (Fin 2) (Fin 2) K) (a : K) :
    (T - (T.trace - a) • (1 : Matrix (Fin 2) (Fin 2) K)).det =
      (T - a • (1 : Matrix (Fin 2) (Fin 2) K)).det := by
  rw [det_sub_smul_one, det_sub_smul_one]
  ring

theorem exists_mulVec_eq_zero_of_det_eq_zero {M : Matrix (Fin 2) (Fin 2) K} (h : M.det = 0) :
    ∃ v : Fin 2 → K, v ≠ 0 ∧ M *ᵥ v = 0 := by
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  exact ⟨v, hv, hMv⟩

theorem sub_smul_one_mulVec_eq_zero_iff {T : Matrix (Fin 2) (Fin 2) K} {a : K}
    {v : Fin 2 → K} : (T - a • (1 : Matrix (Fin 2) (Fin 2) K)) *ᵥ v = 0 ↔ T *ᵥ v = a • v := by
  rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero]

theorem sub_smul_one_mulVec_of_eigen {T : Matrix (Fin 2) (Fin 2) K} {μ : K} {v : Fin 2 → K}
    (h : T *ᵥ v = μ • v) (a : K) :
    (T - a • (1 : Matrix (Fin 2) (Fin 2) K)) *ᵥ v = (μ - a) • v := by
  rw [sub_mulVec, smul_mulVec, one_mulVec, h, sub_smul]

theorem eq_one_of_pow_char_pow_eq_one {p : ℕ} [Fact p.Prime] [CharP K p] {x : K} {k : ℕ}
    (h : x ^ p ^ k = 1) : x = 1 := by
  have : (x - 1) ^ p ^ k = 0 := by rw [sub_pow_char_pow, h, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero k (Fact.out : p.Prime).ne_zero) |>.mp this)

theorem exists_smul_eq_of_eigen {T : Matrix (Fin 2) (Fin 2) K} {a : K}
    (hT : T ≠ a • (1 : Matrix (Fin 2) (Fin 2) K)) {v u : Fin 2 → K} (hv0 : v ≠ 0)
    (hv : T *ᵥ v = a • v) (hu : T *ᵥ u = a • u) : ∃ c : K, u = c • v :=
  exists_smul_eq_of_mulVec_eq_zero (sub_ne_zero.mpr hT) hv0
    (sub_smul_one_mulVec_eq_zero_iff.mpr hv) (sub_smul_one_mulVec_eq_zero_iff.mpr hu)

theorem exists_eigen_pair_of_pow_eq_one [IsAlgClosed K] {T : Matrix (Fin 2) (Fin 2) K} {r : ℕ}
    (hr : (r : K) ≠ 0) (hpow : T ^ r = 1) (hT : ∀ c : K, T ≠ c • 1) :
    ∃ v w : Fin 2 → K, v ≠ 0 ∧ w ≠ 0 ∧ pairDet v w ≠ 0 ∧ ∀ u : Fin 2 → K, u ≠ 0 →
      ((∃ c : K, T *ᵥ u = c • u) ↔ (∃ c : K, u = c • v) ∨ (∃ c : K, u = c • w)) := by
  obtain ⟨a, ha⟩ := exists_det_sub_smul_one_eq_zero T
  have hfac := sub_smul_one_mul_sub_smul_one_eq_zero T a ha
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_of_det_eq_zero ha
  rw [sub_smul_one_mulVec_eq_zero_iff] at hv
  have hab : a ≠ T.trace - a := by
    intro hab
    rw [← hab] at hfac
    set N := T - a • (1 : Matrix (Fin 2) (Fin 2) K) with hN
    have hTN : T = a • 1 + N := by rw [hN]; abel
    have hN0 : N ≠ 0 := sub_ne_zero.mpr (hT a)
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by
      have : r ≠ 0 := by rintro rfl; exact hr Nat.cast_zero
      omega⟩
    have hexp := smul_one_add_pow_succ hfac a m
    rw [← hTN, hpow] at hexp
    have hNv : N *ᵥ v = 0 := by rw [hN]; exact sub_smul_one_mulVec_eq_zero_iff.mpr hv
    have hv' := congrArg (· *ᵥ v) hexp
    simp only [one_mulVec, add_mulVec, smul_mulVec, hNv, smul_zero, add_zero] at hv'
    have ham : a ^ (m + 1) = 1 := by
      by_contra hne
      apply hv0
      have : (1 - a ^ (m + 1)) • v = 0 := by rw [sub_smul, one_smul, ← hv', sub_self]
      exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hne))
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_pow (Nat.succ_ne_zero m)] at ham
      exact zero_ne_one ham
    apply hN0
    have hzero : ((m + 1 : K) * a ^ m) • N = 0 := by
      have := hexp
      rw [ham, one_smul] at this
      exact (add_eq_left.mp this.symm)
    refine (smul_eq_zero.mp hzero).resolve_left (mul_ne_zero ?_ (pow_ne_zero m ha0))
    exact_mod_cast hr
  obtain ⟨w, hw0, hw⟩ := exists_mulVec_eq_zero_of_det_eq_zero
    ((det_sub_trace_sub_smul_one T a).trans ha)
  rw [sub_smul_one_mulVec_eq_zero_iff] at hw
  have hdet : pairDet v w ≠ 0 := by
    intro hdet
    obtain ⟨c, rfl⟩ := exists_smul_eq_of_pairDet_eq_zero hv0 hdet
    rw [mulVec_smul, hv, smul_smul, smul_smul, mul_comm] at hw
    have hc : c ≠ 0 := by
      rintro rfl
      exact hw0 (zero_smul K v)
    have := smul_left_injective K hv0 hw
    exact hab (mul_left_cancel₀ hc (by simpa [mul_comm] using this))
  refine ⟨v, w, hv0, hw0, hdet, fun u hu0 => ⟨?_, ?_⟩⟩
  · rintro ⟨μ, hμ⟩
    have hprod := congrArg (· *ᵥ u) hfac
    simp only [zero_mulVec] at hprod
    rw [← mulVec_mulVec, sub_smul_one_mulVec_of_eigen hμ, mulVec_smul,
      sub_smul_one_mulVec_of_eigen hμ, smul_smul] at hprod
    rcases mul_eq_zero.mp ((smul_eq_zero.mp hprod).resolve_right hu0) with h1 | h1
    · rw [sub_eq_zero] at h1
      rw [h1] at hμ
      exact Or.inr (exists_smul_eq_of_eigen (hT _) hw0 hw hμ)
    · rw [sub_eq_zero] at h1
      rw [h1] at hμ
      exact Or.inl (exists_smul_eq_of_eigen (hT a) hv0 hv hμ)
  · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨a, by rw [mulVec_smul, hv, smul_comm]⟩
    · exact ⟨T.trace - a, by rw [mulVec_smul, hw, smul_comm]⟩

theorem exists_unique_eigenline_of_pow_char_pow_eq_one [IsAlgClosed K] {p : ℕ} [Fact p.Prime]
    [CharP K p] {T : Matrix (Fin 2) (Fin 2) K} {k : ℕ} (hpow : T ^ p ^ k = 1) (hT : T ≠ 1) :
    T ^ p = 1 ∧ ∃ v : Fin 2 → K, v ≠ 0 ∧ ∀ u : Fin 2 → K, u ≠ 0 →
      ((∃ c : K, T *ᵥ u = c • u) ↔ ∃ c : K, u = c • v) := by
  have heig : ∀ {μ : K} {u : Fin 2 → K}, u ≠ 0 → T *ᵥ u = μ • u → μ = 1 := by
    intro μ u hu0 hu
    have h := pow_mulVec_eq_of_mulVec_eq hu (p ^ k)
    rw [hpow, one_mulVec] at h
    have h1 : (μ ^ p ^ k - 1) • u = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
    exact eq_one_of_pow_char_pow_eq_one (sub_eq_zero.mp
      ((smul_eq_zero.mp h1).resolve_right hu0))
  obtain ⟨a, ha⟩ := exists_det_sub_smul_one_eq_zero T
  have hfac := sub_smul_one_mul_sub_smul_one_eq_zero T a ha
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_of_det_eq_zero ha
  rw [sub_smul_one_mulVec_eq_zero_iff] at hv
  obtain ⟨w, hw0, hw⟩ := exists_mulVec_eq_zero_of_det_eq_zero
    ((det_sub_trace_sub_smul_one T a).trans ha)
  rw [sub_smul_one_mulVec_eq_zero_iff] at hw
  have ha1 := heig hv0 hv
  have hb1 := heig hw0 hw
  rw [hb1, ha1] at hfac
  rw [ha1, one_smul] at hv
  set N := T - (1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) with hN
  have hTN : T = (1 : K) • 1 + N := by rw [hN]; abel
  have hN0 : N ≠ 0 := by
    rw [hN, one_smul]
    exact sub_ne_zero.mpr hT
  refine ⟨?_, v, hv0, fun u hu0 => ⟨?_, ?_⟩⟩
  · obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos
      (Fact.out : p.Prime).pos).symm⟩
    have hp0 : ((m + 1 : ℕ) : K) = 0 := by
      rw [← hm]
      exact CharP.cast_eq_zero K p
    rw [hTN, hm, smul_one_add_pow_succ hfac]
    push_cast at hp0
    simp [hp0]
  · rintro ⟨μ, hμ⟩
    rw [heig hu0 hμ] at hμ
    refine exists_smul_eq_of_mulVec_eq_zero hN0 hv0 ?_ ?_
    · rw [hN, one_smul, sub_mulVec, one_mulVec, hv, sub_self]
    · rw [hN, one_smul, sub_mulVec, one_mulVec, hμ, one_smul, sub_self]
  · rintro ⟨c, rfl⟩
    exact ⟨1, by rw [mulVec_smul, hv, one_smul]⟩

theorem mk_eq_one_iff_exists_scalar {g : GL (Fin 2) K} :
    ProjGenLinGroup.mk g = 1 ↔ ∃ u : Kˣ, g = GeneralLinearGroup.scalar (Fin 2) u := by
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨fun ⟨u, hu⟩ => ⟨u, hu.symm⟩, fun ⟨u, hu⟩ => ⟨u, hu.symm⟩⟩

theorem ne_smul_one_of_mk_ne_one {g : GL (Fin 2) K} (hg : ProjGenLinGroup.mk g ≠ 1) (c : K) :
    (g : Matrix (Fin 2) (Fin 2) K) ≠ c • 1 := by
  intro hc
  apply hg
  have hc0 : c ≠ 0 := by
    rintro rfl
    have := g.isUnit.ne_zero
    rw [hc, zero_smul] at this
    exact this rfl
  refine mk_eq_one_iff_exists_scalar.mpr ⟨Units.mk0 c hc0, Units.ext ?_⟩
  rw [hc]
  simp [GeneralLinearGroup.scalar, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]

theorem exists_mk_eq_and_pow_eq_one [IsAlgClosed K] {h : PGL(Fin 2, K)} {n : ℕ} (hn : 0 < n)
    (hh : h ^ n = 1) : ∃ T : GL (Fin 2) K, ProjGenLinGroup.mk T = h ∧ T ^ n = 1 := by
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective h
  rw [← map_pow, mk_eq_one_iff_exists_scalar] at hh
  obtain ⟨u, hu⟩ := hh
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (u : K) hn
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hd
    exact u.ne_zero hd.symm
  set e : Kˣ := Units.mk0 d hd0
  have he : e ^ n = u := Units.ext (by simp [e, hd])
  have hcomm : Commute g (GeneralLinearGroup.scalar (Fin 2) e⁻¹) := by
    have hmem : GeneralLinearGroup.scalar (Fin 2) e⁻¹ ∈ Subgroup.center (GL (Fin 2) K) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨e⁻¹, rfl⟩
    exact (Subgroup.mem_center_iff.mp hmem) g
  refine ⟨g * GeneralLinearGroup.scalar (Fin 2) e⁻¹, ?_, ?_⟩
  · rw [map_mul, ProjGenLinGroup.mk_scalar, mul_one]
  · rw [hcomm.mul_pow, hu, ← map_pow, ← map_mul, inv_pow, he, mul_inv_cancel, map_one]

theorem mk_eq_mk_iff_exists_smul {u v : Fin 2 → K} (hu : u ≠ 0) (hv : v ≠ 0) :
    Projectivization.mk K u hu = Projectivization.mk K v hv ↔ ∃ c : K, u = c • v := by
  rw [Projectivization.mk_eq_mk_iff']
  exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

theorem projective_coprime_prime_fixed_points [IsAlgClosed K] {p r : ℕ} (hp : p.Prime)
    (hr : r.Prime) (hpr : p ≠ r) [CharP K p] {h : PGL(Fin 2, K)} (hh : orderOf h = r) :
    ∃ x y : ℙ K (Fin 2 → K), x ≠ y ∧ ∀ z : ℙ K (Fin 2 → K), h • z = z ↔ z = x ∨ z = y := by
  have hne : h ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hh
    exact hr.one_lt.ne hh
  obtain ⟨T, rfl, hT⟩ := exists_mk_eq_and_pow_eq_one hr.pos (hh ▸ pow_orderOf_eq_one h)
  have hrK : (r : K) ≠ 0 := by
    rw [ne_eq, CharP.cast_eq_zero_iff K p]
    exact fun hdvd => hpr ((Nat.prime_dvd_prime_iff_eq hp hr).mp hdvd)
  have hTr : (T : Matrix (Fin 2) (Fin 2) K) ^ r = 1 := by
    rw [← Units.val_pow_eq_pow_val, hT, Units.val_one]
  obtain ⟨v, w, hv0, hw0, hdet, hfix⟩ :=
    exists_eigen_pair_of_pow_eq_one hrK hTr (ne_smul_one_of_mk_ne_one hne)
  refine ⟨Projectivization.mk K v hv0, Projectivization.mk K w hw0,
    (mk_ne_mk_iff_pairDet_ne_zero hv0 hw0).mpr hdet, fun z => ?_⟩
  induction z using Projectivization.ind with
  | h u hu =>
    rw [mk_smul_mk_eq_iff, mk_eq_mk_iff_exists_smul, mk_eq_mk_iff_exists_smul]
    exact hfix u hu

theorem projective_p_element_fixed_point [IsAlgClosed K] {p : ℕ} (hp : p.Prime) [CharP K p]
    {h : PGL(Fin 2, K)} (hne : h ≠ 1) {k : ℕ} (hk : h ^ p ^ k = 1) :
    orderOf h = p ∧ ∃! x : ℙ K (Fin 2 → K), h • x = x := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T, rfl, hT⟩ := exists_mk_eq_and_pow_eq_one (pow_pos hp.pos k) hk
  have hTk : (T : Matrix (Fin 2) (Fin 2) K) ^ p ^ k = 1 := by
    rw [← Units.val_pow_eq_pow_val, hT, Units.val_one]
  have hT1 : (T : Matrix (Fin 2) (Fin 2) K) ≠ 1 := by
    simpa using ne_smul_one_of_mk_ne_one hne 1
  obtain ⟨hTp, v, hv0, hfix⟩ := exists_unique_eigenline_of_pow_char_pow_eq_one hTk hT1
  refine ⟨orderOf_eq_prime ?_ hne, Projectivization.mk K v hv0, ?_, fun z hz => ?_⟩
  · rw [← map_pow]
    have : T ^ p = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hTp, Units.val_one])
    rw [this, map_one]
  · exact (mk_smul_mk_eq_iff T hv0).mpr ((hfix v hv0).mpr ⟨1, (one_smul K v).symm⟩)
  · induction z using Projectivization.ind with
    | h u hu =>
      rw [mk_smul_mk_eq_iff] at hz
      exact (mk_eq_mk_iff_exists_smul hu hv0).mpr ((hfix u hu).mp hz)

theorem coe_scalar_mulVec (u : Kˣ) (x : Fin 2 → K) :
    (GeneralLinearGroup.scalar (Fin 2) u : Matrix (Fin 2) (Fin 2) K) *ᵥ x = (u : K) • x := by
  ext i
  fin_cases i <;> simp [GeneralLinearGroup.scalar, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

section TwoPoint

variable {v w : Fin 2 → K}

@[expose] def diagIn (v w : Fin 2 → K) (a b : K) : Matrix (Fin 2) (Fin 2) K :=
  (pairDet v w)⁻¹ • !![a * v 0 * w 1 - b * w 0 * v 1, b * w 0 * v 0 - a * v 0 * w 0;
    a * v 1 * w 1 - b * w 1 * v 1, b * w 1 * v 0 - a * v 1 * w 0]

theorem diagIn_mulVec_left (hdet : pairDet v w ≠ 0) (a b : K) :
    diagIn v w a b *ᵥ v = a • v := by
  unfold diagIn
  unfold pairDet at hdet ⊢
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.smul_apply] <;>
    field_simp <;> ring

theorem diagIn_mulVec_right (hdet : pairDet v w ≠ 0) (a b : K) :
    diagIn v w a b *ᵥ w = b • w := by
  unfold diagIn
  unfold pairDet at hdet ⊢
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.smul_apply] <;>
    field_simp <;> ring

theorem eq_diagIn (hdet : pairDet v w ≠ 0) {A : Matrix (Fin 2) (Fin 2) K} {a b : K}
    (hv : A *ᵥ v = a • v) (hw : A *ᵥ w = b • w) : A = diagIn v w a b :=
  eq_of_mulVec_eq hdet (by rw [hv, diagIn_mulVec_left hdet]) (by rw [hw, diagIn_mulVec_right hdet])

theorem diagIn_mul (hdet : pairDet v w ≠ 0) (a b c d : K) :
    diagIn v w a b * diagIn v w c d = diagIn v w (a * c) (b * d) := by
  refine eq_diagIn hdet ?_ ?_
  · rw [← mulVec_mulVec, diagIn_mulVec_left hdet, mulVec_smul, diagIn_mulVec_left hdet, smul_smul,
      mul_comm]
  · rw [← mulVec_mulVec, diagIn_mulVec_right hdet, mulVec_smul, diagIn_mulVec_right hdet,
      smul_smul, mul_comm]

theorem diagIn_one (hdet : pairDet v w ≠ 0) : diagIn v w 1 1 = 1 :=
  (eq_diagIn hdet (by rw [one_mulVec, one_smul]) (by rw [one_mulVec, one_smul])).symm

@[expose] def diagInUnit (hdet : pairDet v w ≠ 0) (a b : Kˣ) : GL (Fin 2) K :=
  ⟨diagIn v w a b, diagIn v w (a⁻¹ : Kˣ) (b⁻¹ : Kˣ),
    by rw [diagIn_mul hdet, Units.mul_inv, Units.mul_inv, diagIn_one hdet],
    by rw [diagIn_mul hdet, Units.inv_mul, Units.inv_mul, diagIn_one hdet]⟩

theorem coe_diagInUnit (hdet : pairDet v w ≠ 0) (a b : Kˣ) :
    (diagInUnit hdet a b : Matrix (Fin 2) (Fin 2) K) = diagIn v w a b :=
  rfl

@[expose] def diagInHom (hdet : pairDet v w ≠ 0) : Kˣ →* PGL(Fin 2, K) where
  toFun c := ProjGenLinGroup.mk (diagInUnit hdet c 1)
  map_one' := by
    rw [← ProjGenLinGroup.mk_one]
    congr 1
    exact Units.ext (by rw [coe_diagInUnit, Units.val_one, diagIn_one hdet, Units.val_one])
  map_mul' c d := by
    rw [← map_mul]
    congr 1
    exact Units.ext (by
      rw [Units.val_mul, coe_diagInUnit, coe_diagInUnit, coe_diagInUnit, diagIn_mul hdet,
        Units.val_mul, Units.val_one, mul_one])

theorem mk_eq_diagInHom (hdet : pairDet v w ≠ 0) {g : GL (Fin 2) K} {a b : Kˣ}
    (hv : (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v = (a : K) • v)
    (hw : (g : Matrix (Fin 2) (Fin 2) K) *ᵥ w = (b : K) • w) :
    ProjGenLinGroup.mk g = diagInHom hdet (a / b) := by
  have hg : g = GeneralLinearGroup.scalar (Fin 2) b * diagInUnit hdet (a / b) 1 := by
    refine Units.ext (eq_of_mulVec_eq hdet ?_ ?_)
    · rw [hv, Units.val_mul, ← mulVec_mulVec, coe_diagInUnit, diagIn_mulVec_left hdet,
        coe_scalar_mulVec, smul_smul, Units.val_div_eq_div_val, mul_div_cancel₀ _ b.ne_zero]
    · rw [hw, Units.val_mul, ← mulVec_mulVec, coe_diagInUnit, diagIn_mulVec_right hdet,
        coe_scalar_mulVec, Units.val_one, smul_smul, mul_one]
  rw [hg, map_mul, ProjGenLinGroup.mk_scalar, one_mul]
  rfl

end TwoPoint

section TwoPointStabilizer

variable {v w : Fin 2 → K}

theorem diagInHom_mem (hdet : pairDet v w ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) (c : Kˣ) :
    diagInHom hdet c ∈ fixingSubgroup PGL(Fin 2, K)
      ({Projectivization.mk K v hv, Projectivization.mk K w hw} : Set (ℙ K (Fin 2 → K))) := by
  rw [mem_fixingSubgroup_iff]
  rintro x (rfl | rfl)
  · exact (mk_smul_mk_eq_iff _ hv).mpr ⟨c, by rw [coe_diagInUnit, diagIn_mulVec_left hdet]⟩
  · exact (mk_smul_mk_eq_iff _ hw).mpr
      ⟨1, by rw [coe_diagInUnit, diagIn_mulVec_right hdet, Units.val_one]⟩

theorem diagInHom_injective (hdet : pairDet v w ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    Function.Injective (diagInHom (K := K) hdet) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  obtain ⟨u, hu⟩ := mk_eq_one_iff_exists_scalar.mp hc
  have hmat := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) hu
  simp only [coe_diagInUnit] at hmat
  have hw' := congrArg (· *ᵥ w) hmat
  have hv' := congrArg (· *ᵥ v) hmat
  simp only [diagIn_mulVec_right hdet, diagIn_mulVec_left hdet, coe_scalar_mulVec,
    Units.val_one, one_smul] at hw' hv'
  have hu1 : (u : K) = 1 := by
    have : ((u : K) - 1) • w = 0 := by rw [sub_smul, one_smul, ← hw', sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hw)
  apply Units.ext
  have : ((c : K) - u) • v = 0 := by rw [sub_smul, hv', sub_self]
  rw [Units.val_one, ← hu1]
  exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hv)

theorem projective_two_point_stabilizer (hv : v ≠ 0) (hw : w ≠ 0)
    (hvw : Projectivization.mk K v hv ≠ Projectivization.mk K w hw) :
    ∃ φ : fixingSubgroup PGL(Fin 2, K)
        ({Projectivization.mk K v hv, Projectivization.mk K w hw} : Set (ℙ K (Fin 2 → K))) ≃* Kˣ,
      (∀ x ∈ fixingSubgroup PGL(Fin 2, K)
          ({Projectivization.mk K v hv, Projectivization.mk K w hw} : Set (ℙ K (Fin 2 → K))),
        ∃ (g : GL (Fin 2) K) (a b : Kˣ), ProjGenLinGroup.mk g = x ∧
          (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v = (a : K) • v ∧
          (g : Matrix (Fin 2) (Fin 2) K) *ᵥ w = (b : K) • w) ∧
      ∀ (g : GL (Fin 2) K) (a b : Kˣ), (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v = (a : K) • v →
        (g : Matrix (Fin 2) (Fin 2) K) *ᵥ w = (b : K) • w →
        ∃ hg : ProjGenLinGroup.mk g ∈ fixingSubgroup PGL(Fin 2, K)
          ({Projectivization.mk K v hv, Projectivization.mk K w hw} : Set (ℙ K (Fin 2 → K))),
          φ ⟨_, hg⟩ = a / b := by
  have hdet := (mk_ne_mk_iff_pairDet_ne_zero hv hw).mp hvw
  set D := fixingSubgroup PGL(Fin 2, K)
    ({Projectivization.mk K v hv, Projectivization.mk K w hw} : Set (ℙ K (Fin 2 → K)))
  have hdiag : ∀ x ∈ D, ∃ (g : GL (Fin 2) K) (a b : Kˣ), ProjGenLinGroup.mk g = x ∧
      (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v = (a : K) • v ∧
      (g : Matrix (Fin 2) (Fin 2) K) *ᵥ w = (b : K) • w := by
    intro x hx
    obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective x
    rw [mem_fixingSubgroup_iff] at hx
    obtain ⟨a, ha⟩ := (mk_smul_mk_eq_iff g hv).mp (hx _ (Set.mem_insert _ _))
    obtain ⟨b, hb⟩ := (mk_smul_mk_eq_iff g hw).mp (hx _ (Set.mem_insert_of_mem _ rfl))
    have hne : ∀ {c : K} {u : Fin 2 → K}, u ≠ 0 → (g : Matrix (Fin 2) (Fin 2) K) *ᵥ u = c • u →
        c ≠ 0 := by
      rintro c u hu hc rfl
      rw [zero_smul] at hc
      exact hu ((smul_eq_zero_iff_eq g).mp hc)
    exact ⟨g, Units.mk0 a (hne hv ha), Units.mk0 b (hne hw hb), rfl, ha, hb⟩
  let ψ : Kˣ →* D := (diagInHom hdet).codRestrict D (diagInHom_mem hdet hv hw)
  have hψ : Function.Bijective ψ := by
    refine ⟨fun c d h => diagInHom_injective hdet hv hw (congrArg Subtype.val h), ?_⟩
    rintro ⟨x, hx⟩
    obtain ⟨g, a, b, rfl, ha, hb⟩ := hdiag x hx
    exact ⟨a / b, Subtype.ext (mk_eq_diagInHom hdet ha hb).symm⟩
  refine ⟨(MulEquiv.ofBijective ψ hψ).symm, hdiag, fun g a b ha hb => ?_⟩
  have hmem : ProjGenLinGroup.mk g ∈ D := by
    rw [mk_eq_diagInHom hdet ha hb]
    exact diagInHom_mem hdet hv hw _
  refine ⟨hmem, ?_⟩
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext (mk_eq_diagInHom hdet ha hb)

end TwoPointStabilizer

theorem projective_p_element_two_set_trivial {p : ℕ} (hp : p.Prime) (hodd : Odd p) [CharP K p]
    {h : PGL(Fin 2, K)} {k : ℕ} (hk : h ^ p ^ k = 1) {x y : ℙ K (Fin 2 → K)} (hxy : x ≠ y)
    (hpres : ∀ z ∈ ({x, y} : Set (ℙ K (Fin 2 → K))), h • z ∈ ({x, y} : Set (ℙ K (Fin 2 → K)))) :
    h = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hpx : h • x = x ∨ h • x = y := hpres x (Set.mem_insert _ _)
  have hpy : h • y = x ∨ h • y = y := hpres y (Set.mem_insert_of_mem _ rfl)
  have hx : h • x = x := by
    rcases hpx with hx | hx
    · exact hx
    · exfalso
      have hy : h • y = x := by
        rcases hpy with hy | hy
        · exact hy
        · exact absurd (smul_left_cancel h (hx.trans hy.symm)) hxy
      have h2 : h ^ 2 ∈ MulAction.stabilizer PGL(Fin 2, K) x := by
        rw [MulAction.mem_stabilizer_iff, pow_two, mul_smul, hx, hy]
      obtain ⟨m, hm⟩ := hodd.pow (n := k)
      have hxy' : (h ^ p ^ k) • x = y := by
        rw [hm, pow_succ', pow_mul, mul_smul,
          MulAction.mem_stabilizer_iff.mp (pow_mem h2 m), hx]
      rw [hk, one_smul] at hxy'
      exact hxy hxy'
  have hy : h • y = y := by
    rcases hpy with hy | hy
    · exact absurd (smul_left_cancel h (hx.trans hy.symm)) hxy
    · exact hy
  induction x using Projectivization.ind with
  | h v hv =>
  induction y using Projectivization.ind with
  | h w hw =>
  obtain ⟨φ, -, -⟩ := projective_two_point_stabilizer hv hw hxy
  have hmem : h ∈ fixingSubgroup PGL(Fin 2, K)
      ({Projectivization.mk K v hv, Projectivization.mk K w hw} : Set (ℙ K (Fin 2 → K))) := by
    rw [mem_fixingSubgroup_iff]
    rintro z (rfl | rfl)
    · exact hx
    · exact hy
  have hφ : φ ⟨h, hmem⟩ = 1 := by
    apply Units.ext
    rw [Units.val_one]
    apply eq_one_of_pow_char_pow_eq_one (p := p) (k := k)
    rw [← Units.val_pow_eq_pow_val, ← map_pow]
    have : (⟨h, hmem⟩ : fixingSubgroup PGL(Fin 2, K) _) ^ p ^ k = 1 :=
      Subtype.ext (by simpa using hk)
    rw [this, map_one, Units.val_one]
  have := φ.injective (hφ.trans φ.map_one.symm)
  exact congrArg Subtype.val this

theorem projective_elementary_abelian_coprime_rank [IsAlgClosed K] {p r : ℕ} (hp : p.Prime)
    (hr : r.Prime) (hpr : p ≠ r) [CharP K p] (R : Subgroup PGL(Fin 2, K)) [Finite R]
    [Nontrivial R] [IsElementaryAbelian r R] :
    Nat.card R = r ∨ (r = 2 ∧ Nat.card R = 4) := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨⟨h, hhR⟩, hne⟩ := exists_ne (1 : R)
  have hne' : h ≠ 1 := fun h1 => hne (Subtype.ext h1)
  have hpow : h ^ r = 1 := elemPow_eq_one_of_isElementaryAbelian h hhR
  obtain ⟨x, y, hxy, hfix⟩ :=
    projective_coprime_prime_fixed_points hp hr hpr (orderOf_eq_prime hpow hne')
  have hcomm : ∀ g ∈ R, g * h = h * g := by
    intro g hg
    have := (IsMulCommutative.is_comm (M := R)).comm ⟨g, hg⟩ ⟨h, hhR⟩
    exact congrArg Subtype.val this
  have hpres : ∀ g : R, ∀ z, (z = x ∨ z = y) → ((g : PGL(Fin 2, K)) • z = x ∨
      (g : PGL(Fin 2, K)) • z = y) := by
    intro g z hz
    rw [← hfix] at hz ⊢
    rw [smul_smul, ← hcomm g g.2, mul_smul, hz]
  set R₀ := MulAction.stabilizer R x with hR₀
  have hR₀y : ∀ g ∈ R₀, (g : PGL(Fin 2, K)) • y = y := by
    intro g hg
    have hgx : (g : PGL(Fin 2, K)) • x = x := MulAction.mem_stabilizer_iff.mp hg
    rcases hpres g y (Or.inr rfl) with hgy | hgy
    · exact absurd (smul_left_cancel (g : PGL(Fin 2, K)) (hgy.trans hgx.symm)) hxy.symm
    · exact hgy
  have hle : Nat.card R₀ ≤ r := by
    induction x using Projectivization.ind with
    | h v hv =>
    induction y using Projectivization.ind with
    | h w hw =>
    obtain ⟨φ, -, -⟩ := projective_two_point_stabilizer hv hw hxy
    have hmem : ∀ g : R₀, ((g : R) : PGL(Fin 2, K)) ∈ fixingSubgroup PGL(Fin 2, K)
        ({Projectivization.mk K v hv, Projectivization.mk K w hw} : Set (ℙ K (Fin 2 → K))) := by
      intro g
      rw [mem_fixingSubgroup_iff]
      rintro z (rfl | rfl)
      · exact MulAction.mem_stabilizer_iff.mp g.2
      · exact hR₀y g g.2
    let ι : R₀ → rootsOfUnity r K := fun g => ⟨φ ⟨((g : R) : PGL(Fin 2, K)), hmem g⟩, by
      rw [mem_rootsOfUnity, ← map_pow]
      have : (⟨((g : R) : PGL(Fin 2, K)), hmem g⟩ : fixingSubgroup PGL(Fin 2, K) _) ^ r = 1 :=
        Subtype.ext (by simpa using elemPow_eq_one_of_isElementaryAbelian _ (g : R).2)
      rw [this, map_one]⟩
    have hι : Function.Injective ι := by
      intro g g' hgg'
      have h1 := congrArg Subtype.val hgg'
      have h3 := Subtype.mk.inj (φ.injective h1)
      exact Subtype.ext (Subtype.ext h3)
    have : NeZero r := ⟨hr.ne_zero⟩
    calc Nat.card R₀ ≤ Nat.card (rootsOfUnity r K) := Nat.card_le_card_of_injective ι hι
      _ ≤ r := card_rootsOfUnity K r
  have hge : r ≤ Nat.card R₀ := by
    have hzp : Subgroup.zpowers (⟨h, hhR⟩ : R) ≤ R₀ := by
      rw [Subgroup.zpowers_le, hR₀, MulAction.mem_stabilizer_iff]
      exact (hfix x).mpr (Or.inl rfl)
    calc r = orderOf (⟨h, hhR⟩ : R) := by
          rw [← orderOf_injective R.subtype R.subtype_injective ⟨h, hhR⟩]
          exact (orderOf_eq_prime hpow hne').symm
      _ = Nat.card (Subgroup.zpowers (⟨h, hhR⟩ : R)) := (Nat.card_zpowers _).symm
      _ ≤ Nat.card R₀ := Subgroup.card_le_of_le hzp
  have hR₀card : Nat.card R₀ = r := le_antisymm hle hge
  have hidx : R₀.index ≤ 2 := by
    rw [hR₀, MulAction.index_stabilizer]
    calc (MulAction.orbit R x).ncard ≤ ({x, y} : Set (ℙ K (Fin 2 → K))).ncard := by
          apply Set.ncard_le_ncard _ (Set.toFinite _)
          rintro _ ⟨g, rfl⟩
          rcases hpres g x (Or.inl rfl) with h1 | h1
          · exact Or.inl h1
          · exact Or.inr h1
      _ = 2 := Set.ncard_pair hxy
  have hidx0 : 1 ≤ R₀.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hcardR := Subgroup.index_mul_card R₀
  rw [hR₀card] at hcardR
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup r R).exists_card_eq
  interval_cases hi : R₀.index
  · left
    rw [← hcardR, one_mul]
  · right
    have h2 : 2 ∣ r ^ n := ⟨r, by rw [← hn, ← hcardR]⟩
    have hr2 : r = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp
      (Nat.prime_two.dvd_of_dvd_pow h2)).symm
    exact ⟨hr2, by rw [← hcardR, hr2]⟩

end CFSG.LinearGroups
