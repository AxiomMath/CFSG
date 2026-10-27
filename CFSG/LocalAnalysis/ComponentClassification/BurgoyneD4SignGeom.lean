module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOPairNorm
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalStabilizerRigidityGeometry
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4Fam

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.D4

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction (Points)
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)

variable {K : Type} [Field K]

theorem polar_oQ {d : ℕ} {R : GL (Fin d) K} (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R)
    (x y : Fin d → K) :
    QuadraticMap.polar (oQ R) x y = 2 * (x ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ y) := by
  rw [QuadraticMap.polar, oQ_apply, oQ_apply, oQ_apply, mulVec_add, dotProduct_add,
    add_dotProduct, add_dotProduct, dot_symm hR x y]
  ring

theorem false_of_perp (hK : ringChar K ≠ 2) {R : GL (Fin (2 * 4)) K}
    (hR : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)ᵀ = R) {W : Submodule K (Fin (2 * 4) → K)}
    (hW : IsTS (oQ R) 4 W) {u : Fin (2 * 4) → K} (hu : oQ R u ≠ 0)
    (hperp : ∀ v ∈ W, v ⬝ᵥ (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ u = 0) : False := by
  have hnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hK R hR
  have hdim : Module.finrank K (Fin (2 * 4) → K) = 2 * Module.finrank K W := by
    rw [hW.1, Module.finrank_fin_fun]
  have heq := CatalogueBOrthogonalStabilizerRigidity.totally_singular_eq_orthogonal hnd hW.2 hdim
  have huW : u ∈ W := by
    rw [heq]
    refine LinearMap.BilinForm.mem_orthogonal_iff.2 fun v hv => ?_
    change QuadraticMap.polar (oQ R) v u = 0
    rw [polar_oQ hR, hperp v hv, mul_zero]
  exact hu (hW.2 u huW)

variable {d : ℕ}

@[expose] def restr (M : Finset (Fin d)) (v : Fin d → K) : Fin d → K :=
  fun i => if i ∈ M then v i else 0

theorem signMat_mulVec (M : Finset (Fin d)) (v : Fin d → K) :
    signMat K M *ᵥ v = v - (2 : K) • restr M v := by
  funext i
  rw [signMat, mulVec_diagonal]
  simp only [restr, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem restr_mem (h2 : (2 : K) ≠ 0) {M : Finset (Fin d)} {W : Submodule K (Fin d → K)}
    (hW : ∀ v ∈ W, signMat K M *ᵥ v ∈ W) {v : Fin d → K} (hv : v ∈ W) : restr M v ∈ W := by
  have h := W.sub_mem hv (hW v hv)
  rw [signMat_mulVec, sub_sub_cancel] at h
  have := W.smul_mem (2 : K)⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ h2, one_smul] at this

theorem restr_restr (M M' : Finset (Fin d)) (v : Fin d → K) :
    restr M' (restr M v) = restr (M ∩ M') v := by
  funext i
  simp only [restr, Finset.mem_inter]
  by_cases h : i ∈ M <;> by_cases h' : i ∈ M' <;> simp [h, h']

theorem oQ_diag {w : Fin d → K} (hw : ∀ i, w i ≠ 0) (v : Fin d → K) :
    oQ (diagGL hw) v = ∑ i, w i * v i ^ 2 := by
  rw [oQ_apply, coe_diagGL, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by rw [mulVec_diagonal]; ring

theorem oQ_diag_restr {w : Fin d → K} (hw : ∀ i, w i ≠ 0) (M : Finset (Fin d)) (v : Fin d → K) :
    oQ (diagGL hw) (restr M v) = ∑ i ∈ M, w i * v i ^ 2 := by
  rw [oQ_diag, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ M)]
  have h1 : ∑ i ∈ Finset.univ.filter (· ∈ M), w i * restr M v i ^ 2 = ∑ i ∈ M, w i * v i ^ 2 := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact Finset.sum_congr rfl fun i hi => by simp [restr, hi]
  have h2 : ∑ i ∈ Finset.univ.filter (· ∉ M), w i * restr M v i ^ 2 = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [Finset.mem_filter] at hi
      simp [restr, hi.2]
  rw [h1, h2, add_zero]

theorem dot_diag_single {w : Fin d → K} (hw : ∀ i, w i ≠ 0) (u : Fin d → K) (a : Fin d) :
    u ⬝ᵥ ((diagGL hw : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ Pi.single a 1 =
      u a * w a := by
  rw [coe_diagGL, dotProduct, Finset.sum_eq_single a]
  · rw [mulVec_diagonal]
    simp
  · intro b _ hb
    rw [mulVec_diagonal]
    simp [hb]
  · simp

theorem false_of_coord_zero (hK : ringChar K ≠ 2) {w : Fin (2 * 4) → K} (hw : ∀ i, w i ≠ 0)
    {W : Submodule K (Fin (2 * 4) → K)} (hW : IsTS (oQ (diagGL hw)) 4 W) {a : Fin (2 * 4)}
    (ha : ∀ v ∈ W, v a = 0) : False := by
  refine false_of_perp hK (diagGL_transpose hw) hW (u := Pi.single a 1) ?_ fun v hv => ?_
  · rw [oQ_diag, Finset.sum_eq_single a]
    · simpa using hw a
    · intro b _ hb
      simp [hb]
    · simp
  · rw [dot_diag_single, ha v hv, zero_mul]

theorem not_klein_invariant (hK : ringChar K ≠ 2) {w : Fin (2 * 4) → K} (hw : ∀ i, w i ≠ 0)
    {W : Submodule K (Fin (2 * 4) → K)} (hW : IsTS (oQ (diagGL hw)) 4 W) {a b c : Fin (2 * 4)}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h₁ : ∀ v ∈ W, signMat K {a, b} *ᵥ v ∈ W) (h₂ : ∀ v ∈ W, signMat K {b, c} *ᵥ v ∈ W) :
    False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  refine false_of_coord_zero hK hw hW (a := b) fun v hv => ?_
  have hm := restr_mem h2 h₂ (restr_mem h2 h₁ hv)
  rw [restr_restr] at hm
  have hint : ({a, b} : Finset (Fin (2 * 4))) ∩ {b, c} = {b} := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h | h, h' | h'⟩
      · exact absurd (h.symm.trans h') hab
      · exact absurd (h.symm.trans h') hac
      · exact h
      · exact h
    · rintro rfl
      exact ⟨Or.inr rfl, Or.inl rfl⟩
  rw [hint] at hm
  have hq := hW.2 _ hm
  rw [oQ_diag_restr, Finset.sum_singleton] at hq
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ((mul_eq_zero.1 hq).resolve_left (hw b))

theorem not_aniso_invariant (hK : ringChar K ≠ 2) {w : Fin (2 * 4) → K} (hw : ∀ i, w i ≠ 0)
    {W : Submodule K (Fin (2 * 4) → K)} (hW : IsTS (oQ (diagGL hw)) 4 W) {a b : Fin (2 * 4)}
    (hab : a ≠ b) (haniso : ∀ x y : K, w a * x ^ 2 + w b * y ^ 2 = 0 → x = 0)
    (h₁ : ∀ v ∈ W, signMat K {a, b} *ᵥ v ∈ W) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  refine false_of_coord_zero hK hw hW (a := a) fun v hv => ?_
  have hq := hW.2 _ (restr_mem h2 h₁ hv)
  rw [oQ_diag_restr, Finset.sum_insert (by simpa using hab), Finset.sum_singleton] at hq
  exact haniso _ _ hq

theorem exists_singular_on [Finite K] (hK : ringChar K ≠ 2) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {x y z : Fin d} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ v : Fin d → K, v ≠ 0 ∧ (∀ i, i ≠ x → i ≠ y → i ≠ z → v i = 0) ∧ oQ (diagGL hw) v = 0 := by
  have hc : -(w y / w x) ≠ 0 := neg_ne_zero.2 (div_ne_zero (hw y) (hw x))
  obtain ⟨α, β, hαβ⟩ := exists_sq_sub_mul_sq hK hc (-(w z / w x))
  set v : Fin d → K := Pi.single x α + Pi.single y β + Pi.single z 1 with hv
  have hvx : v x = α := by simp [hv, hxy, hxz]
  have hvy : v y = β := by simp [hv, hxy.symm, hyz]
  have hvz : v z = 1 := by simp [hv, hxz.symm, hyz.symm]
  have hsupp : ∀ i, i ≠ x → i ≠ y → i ≠ z → v i = 0 := by
    intro i hix hiy hiz
    simp [hv, hix, hiy, hiz]
  refine ⟨v, fun h0 => by simp [h0] at hvz, hsupp, ?_⟩
  have hr : restr {x, y, z} v = v := by
    funext i
    by_cases hi : i ∈ ({x, y, z} : Finset (Fin d))
    · simp [restr, hi]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      simp [restr, hi.1, hi.2.1, hi.2.2, hsupp i hi.1 hi.2.1 hi.2.2]
  rw [← hr, oQ_diag_restr, Finset.sum_insert (by simp [hxy, hxz]),
    Finset.sum_insert (by simp [hyz]), Finset.sum_singleton, hvx, hvy, hvz]
  have hx := hw x
  field_simp at hαβ
  linear_combination hαβ

theorem signMat_mulVec_of_disjoint {M : Finset (Fin d)} {v : Fin d → K}
    (hv : ∀ i ∈ M, v i = 0) : signMat K M *ᵥ v = v := by
  funext i
  rw [signMat, mulVec_diagonal]
  by_cases hi : i ∈ M
  · simp [hi, hv i hi]
  · simp [hi]

end CFSG.ComponentClassification.Burgoyne.D4
