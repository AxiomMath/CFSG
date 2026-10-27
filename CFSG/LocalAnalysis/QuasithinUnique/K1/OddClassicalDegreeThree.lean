module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.OddClassicalFusion
public import CFSG.Open.StatedDefs
public import CFSG.Open.StatedAPI
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import Certificates.Certificate113

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open Matrix

section Projective

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem statedProj_mk_eq_iff (Hg : Subgroup (GL ι K)) (x y : Hg) :
    (QuotientGroup.mk x : StatedProj Hg) = QuotientGroup.mk y ↔
      ∃ u : Kˣ, ((y : GL ι K) : Matrix ι ι K) =
        ((x : GL ι K) : Matrix ι ι K) * ((u : K) • (1 : Matrix ι ι K)) :=
  CFSG.Open.StatedAPI.statedProj_mk_eq_iff Hg x y

end Projective

section Deg3

variable {K : Type} [Field K]

theorem deg3_scalar_eq_one (A Z : Matrix (Fin 3) (Fin 3) K) (hAA : A * A = 1) (hdA : A.det = 1)
    (hdZ : Z.det = 1) (u : K)
    (h : A * Z = (Z * A) * (u • (1 : Matrix (Fin 3) (Fin 3) K))) : u = 1 := by
  have h3 : u ^ 3 = 1 := by
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_smul_of_tower] at this
    simpa [hdA, hdZ] using this.symm
  have hZ : Z = (u ^ 2) • Z := by
    calc Z = A * (A * Z) := by rw [← mul_assoc, hAA, one_mul]
      _ = A * ((Z * A) * (u • (1 : Matrix (Fin 3) (Fin 3) K))) := by rw [h]
      _ = u • ((A * Z) * A) := by
        rw [Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul, ← mul_assoc]
      _ = u • (((Z * A) * (u • (1 : Matrix (Fin 3) (Fin 3) K))) * A) := by rw [h]
      _ = (u ^ 2) • Z := by
        rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_assoc, hAA,
          Matrix.mul_one, smul_smul, sq]
  have h2 : u ^ 2 = 1 := by
    by_contra hne
    have h0 : (1 - u ^ 2) • Z = 0 := by rw [sub_smul, one_smul]; exact sub_eq_zero.mpr hZ
    have hZ0 : Z = 0 := by
      rcases smul_eq_zero.mp h0 with h' | h'
      · exact absurd (sub_eq_zero.mp h').symm hne
      · exact h'
    rw [hZ0] at hdZ
    simp at hdZ
  calc u = u * u ^ 2 := by rw [h2, mul_one]
    _ = u ^ 3 := by ring
    _ = 1 := h3

theorem deg3_centralizer_core (h2 : (2 : K) ≠ 0) (Zm : Matrix (Fin 3) (Fin 3) K)
    (hdet : Zm.det = 1) (μ : K)
    (hA : !![1, 0, 0; 0, -1, 0; 0, 0, -1] * Zm = Zm * !![1, 0, 0; 0, -1, 0; 0, 0, -1])
    (hB : !![0, 1, 0; 1, 0, 0; 0, 0, -1] * Zm = Zm * !![0, 1, 0; 1, 0, 0; 0, 0, -1])
    (hZZ : Zm * Zm = μ • (1 : Matrix (Fin 3) (Fin 3) K))
    (hns : ∀ w : K, Zm ≠ w • (1 : Matrix (Fin 3) (Fin 3) K)) :
    ∃ w : K, w ≠ 0 ∧ (!![-1, 0, 0; 0, -1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) =
      Zm * (w • (1 : Matrix (Fin 3) (Fin 3) K)) := by
  have h01 : Zm 0 1 = 0 := by
    have e := congrFun (congrFun hA 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three] at e
    have : (2 : K) * Zm 0 1 = 0 := by linear_combination e
    exact (mul_eq_zero.mp this).resolve_left h2
  have h02 : Zm 0 2 = 0 := by
    have e := congrFun (congrFun hA 0) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three] at e
    have : (2 : K) * Zm 0 2 = 0 := by linear_combination e
    exact (mul_eq_zero.mp this).resolve_left h2
  have h10 : Zm 1 0 = 0 := by
    have e := congrFun (congrFun hA 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three] at e
    have : (2 : K) * Zm 1 0 = 0 := by linear_combination -e
    exact (mul_eq_zero.mp this).resolve_left h2
  have h20 : Zm 2 0 = 0 := by
    have e := congrFun (congrFun hA 2) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three] at e
    have : (2 : K) * Zm 2 0 = 0 := by linear_combination -e
    exact (mul_eq_zero.mp this).resolve_left h2
  have h11 : Zm 1 1 = Zm 0 0 := by
    have e := congrFun (congrFun hB 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three] at e
    linear_combination e
  have h12 : Zm 1 2 = 0 := by
    have e := congrFun (congrFun hB 0) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three] at e
    linear_combination e - h02
  have h21 : Zm 2 1 = 0 := by
    have e := congrFun (congrFun hB 2) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three] at e
    linear_combination -e - h20
  obtain ⟨z, y, hZm⟩ : ∃ z y : K, Zm = !![z, 0, 0; 0, z, 0; 0, 0, y] :=
    ⟨Zm 0 0, Zm 2 2, by
      ext i j; fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h20, h11, h12, h21]⟩
  subst hZm
  have hz2 : z * z = μ := by
    have e := congrFun (congrFun hZZ 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using e
  have hy2 : y * y = μ := by
    have e := congrFun (congrFun hZZ 2) 2
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using e
  have hzy : y ≠ z := by
    intro h
    apply hns z
    ext i j; fin_cases i <;> fin_cases j <;> simp [h]
  have hy : y = -z := by
    have h0 : (y - z) * (y + z) = 0 := by linear_combination hy2 - hz2
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h) hzy
    · exact eq_neg_of_add_eq_zero_left h
  have hdet' : z * z * y = 1 := by simpa [Matrix.det_fin_three] using hdet
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hdet'
  refine ⟨-z⁻¹, neg_ne_zero.mpr (inv_ne_zero hz0), ?_⟩
  ext i j; fin_cases i <;> fin_cases j <;> simp [hy, hz0]

theorem deg3_centralizer (h2 : (2 : K) ≠ 0) (Zm : Matrix (Fin 3) (Fin 3) K) (hdet : Zm.det = 1)
    (u v μ : K)
    (hA : !![1, 0, 0; 0, -1, 0; 0, 0, -1] * Zm =
      (Zm * !![1, 0, 0; 0, -1, 0; 0, 0, -1]) * (u • (1 : Matrix (Fin 3) (Fin 3) K)))
    (hB : !![0, 1, 0; 1, 0, 0; 0, 0, -1] * Zm =
      (Zm * !![0, 1, 0; 1, 0, 0; 0, 0, -1]) * (v • (1 : Matrix (Fin 3) (Fin 3) K)))
    (hZZ : Zm * Zm = μ • (1 : Matrix (Fin 3) (Fin 3) K))
    (hns : ∀ w : K, Zm ≠ w • (1 : Matrix (Fin 3) (Fin 3) K)) :
    ∃ w : K, w ≠ 0 ∧ (!![-1, 0, 0; 0, -1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) =
      Zm * (w • (1 : Matrix (Fin 3) (Fin 3) K)) := by
  have hdA : (!![1, 0, 0; 0, -1, 0; 0, 0, -1] : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    simp [Matrix.det_fin_three]
  have hdB : (!![0, 1, 0; 1, 0, 0; 0, 0, -1] : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    simp [Matrix.det_fin_three]
  have hAA : (!![1, 0, 0; 0, -1, 0; 0, 0, -1] : Matrix (Fin 3) (Fin 3) K) *
      !![1, 0, 0; 0, -1, 0; 0, 0, -1] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hBB : (!![0, 1, 0; 1, 0, 0; 0, 0, -1] : Matrix (Fin 3) (Fin 3) K) *
      !![0, 1, 0; 1, 0, 0; 0, 0, -1] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hu := deg3_scalar_eq_one _ _ hAA hdA hdet u hA
  have hv := deg3_scalar_eq_one _ _ hBB hdB hdet v hB
  subst hu
  subst hv
  simp only [one_smul, Matrix.mul_one] at hA hB
  exact deg3_centralizer_core h2 Zm hdet μ hA hB hZZ hns

variable [Finite K]

theorem noStrongAb_statedProj_deg3 (h2 : (2 : K) ≠ 0) (Hg : Subgroup (GL (Fin 3) K))
    (hdet : ∀ A ∈ Hg, (A : Matrix (Fin 3) (Fin 3) K).det = 1)
    (a b c g₁ g₂ : GL (Fin 3) K) (ha : a ∈ Hg) (hb : b ∈ Hg) (hc : c ∈ Hg)
    (hg₁ : g₁ ∈ Hg) (hg₂ : g₂ ∈ Hg)
    (ham : (a : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, -1, 0; 0, 0, -1])
    (hbm : (b : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; 1, 0, 0; 0, 0, -1])
    (hcm : (c : Matrix (Fin 3) (Fin 3) K) = !![-1, 0, 0; 0, -1, 0; 0, 0, 1])
    (hg₁m : (g₁ : Matrix (Fin 3) (Fin 3) K) * (c : Matrix (Fin 3) (Fin 3) K) =
      (a : Matrix (Fin 3) (Fin 3) K) * (g₁ : Matrix (Fin 3) (Fin 3) K))
    (hg₂m : (g₂ : Matrix (Fin 3) (Fin 3) K) * (c : Matrix (Fin 3) (Fin 3) K) =
      (b : Matrix (Fin 3) (Fin 3) K) * (g₂ : Matrix (Fin 3) (Fin 3) K)) :
    NoStrongAb (⊤ : Subgroup (StatedProj Hg)) ∧ (∃ x y : StatedProj Hg, x * y ≠ y * x) ∧
      2 ∣ Nat.card (StatedProj Hg) := by
  classical
  set A : Hg := ⟨a, ha⟩ with hA
  set B : Hg := ⟨b, hb⟩ with hB
  set C : Hg := ⟨c, hc⟩ with hC
  set G₁ : Hg := ⟨g₁, hg₁⟩ with hG₁
  set G₂ : Hg := ⟨g₂, hg₂⟩ with hG₂
  have hmat : ∀ x y : Hg, (((x * y : Hg) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := fun x y => rfl
  have hone : (((1 : Hg) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := rfl
  have hAm : (((A : Hg) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 0, 0; 0, -1, 0; 0, 0, -1] := ham
  have hBm : (((B : Hg) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![0, 1, 0; 1, 0, 0; 0, 0, -1] := hbm
  have hCm : (((C : Hg) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := hcm
  have hAA : A * A = 1 := by
    apply Subtype.ext; apply Units.ext
    rw [hmat, hAm, hone]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hBB : B * B = 1 := by
    apply Subtype.ext; apply Units.ext
    rw [hmat, hBm, hone]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hCC : C * C = 1 := by
    apply Subtype.ext; apply Units.ext
    rw [hmat, hCm, hone]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hABC : (A * B) * (A * B) = C := by
    apply Subtype.ext; apply Units.ext
    rw [hmat, hmat, hAm, hBm, hCm]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hAB4 : (A * B) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, hABC, hCC]
  have hG₁C : G₁ * C = A * G₁ := by
    apply Subtype.ext; apply Units.ext
    rw [hmat, hmat]
    exact hg₁m
  have hG₂C : G₂ * C = B * G₂ := by
    apply Subtype.ext; apply Units.ext
    rw [hmat, hmat]
    exact hg₂m
  have hnc : (QuotientGroup.mk A : StatedProj Hg) * QuotientGroup.mk B ≠
      QuotientGroup.mk B * QuotientGroup.mk A := by
    intro h
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at h
    obtain ⟨u, hu⟩ := (statedProj_mk_eq_iff Hg (A * B) (B * A)).mp h
    rw [hmat, hmat, hAm, hBm] at hu
    have e22 := congrFun (congrFun hu 2) 2
    have e01 := congrFun (congrFun hu 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three] at e22 e01
    apply h2
    linear_combination e22 - e01
  refine ⟨?_, ⟨_, _, hnc⟩, ?_⟩
  · refine nasc_of_centralizer (a := (QuotientGroup.mk A : StatedProj Hg))
      (b := (QuotientGroup.mk B : StatedProj Hg)) (c := (QuotientGroup.mk C : StatedProj Hg))
      ?_ ?_ ?_ hnc ?_ ?_ ?_
    · rw [← QuotientGroup.mk_mul, hAA, QuotientGroup.mk_one]
    · rw [← QuotientGroup.mk_mul, hBB, QuotientGroup.mk_one]
    · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, hAB4, QuotientGroup.mk_one]
    · refine (isConj_iff.mpr ⟨(QuotientGroup.mk G₁ : StatedProj Hg), ?_⟩).symm
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hG₁C]
      simp
    · refine (isConj_iff.mpr ⟨(QuotientGroup.mk G₂ : StatedProj Hg), ?_⟩).symm
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hG₂C]
      simp
    · intro z hz2 hz1 hza hzb
      obtain ⟨Z, rfl⟩ := QuotientGroup.mk_surjective z
      have hZdet := hdet Z.1 Z.2
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_one] at hz2
      obtain ⟨μ', hμ'⟩ := (statedProj_mk_eq_iff Hg (Z * Z) 1).mp hz2
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hza hzb
      obtain ⟨u, hu⟩ := (statedProj_mk_eq_iff Hg (Z * A) (A * Z)).mp hza
      obtain ⟨v, hv⟩ := (statedProj_mk_eq_iff Hg (Z * B) (B * Z)).mp hzb
      rw [hmat, hmat, hAm] at hu
      rw [hmat, hmat, hBm] at hv
      rw [hone, hmat] at hμ'
      have hZZ : ((Z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((Z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          ((μ' : K)⁻¹) • (1 : Matrix (Fin 3) (Fin 3) K) := by
        have h1 : (1 : Matrix (Fin 3) (Fin 3) K) = (μ' : K) •
            (((Z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
              ((Z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
          rw [hμ', Matrix.mul_smul, Matrix.mul_one]
        calc ((Z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
              ((Z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
            = ((μ' : K)⁻¹) • ((μ' : K) • (((Z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
              ((Z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) := by
              rw [smul_smul, inv_mul_cancel₀ (Units.ne_zero μ'), one_smul]
          _ = ((μ' : K)⁻¹) • (1 : Matrix (Fin 3) (Fin 3) K) := by rw [← h1]
      have hz1' : (QuotientGroup.mk Z : StatedProj Hg) ≠ QuotientGroup.mk 1 := by
        rwa [QuotientGroup.mk_one]
      have hns : ∀ w : K, ((Z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠
          w • (1 : Matrix (Fin 3) (Fin 3) K) := by
        intro w hw
        have hw0 : w ≠ 0 := by
          rintro rfl
          rw [hw] at hZdet
          simp at hZdet
        apply hz1'
        refine (statedProj_mk_eq_iff Hg Z 1).mpr ⟨Units.mk0 w⁻¹ (inv_ne_zero hw0), ?_⟩
        rw [hone, hw, Units.val_mk0, Matrix.smul_mul, Matrix.one_mul, smul_smul,
          mul_inv_cancel₀ hw0, one_smul]
      obtain ⟨w, hw0, hw⟩ := deg3_centralizer h2 _ hZdet u v _ hu hv hZZ hns
      rw [← hCm] at hw
      exact (statedProj_mk_eq_iff Hg Z C).mpr ⟨Units.mk0 w hw0, hw⟩
  · have hA1 : (QuotientGroup.mk A : StatedProj Hg) ≠ 1 := by
      intro h
      apply hnc
      rw [h, one_mul, mul_one]
    have hAsq : (QuotientGroup.mk A : StatedProj Hg) ^ 2 = 1 := by
      rw [sq, ← QuotientGroup.mk_mul, hAA, QuotientGroup.mk_one]
    have hord : orderOf (QuotientGroup.mk A : StatedProj Hg) = 2 := orderOf_eq_prime hAsq hA1
    rw [← hord]
    exact orderOf_dvd_natCard _

end Deg3

section Closure

theorem det_eq_one_of_mem_closure {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
    {S : Set (GL n K)} (hS : ∀ A ∈ S, (A : Matrix n n K).det = 1) {A : GL n K}
    (hA : A ∈ Subgroup.closure S) : (A : Matrix n n K).det = 1 := by
  induction hA using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => simp
  | mul x y _ _ hx hy => simp [hx, hy]
  | inv x _ hx => simp [Matrix.coe_units_inv, Matrix.det_nonsing_inv, hx]

end Closure

section SL3

variable {K : Type} [Field K] [Finite K]

theorem statedSL3_data (h2 : (2 : K) ≠ 0) :
    NoStrongAb (⊤ : Subgroup (StatedProj (StatedSL 3 K))) ∧
      (∃ x y : StatedProj (StatedSL 3 K), x * y ≠ y * x) ∧
      2 ∣ Nat.card (StatedProj (StatedSL 3 K)) := by
  have hhalf : (2 : K)⁻¹ + (2 : K)⁻¹ = 1 := by rw [← two_mul]; exact mul_inv_cancel₀ h2
  have hd₂ : (!![1, 0, -(2 : K)⁻¹; -1, 0, -(2 : K)⁻¹; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K).det
      = 1 := by
    simp [Matrix.det_fin_three, hhalf]
  let a : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![1, 0, 0; 0, -1, 0; 0, 0, -1] (by simp [Matrix.det_fin_three])
  let b : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![0, 1, 0; 1, 0, 0; 0, 0, -1] (by simp [Matrix.det_fin_three])
  let c : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![-1, 0, 0; 0, -1, 0; 0, 0, 1] (by simp [Matrix.det_fin_three])
  let g₁ : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![0, 0, -1; 0, -1, 0; -1, 0, 0] (by simp [Matrix.det_fin_three])
  let g₂ : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![1, 0, -(2 : K)⁻¹; -1, 0, -(2 : K)⁻¹; 0, 1, 0] (by rw [hd₂]; exact one_ne_zero)
  have mem : ∀ M : GL (Fin 3) K, (M : Matrix (Fin 3) (Fin 3) K).det = 1 → M ∈ StatedSL 3 K :=
    fun M hM => Subgroup.subset_closure hM
  have hdetSL : ∀ A ∈ StatedSL 3 K, (A : Matrix (Fin 3) (Fin 3) K).det = 1 := fun A hA =>
    det_eq_one_of_mem_closure (fun B hB => hB) hA
  have ham : (a : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, -1, 0; 0, 0, -1] := by simp [a]
  have hbm : (b : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; 1, 0, 0; 0, 0, -1] := by simp [b]
  have hcm : (c : Matrix (Fin 3) (Fin 3) K) = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by simp [c]
  have hg₁m' : (g₁ : Matrix (Fin 3) (Fin 3) K) = !![0, 0, -1; 0, -1, 0; -1, 0, 0] := by
    simp [g₁]
  have hg₂m' : (g₂ : Matrix (Fin 3) (Fin 3) K) =
      !![1, 0, -(2 : K)⁻¹; -1, 0, -(2 : K)⁻¹; 0, 1, 0] := by simp [g₂]
  refine noStrongAb_statedProj_deg3 h2 (StatedSL 3 K) hdetSL a b c g₁ g₂ ?_ ?_ ?_ ?_ ?_
    ham hbm hcm ?_ ?_
  · exact mem a (by rw [ham]; simp [Matrix.det_fin_three])
  · exact mem b (by rw [hbm]; simp [Matrix.det_fin_three])
  · exact mem c (by rw [hcm]; simp [Matrix.det_fin_three])
  · exact mem g₁ (by rw [hg₁m']; simp [Matrix.det_fin_three])
  · exact mem g₂ (by rw [hg₂m']; exact hd₂)
  · rw [hg₁m', hcm, ham]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · rw [hg₂m', hcm, hbm]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

end SL3

section SU3

theorem exists_norm_half (p : ℕ) [hp : Fact p.Prime] (K' : Type) [Field K'] [Finite K']
    (hcard : Nat.card K' = p ^ 2) (hodd : p ≠ 2) :
    ∃ s : K', s ^ (p + 1) = (2 : K')⁻¹ := by
  have : Fintype K' := Fintype.ofFinite K'
  have hchar : CharP K' p := by
    refine charP_of_card_eq_prime_pow (f := 2) ?_
    rw [← Nat.card_eq_fintype_card]; exact hcard
  let _ : Algebra (ZMod p) K' := ZMod.algebra K' p
  obtain ⟨x, hx⟩ := FiniteField.norm_surjective (K := ZMod p) (K' := K') (2 : ZMod p)⁻¹
  refine ⟨x, ?_⟩
  have h := FiniteField.algebraMap_norm_eq_pow (K := ZMod p) (K' := K') (x := x)
  rw [hx, hcard, Nat.card_zmod] at h
  have : (p ^ 2 - 1) / (p - 1) = p + 1 := by
    have hp1 : 1 ≤ p := hp.out.one_lt.le
    have : p ^ 2 - 1 = (p + 1) * (p - 1) := by
      cases p with
      | zero => omega
      | succ n => simp; ring_nf; omega
    rw [this]
    exact Nat.mul_div_cancel _ (by have := hp.out.two_le; omega)
  rw [this] at h
  rw [← h, map_inv₀, map_ofNat]

theorem map_pow_of_signed {K : Type} [Field K] {p : ℕ} (hp : Odd p)
    (M : Matrix (Fin 3) (Fin 3) K) (hM : ∀ i j, M i j = 0 ∨ M i j = 1 ∨ M i j = -1) :
    M.map (· ^ p) = M := by
  have h0 : (0 : K) ^ p = 0 := zero_pow (by rintro rfl; exact absurd hp (by decide))
  ext i j
  rcases hM i j with h | h | h <;> simp [Matrix.map_apply, h, h0, hp.neg_one_pow]

variable {K : Type} [Field K] [Finite K]

theorem statedSU3_data (p q : ℕ) [hp : Fact p.Prime] (hq : q = p) (hodd : p ≠ 2)
    (hcard : Nat.card K = p ^ 2) :
    NoStrongAb (⊤ : Subgroup (StatedProj (StatedSU 3 q K))) ∧
      (∃ x y : StatedProj (StatedSU 3 q K), x * y ≠ y * x) ∧
      2 ∣ Nat.card (StatedProj (StatedSU 3 q K)) := by
  subst q
  have hpodd : Odd p := hp.out.odd_of_ne_two hodd
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K p := by
    refine charP_of_card_eq_prime_pow (f := 2) ?_
    rw [← Nat.card_eq_fintype_card]; exact hcard
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at h'
    exact hodd ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h')
  have h2p : (2 : K) ^ p = 2 := by
    have : (2 : K) = 1 + 1 := one_add_one_eq_two.symm
    rw [this, add_pow_char]; simp
  obtain ⟨s, hs⟩ := exists_norm_half p K hcard hodd
  have hhalf : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  have hs' : s ^ p * s = 2⁻¹ := by rw [← pow_succ]; exact hs
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hs
    exact inv_ne_zero h2 hs.symm
  set t : K := -(2 * s)⁻¹ with ht
  have hts : 2 * s * t = -1 := by
    rw [ht]; field_simp
  have ht' : t ^ p * t = 2⁻¹ := by
    rw [ht, hpodd.neg_pow, inv_pow, mul_pow, h2p, neg_mul_neg, ← mul_inv]
    congr 1
    linear_combination 4 * hs' + 2 * hhalf
  have h0 : (0 : K) ^ p = 0 := zero_pow hp.out.ne_zero
  have hg₂u : ((!![s, 0, t; -s, 0, t; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K).map (· ^ p))ᵀ *
      !![s, 0, t; -s, 0, t; 0, 1, 0] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.map_apply, hpodd.neg_pow, h0]
    all_goals first | ring1 | linear_combination 2 * hs' + hhalf | linear_combination 2 * ht' + hhalf
  have hg₂d : (!![s, 0, t; -s, 0, t; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    simp [Matrix.det_fin_three]
    linear_combination (-1) * hts
  let a : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![1, 0, 0; 0, -1, 0; 0, 0, -1] (by simp [Matrix.det_fin_three])
  let b : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![0, 1, 0; 1, 0, 0; 0, 0, -1] (by simp [Matrix.det_fin_three])
  let c : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![-1, 0, 0; 0, -1, 0; 0, 0, 1] (by simp [Matrix.det_fin_three])
  let g₁ : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![0, 0, -1; 0, -1, 0; -1, 0, 0] (by simp [Matrix.det_fin_three])
  let g₂ : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![s, 0, t; -s, 0, t; 0, 1, 0] (by rw [hg₂d]; exact one_ne_zero)
  have ham : (a : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, -1, 0; 0, 0, -1] := by simp [a]
  have hbm : (b : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; 1, 0, 0; 0, 0, -1] := by simp [b]
  have hcm : (c : Matrix (Fin 3) (Fin 3) K) = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by simp [c]
  have hg₁m' : (g₁ : Matrix (Fin 3) (Fin 3) K) = !![0, 0, -1; 0, -1, 0; -1, 0, 0] := by
    simp [g₁]
  have hg₂m' : (g₂ : Matrix (Fin 3) (Fin 3) K) = !![s, 0, t; -s, 0, t; 0, 1, 0] := by
    simp [g₂]
  have memS : ∀ M : GL (Fin 3) K, (M : Matrix (Fin 3) (Fin 3) K).det = 1 →
      ((M : Matrix (Fin 3) (Fin 3) K).map (· ^ p))ᵀ * (M : Matrix (Fin 3) (Fin 3) K) = 1 →
      M ∈ StatedSU 3 p K := fun M h1 h2 => Subgroup.subset_closure ⟨h1, h2⟩
  have hdetSU : ∀ A ∈ StatedSU 3 p K, (A : Matrix (Fin 3) (Fin 3) K).det = 1 := fun A hA =>
    det_eq_one_of_mem_closure (fun B hB => hB.1) hA
  have signed : ∀ (M : GL (Fin 3) K) (N : Matrix (Fin 3) (Fin 3) K),
      (M : Matrix (Fin 3) (Fin 3) K) = N → (∀ i j, N i j = 0 ∨ N i j = 1 ∨ N i j = -1) →
      Nᵀ * N = 1 → N.det = 1 → M ∈ StatedSU 3 p K := by
    intro M N hMN hN hNN hNd
    refine memS M (by rw [hMN]; exact hNd) ?_
    rw [hMN, map_pow_of_signed hpodd N hN]
    exact hNN
  refine noStrongAb_statedProj_deg3 h2 (StatedSU 3 p K) hdetSU a b c g₁ g₂ ?_ ?_ ?_ ?_ ?_
    ham hbm hcm ?_ ?_
  · refine signed a _ ham (by intro i j; fin_cases i <;> fin_cases j <;> simp) ?_ ?_
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    · simp [Matrix.det_fin_three]
  · refine signed b _ hbm (by intro i j; fin_cases i <;> fin_cases j <;> simp) ?_ ?_
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    · simp [Matrix.det_fin_three]
  · refine signed c _ hcm (by intro i j; fin_cases i <;> fin_cases j <;> simp) ?_ ?_
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    · simp [Matrix.det_fin_three]
  · refine signed g₁ _ hg₁m' (by intro i j; fin_cases i <;> fin_cases j <;> simp) ?_ ?_
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    · simp [Matrix.det_fin_three]
  · exact memS g₂ (by rw [hg₂m']; exact hg₂d) (by rw [hg₂m']; exact hg₂u)
  · rw [hg₁m', hcm, ham]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · rw [hg₂m', hcm, hbm]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

end SU3

end CFSG.QuasithinUnique.K1
