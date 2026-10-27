module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA6LBlockComm
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA6LLift
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA6LBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA7Block
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA6LClosure

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

open Matrix

variable {K : Type} [Field K]

theorem conj_mul_conj (S : Matrix.GeneralLinearGroup (Fin 6) K) (x y : Matrix (Fin 6) (Fin 6) K) :
    ((S : Matrix (Fin 6) (Fin 6) K) * (x * y) *
        ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) =
      ((S : Matrix (Fin 6) (Fin 6) K) * x *
        ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) *
      ((S : Matrix (Fin 6) (Fin 6) K) * y *
        ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) := by
  simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left]

theorem inv_conj_cancel (S : Matrix.GeneralLinearGroup (Fin 6) K) (x : Matrix (Fin 6) (Fin 6) K) :
    ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      ((S : Matrix (Fin 6) (Fin 6) K) * x *
        ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) *
      (S : Matrix (Fin 6) (Fin 6) K) = x := by
  have hS1 : ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      (S : Matrix (Fin 6) (Fin 6) K) = 1 := Units.inv_mul S
  simp only [Matrix.mul_assoc, hS1, Matrix.mul_one]
  exact Units.inv_mul_cancel_left S x

@[expose] noncomputable def conjS (S : Matrix.GeneralLinearGroup (Fin 6) K) :
    Matrix.SpecialLinearGroup (Fin 6) K →* Matrix.SpecialLinearGroup (Fin 6) K where
  toFun x := ⟨(S : Matrix (Fin 6) (Fin 6) K) * (x : Matrix (Fin 6) (Fin 6) K) *
      ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K), by
    have hS : (S : Matrix (Fin 6) (Fin 6) K).det *
        ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
      rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one]
    exact hS⟩
  map_one' := by
    apply Subtype.ext
    show (S : Matrix (Fin 6) (Fin 6) K) * ((1 : Matrix.SpecialLinearGroup (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) * ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
    exact Units.mul_inv S
  map_mul' x y := by
    apply Subtype.ext
    show (S : Matrix (Fin 6) (Fin 6) K) * ((x * y : Matrix.SpecialLinearGroup (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) * ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) =
      ((S : Matrix (Fin 6) (Fin 6) K) * (x : Matrix (Fin 6) (Fin 6) K) *
        ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) *
      ((S : Matrix (Fin 6) (Fin 6) K) * (y : Matrix (Fin 6) (Fin 6) K) *
        ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact conj_mul_conj S _ _

theorem conjS_coe (S : Matrix.GeneralLinearGroup (Fin 6) K)
    (x : Matrix.SpecialLinearGroup (Fin 6) K) :
    ((conjS S x : Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      (S : Matrix (Fin 6) (Fin 6) K) * (x : Matrix (Fin 6) (Fin 6) K) *
        ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := rfl

theorem conjS_injective (S : Matrix.GeneralLinearGroup (Fin 6) K) :
    Function.Injective (conjS S) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  apply Subtype.ext
  have h2 : (S : Matrix (Fin 6) (Fin 6) K) * (x : Matrix (Fin 6) (Fin 6) K) *
      ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
    have h := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 6) K =>
      (z : Matrix (Fin 6) (Fin 6) K)) hx
    rw [conjS_coe, Matrix.SpecialLinearGroup.coe_one] at h
    exact h
  have h3 := congrArg (fun M : Matrix (Fin 6) (Fin 6) K =>
    ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * M *
      (S : Matrix (Fin 6) (Fin 6) K)) h2
  simp only [Matrix.mul_one] at h3
  rw [inv_conj_cancel] at h3
  rw [h3]
  exact Units.inv_mul S

theorem Psi_injective (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))]
    (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0) : Function.Injective (Psi K hnr) := by
  intro X Y h
  apply Subtype.ext
  apply Theta_injective K
  apply blk6_fst_inj
  exact congrArg Subtype.val h

theorem eq_conj_of (S : Matrix.GeneralLinearGroup (Fin 6) K) (g x : Matrix (Fin 6) (Fin 6) K)
    (h : ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * g *
      (S : Matrix (Fin 6) (Fin 6) K) = x) :
    g = (S : Matrix (Fin 6) (Fin 6) K) * x *
      ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
  rw [← h]
  simp only [Matrix.mul_assoc]
  have hS2 : (S : Matrix (Fin 6) (Fin 6) K) *
      ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 :=
    Units.mul_inv S
  rw [← Matrix.mul_assoc, hS2, Matrix.one_mul, Matrix.mul_one]

theorem Psi_coe (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))]
    (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0) (X : Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot (KA7.quad K))) :
    ((Psi K hnr X : Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      blk6 (Theta (X : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K)))) 1 := rfl

@[expose] noncomputable def HS (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))]
    (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0) (S : Matrix.GeneralLinearGroup (Fin 6) K) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 6) K) :=
  (Psi K hnr).range.map (conjS S)

theorem mem_HS_iff (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))]
    (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0) (S : Matrix.GeneralLinearGroup (Fin 6) K)
    (h : Matrix.SpecialLinearGroup (Fin 6) K) :
    h ∈ HS K hnr S ↔ ∃ X : Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot (KA7.quad K)),
      conjS S (Psi K hnr X) = h := by
  unfold HS
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, ⟨X, rfl⟩, rfl⟩
    exact ⟨X, rfl⟩
  · rintro ⟨X, rfl⟩
    exact ⟨Psi K hnr X, ⟨X, rfl⟩, rfl⟩

theorem inv_conj_mul (S : Matrix.GeneralLinearGroup (Fin 6) K) (a b : Matrix (Fin 6) (Fin 6) K) :
    ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * a *
      (S : Matrix (Fin 6) (Fin 6) K) *
    (((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * b *
      (S : Matrix (Fin 6) (Fin 6) K)) =
    ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * (a * b) *
      (S : Matrix (Fin 6) (Fin 6) K) := by
  have hS2 : (S : Matrix (Fin 6) (Fin 6) K) *
      ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 :=
    Units.mul_inv S
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (S : Matrix (Fin 6) (Fin 6) K)
    ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K), hS2, Matrix.one_mul]

theorem coe_comm_of {x y : Matrix.SpecialLinearGroup (Fin 6) K} (h : Commute x y) :
    Commute (x : Matrix (Fin 6) (Fin 6) K) (y : Matrix (Fin 6) (Fin 6) K) := by
  have h' := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 6) K =>
    (z : Matrix (Fin 6) (Fin 6) K)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h'
  exact h'

theorem conj_sandwich (S : Matrix.GeneralLinearGroup (Fin 6) K) (c c' Ψ : Matrix (Fin 6) (Fin 6) K) :
    (S : Matrix (Fin 6) (Fin 6) K) * (((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) * c * (S : Matrix (Fin 6) (Fin 6) K) * Ψ *
      (((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * c' *
        (S : Matrix (Fin 6) (Fin 6) K))) * ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) =
    c * ((S : Matrix (Fin 6) (Fin 6) K) * Ψ * ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K)) * c' := by
  simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left, Units.inv_mul_cancel_left, Units.mul_inv,
    Matrix.mul_one]

theorem HS_normal [Finite K] [Fact (Irreducible (KA7.quad K))] (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0)
    (S : Matrix.GeneralLinearGroup (Fin 6) K)
    (g t : Matrix.SpecialLinearGroup (Fin 6) K) (G T2 : Matrix (Fin 2) (Fin 2) K)
    (eq1 : ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      (g : Matrix (Fin 6) (Fin 6) K) * (S : Matrix (Fin 6) (Fin 6) K) = blk6 1 G)
    (eq2 : ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      (t : Matrix (Fin 6) (Fin 6) K) * (S : Matrix (Fin 6) (Fin 6) K) = blk6 (D4 K) T2)
    (eq3 : ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      emat (g : Matrix (Fin 6) (Fin 6) K) * (S : Matrix (Fin 6) (Fin 6) K) = blk6 1 0)
    (c : Matrix.SpecialLinearGroup (Fin 6) K) (hcg : Commute c g) (hct : Commute c t)
    (h : Matrix.SpecialLinearGroup (Fin 6) K) (hh : h ∈ HS K hnr S) :
    c * h * c⁻¹ ∈ HS K hnr S := by
  haveI : Finite (AdjoinRoot (KA7.quad K)) := by
    haveI : Module.Finite K (AdjoinRoot (KA7.quad K)) :=
      Polynomial.Monic.finite_adjoinRoot (quad_monic K)
    exact Module.finite_of_finite K
  obtain ⟨X, rfl⟩ := (mem_HS_iff K hnr S h).mp hh
  set cM : Matrix (Fin 6) (Fin 6) K := (c : Matrix (Fin 6) (Fin 6) K) with hcM
  set c'M : Matrix (Fin 6) (Fin 6) K := ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 6) K) :
    Matrix (Fin 6) (Fin 6) K) with hc'M
  have hcc : cM * c'M = 1 := by
    rw [hcM, hc'M, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hc'c : c'M * cM = 1 := by
    rw [hcM, hc'M, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hcgM : Commute cM (g : Matrix (Fin 6) (Fin 6) K) := coe_comm_of hcg
  have hctM : Commute cM (t : Matrix (Fin 6) (Fin 6) K) := coe_comm_of hct
  have hcg'M : Commute c'M (g : Matrix (Fin 6) (Fin 6) K) := coe_comm_of hcg.inv_left
  have hct'M : Commute c'M (t : Matrix (Fin 6) (Fin 6) K) := coe_comm_of hct.inv_left
  have hcE : Commute cM (emat (g : Matrix (Fin 6) (Fin 6) K)) := by
    unfold emat
    exact (((Commute.one_right _).add_right hcgM).add_right (hcgM.pow_right 2)).smul_right _
  have hc'E : Commute c'M (emat (g : Matrix (Fin 6) (Fin 6) K)) := by
    unfold emat
    exact (((Commute.one_right _).add_right hcg'M).add_right (hcg'M.pow_right 2)).smul_right _
  have ha : ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * cM *
      (S : Matrix (Fin 6) (Fin 6) K) * blk6 1 0 = blk6 1 0 *
      (((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * cM *
        (S : Matrix (Fin 6) (Fin 6) K)) := by
    rw [← eq3, inv_conj_mul, inv_conj_mul, hcE.eq]
  have hb : ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * cM *
      (S : Matrix (Fin 6) (Fin 6) K) * blk6 (D4 K) T2 = blk6 (D4 K) T2 *
      (((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * cM *
        (S : Matrix (Fin 6) (Fin 6) K)) := by
    rw [← eq2, inv_conj_mul, inv_conj_mul, hctM.eq]
  have ha' : ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * c'M *
      (S : Matrix (Fin 6) (Fin 6) K) * blk6 1 0 = blk6 1 0 *
      (((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * c'M *
        (S : Matrix (Fin 6) (Fin 6) K)) := by
    rw [← eq3, inv_conj_mul, inv_conj_mul, hc'E.eq]
  have hb' : ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * c'M *
      (S : Matrix (Fin 6) (Fin 6) K) * blk6 (D4 K) T2 = blk6 (D4 K) T2 *
      (((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * c'M *
        (S : Matrix (Fin 6) (Fin 6) K)) := by
    rw [← eq2, inv_conj_mul, inv_conj_mul, hct'M.eq]
  have hCC' : ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * cM *
      (S : Matrix (Fin 6) (Fin 6) K) * (((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) * c'M * (S : Matrix (Fin 6) (Fin 6) K)) = 1 := by
    rw [inv_conj_mul, hcc, Matrix.mul_one, Units.inv_mul]
  have hC'C : ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * c'M *
      (S : Matrix (Fin 6) (Fin 6) K) * (((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) * cM * (S : Matrix (Fin 6) (Fin 6) K)) = 1 := by
    rw [inv_conj_mul, hc'c, Matrix.mul_one, Units.inv_mul]
  obtain ⟨Y, Y', hYY, hY'Y, hmain⟩ := normal_Psi _ _ T2 hCC' hC'C ha hb ha' hb' X
  have hdYY : (Y : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K))).det *
      (Y' : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K))).det = 1 := by
    rw [← Matrix.det_mul, hYY, Matrix.det_one]
  have hdetX : (Y * (X : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K))) * Y').det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe]
    calc Y.det * 1 * Y'.det = Y.det * Y'.det := by ring
      _ = 1 := hdYY
  obtain ⟨X', hX'⟩ : ∃ X' : Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot (KA7.quad K)),
      (X' : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K))) =
        Y * (X : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K))) * Y' :=
    ⟨⟨_, hdetX⟩, rfl⟩
  refine (mem_HS_iff K hnr S _).mpr ⟨X', ?_⟩
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, conjS_coe, conjS_coe,
    Psi_coe, Psi_coe, hX', ← hmain]
  exact conj_sandwich S cM c'M (blk6 (Theta (X : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K)))) 1)

theorem det_blk6_of_conj (S : Matrix.GeneralLinearGroup (Fin 6) K)
    (x : Matrix.SpecialLinearGroup (Fin 6) K) (A : Matrix (Fin 4) (Fin 4) K)
    (B : Matrix (Fin 2) (Fin 2) K)
    (hx : ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      (x : Matrix (Fin 6) (Fin 6) K) * (S : Matrix (Fin 6) (Fin 6) K) = blk6 A B) :
    (blk6 A B).det = 1 := by
  have hS : ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det *
      (S : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
  rw [← hx, Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one, hS]

theorem HS_commute_of (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))]
    (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0) (S : Matrix.GeneralLinearGroup (Fin 6) K)
    (x : Matrix.SpecialLinearGroup (Fin 6) K) (A : Matrix (Fin 4) (Fin 4) K)
    (B : Matrix (Fin 2) (Fin 2) K)
    (hx : ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      (x : Matrix (Fin 6) (Fin 6) K) * (S : Matrix (Fin 6) (Fin 6) K) = blk6 A B)
    (hA : ∀ X : Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot (KA7.quad K)),
      Theta (X : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K))) * A =
        A * Theta (X : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K))))
    (h : Matrix.SpecialLinearGroup (Fin 6) K) (hh : h ∈ HS K hnr S) : h * x = x * h := by
  obtain ⟨X, rfl⟩ := (mem_HS_iff K hnr S h).mp hh
  have hdet := det_blk6_of_conj S x A B hx
  obtain ⟨Bs, hBs⟩ : ∃ Bs : Matrix.SpecialLinearGroup (Fin 6) K,
      (Bs : Matrix (Fin 6) (Fin 6) K) = blk6 A B := ⟨⟨blk6 A B, hdet⟩, rfl⟩
  have hxS : x = conjS S Bs := by
    apply Subtype.ext
    rw [conjS_coe, hBs]
    exact eq_conj_of S _ _ hx
  have hcomm : Psi K hnr X * Bs = Bs * Psi K hnr X := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Psi_coe, hBs]
    refine (blk6_comm_iff _ _ _ _).mpr ⟨hA X, ?_⟩
    rw [one_mul, mul_one]
  rw [hxS, ← map_mul, ← map_mul, hcomm]

theorem D4_central_Theta (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))]
    (X : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K))) :
    Theta X * D4 K = D4 K * Theta X := by
  rw [← Theta_root K, ← Theta_mul, ← Theta_mul]
  congr 1
  rw [Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]

theorem conjPsi_injective (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))]
    (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0) (S : Matrix.GeneralLinearGroup (Fin 6) K) :
    Function.Injective ((conjS S).comp (Psi K hnr)) :=
  (conjS_injective S).comp (Psi_injective K hnr)

theorem HS_eq_range (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))]
    (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0) (S : Matrix.GeneralLinearGroup (Fin 6) K) :
    HS K hnr S = ((conjS S).comp (Psi K hnr)).range := by
  unfold HS
  rw [MonoidHom.range_comp]

noncomputable def HSiso (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))]
    (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0) (S : Matrix.GeneralLinearGroup (Fin 6) K) :
    Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot (KA7.quad K)) ≃* HS K hnr S :=
  (MonoidHom.ofInjective (conjPsi_injective K hnr S)).trans
    (MulEquiv.subgroupCongr (HS_eq_range K hnr S).symm)

theorem HS_isQuasisimple (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))]
    (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0) (S : Matrix.GeneralLinearGroup (Fin 6) K) :
    CFSG.Open.IsQuasisimple (HS K hnr S) :=
  CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.isQuasisimple_equiv (HSiso K hnr S)
    (isQuasisimple_SL2 K hnr)

noncomputable def MtSL (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))] :
    Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot (KA7.quad K)) :=
  ⟨Mt (AdjoinRoot (KA7.quad K)), by
    rw [Matrix.det_fin_two]
    simp [Mt]⟩

theorem MtSL_pow3 (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))] :
    MtSL K ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  have hq := Mt_quad (AdjoinRoot (KA7.quad K))
  have h : (Mt (AdjoinRoot (KA7.quad K)) - 1) *
      (Mt (AdjoinRoot (KA7.quad K)) * Mt (AdjoinRoot (KA7.quad K)) +
        Mt (AdjoinRoot (KA7.quad K)) + 1) = Mt (AdjoinRoot (KA7.quad K)) ^ 3 - 1 := by
    rw [pow_three']
    noncomm_ring
  rw [hq, mul_zero] at h
  show Mt (AdjoinRoot (KA7.quad K)) ^ 3 = 1
  exact sub_eq_zero.mp h.symm

theorem MtSL_not_central (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))] :
    MtSL K ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot (KA7.quad K))) := by
  intro hz
  let E : Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot (KA7.quad K)) :=
    ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have hc := (Subgroup.mem_center_iff.mp hz) E
  have h : ((E * MtSL K : Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot (KA7.quad K))) :
      Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K))) 0 0 =
      ((MtSL K * E : Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot (KA7.quad K))) :
      Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K))) 0 0 := by rw [hc]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h
  simp [E, MtSL, Mt, Matrix.mul_apply, Fin.sum_univ_two] at h

theorem HS_three_dvd (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))]
    (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0) (S : Matrix.GeneralLinearGroup (Fin 6) K) :
    3 ∣ Nat.card (HS K hnr S ⧸ Subgroup.center (HS K hnr S)) := by
  rw [← CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.card_quotient_center_equiv (HSiso K hnr S)]
  exact KA7.three_dvd_quot_of_noncentral (MtSL K) (MtSL_pow3 K) (MtSL_not_central K)

theorem HS_center_inj [Finite K] (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0)
    [Fact (Irreducible (KA7.quad K))] (S : Matrix.GeneralLinearGroup (Fin 6) K)
    (h : Matrix.SpecialLinearGroup (Fin 6) K) (hh : h ∈ HS K hnr S)
    (hc : piSL6 K h = 1) : h = 1 := by
  have hz : h ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) K) :=
    (QuotientGroup.eq_one_iff h).mp hc
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  obtain ⟨X, rfl⟩ := (mem_HS_iff K hnr S _).mp hh
  have hsc0 : Matrix.scalar (Fin 6) r = r • (1 : Matrix (Fin 6) (Fin 6) K) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.scalar_apply]
    · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hsc : ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      (r • (1 : Matrix (Fin 6) (Fin 6) K)) * (S : Matrix (Fin 6) (Fin 6) K) =
      r • (1 : Matrix (Fin 6) (Fin 6) K) := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.inv_mul]
  have h2 : ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      (r • (1 : Matrix (Fin 6) (Fin 6) K)) * (S : Matrix (Fin 6) (Fin 6) K) =
      blk6 (Theta (X : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K)))) 1 := by
    rw [← hsc0, hr, conjS_coe, Psi_coe]
    exact inv_conj_cancel S _
  have h3 : blk6 (Theta (X : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K)))) 1 =
      r • (1 : Matrix (Fin 6) (Fin 6) K) := by
    rw [← h2, hsc]
  have hr1 : r = 1 := by
    have := congrArg (fun M : Matrix (Fin 6) (Fin 6) K => M (ib 0) (ib 0)) h3
    simp [blk6_ib_ib] at this
    exact this.symm
  apply Subtype.ext
  rw [← hr, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem commute_of_pi6 (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0) {x y : Matrix.SpecialLinearGroup (Fin 6) K}
    (hy : y ^ 3 = 1) (h : piSL6 K x * piSL6 K y = piSL6 K y * piSL6 K x) : x * y = y * x := by
  set c := x * y * x⁻¹ * y⁻¹ with hcdef
  have hc1 : piSL6 K c = 1 := by
    rw [hcdef, map_mul, map_mul, map_mul, map_inv, map_inv]
    calc piSL6 K x * piSL6 K y * (piSL6 K x)⁻¹ * (piSL6 K y)⁻¹
        = piSL6 K y * piSL6 K x * (piSL6 K x)⁻¹ * (piSL6 K y)⁻¹ := by rw [h]
      _ = 1 := by simp [mul_assoc]
  have hcmem : c ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) K) :=
    (QuotientGroup.eq_one_iff _).mp hc1
  have hcommute : Commute c y := (Subgroup.mem_center_iff.mp hcmem y).symm
  have hxyx : x * y * x⁻¹ = c * y := by
    rw [hcdef]
    simp [mul_assoc]
  have hpow : (x * y * x⁻¹) ^ 3 = 1 := by
    have e : (x * y * x⁻¹) ^ 3 = x * y ^ 3 * x⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left]
    rw [e, hy]
    simp
  have h5 : c ^ 3 * y ^ 3 = 1 := by
    rw [← hcommute.mul_pow 3, ← hxyx, hpow]
  have hc3 : c ^ 3 = 1 := by
    rw [hy, mul_one] at h5
    exact h5
  have hc : c = 1 := central_eq_one_of_pow_three hnr hcmem hc3
  calc x * y = c * (y * x) := by
        rw [hcdef]
        simp [mul_assoc]
    _ = y * x := by rw [hc, one_mul]

theorem piSL6_inj_pow3 (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0) {x : Matrix.SpecialLinearGroup (Fin 6) K}
    (h3 : x ^ 3 = 1) (h : piSL6 K x = 1) : x = 1 :=
  central_eq_one_of_pow_three hnr ((QuotientGroup.eq_one_iff x).mp h) h3

theorem piSL6_surj (K : Type) [Field K] (x : Matrix.ProjectiveSpecialLinearGroup (Fin 6) K) :
    ∃ y : Matrix.SpecialLinearGroup (Fin 6) K, piSL6 K y = x := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨y, rfl⟩

theorem kerConcl_PSL6 (K : Type) [Field K] [Finite K] (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0)
    {E : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 6) K)}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hc : Nat.card E = 27) :
    CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.KerConcl E := by
  haveI : Fact (Irreducible (KA7.quad K)) := ⟨KA7.quad_irreducible hnr⟩
  obtain ⟨P, hPE, hcomm, hpow, hcardP⟩ := lift_of_elemAbelian6 hnr hE hc
  subst hPE
  haveI : Finite P := Nat.finite_of_card_ne_zero (by rw [hcardP]; norm_num)
  haveI : Fintype P := Fintype.ofFinite P
  have hcard : Fintype.card P = 27 := by rw [← Nat.card_eq_fintype_card]; exact hcardP
  obtain ⟨g, t, hg1, htnot, S, G, T2, e1, e2, e3⟩ := bridge_frame K hnr P hcomm hpow hcard
  have hgt : (g : Matrix.SpecialLinearGroup (Fin 6) K) * (t : Matrix.SpecialLinearGroup (Fin 6) K) =
      (t : Matrix.SpecialLinearGroup (Fin 6) K) * (g : Matrix.SpecialLinearGroup (Fin 6) K) :=
    hcomm _ g.2 _ t.2
  have hg3 : (g : Matrix.SpecialLinearGroup (Fin 6) K) ^ 3 = 1 := hpow _ g.2
  have ht3 : (t : Matrix.SpecialLinearGroup (Fin 6) K) ^ 3 = 1 := hpow _ t.2
  have hgS1 : (g : Matrix.SpecialLinearGroup (Fin 6) K) ≠ 1 := fun h =>
    hg1 (Subtype.ext (by rw [Subgroup.coe_one]; exact h))
  obtain ⟨F', hF'⟩ : ∃ F' : Subgroup (Matrix.SpecialLinearGroup (Fin 6) K),
      F' = Subgroup.closure {(g : Matrix.SpecialLinearGroup (Fin 6) K),
        (t : Matrix.SpecialLinearGroup (Fin 6) K)} := ⟨_, rfl⟩
  have hF'card : Nat.card F' = 9 := by
    rw [hF']; exact card_closure_pair _ _ hgt hg3 ht3 hgS1 htnot
  have hF'P : F' ≤ P := by
    rw [hF', Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact g.2
    · exact t.2
  have hgF : (g : Matrix.SpecialLinearGroup (Fin 6) K) ∈ F' := by
    rw [hF']; exact Subgroup.subset_closure (by simp)
  have htF : (t : Matrix.SpecialLinearGroup (Fin 6) K) ∈ F' := by
    rw [hF']; exact Subgroup.subset_closure (by simp)
  have hcentF : ∀ h ∈ HS K hnr S, ∀ f ∈ F', h * f = f * h := by
    intro h hh f hf
    have hsub : F' ≤ Subgroup.centralizer ({h} : Set (Matrix.SpecialLinearGroup (Fin 6) K)) := by
      rw [hF', Subgroup.closure_le]
      rintro x (rfl | rfl)
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.mp hy]
        exact HS_commute_of K hnr S _ 1 G e1 (fun X => by rw [mul_one, one_mul]) h hh
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.mp hy]
        exact HS_commute_of K hnr S _ (D4 K) T2 e2
          (fun X => D4_central_Theta K (X : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K)))) h hh
    exact Subgroup.mem_centralizer_iff.mp (hsub hf) h (Set.mem_singleton h)
  obtain ⟨F, hF⟩ : ∃ F : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 6) K),
      F = F'.map (piSL6 K) := ⟨_, rfl⟩
  have hFE : F ≤ P.map (piSL6 K) := by
    rw [hF]; exact Subgroup.map_mono hF'P
  have hFcard : Nat.card F = 9 := by
    rw [hF, card_map_eq_of_injOn (piSL6 K) F' (fun x hx hx1 =>
      piSL6_inj_pow3 hnr (hpow x (hF'P hx)) hx1), hF'card]
  have hgmem : piSL6 K (g : Matrix.SpecialLinearGroup (Fin 6) K) ∈ F := by
    rw [hF]; exact Subgroup.mem_map_of_mem (piSL6 K) hgF
  have htmem : piSL6 K (t : Matrix.SpecialLinearGroup (Fin 6) K) ∈ F := by
    rw [hF]; exact Subgroup.mem_map_of_mem (piSL6 K) htF
  have hHC : (HS K hnr S).map (piSL6 K) ≤
      Subgroup.centralizer (F : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 6) K)) := by
    intro x hx
    obtain ⟨h', hh', rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hf2 : f ∈ F := hf
    rw [hF] at hf2
    obtain ⟨f', hf', rfl⟩ := Subgroup.mem_map.mp hf2
    rw [← map_mul, ← map_mul, hcentF h' hh' f' hf']
  have hsub : CFSG.Open.IsSubnormal ((HS K hnr S).map (piSL6 K))
      (Subgroup.centralizer (F : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 6) K))) := by
    refine CFSG.Open.IsSubnormal.step hHC ?_ (CFSG.Open.IsSubnormal.refl _)
    refine ⟨fun n hn c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    obtain ⟨n', hn', hnn'⟩ := Subgroup.mem_map.mp hn
    obtain ⟨c', hc'⟩ := piSL6_surj K c.1
    have hcg : c' * (g : Matrix.SpecialLinearGroup (Fin 6) K) =
        (g : Matrix.SpecialLinearGroup (Fin 6) K) * c' :=
      commute_of_pi6 hnr hg3 (by
        rw [hc']
        exact (Subgroup.mem_centralizer_iff.mp c.2 (piSL6 K (g : Matrix.SpecialLinearGroup (Fin 6) K))
          hgmem).symm)
    have hct : c' * (t : Matrix.SpecialLinearGroup (Fin 6) K) =
        (t : Matrix.SpecialLinearGroup (Fin 6) K) * c' :=
      commute_of_pi6 hnr ht3 (by
        rw [hc']
        exact (Subgroup.mem_centralizer_iff.mp c.2 (piSL6 K (t : Matrix.SpecialLinearGroup (Fin 6) K))
          htmem).symm)
    rw [← hc', ← hnn', ← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem (piSL6 K)
      (HS_normal hnr S (g : Matrix.SpecialLinearGroup (Fin 6) K)
        (t : Matrix.SpecialLinearGroup (Fin 6) K) G T2 e1 e2 e3 c' hcg hct n' hn')
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥(HS K hnr S) →* ↥((HS K hnr S).map (piSL6 K)),
      ∀ x : ↥(HS K hnr S), ((ρ x : ↥((HS K hnr S).map (piSL6 K))) :
        Matrix.ProjectiveSpecialLinearGroup (Fin 6) K) =
          piSL6 K (x : Matrix.SpecialLinearGroup (Fin 6) K) :=
    ⟨((piSL6 K).comp (HS K hnr S).subtype).codRestrict ((HS K hnr S).map (piSL6 K))
      (fun x => Subgroup.mem_map_of_mem (piSL6 K) x.2), fun x => rfl⟩
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : piSL6 K (x : Matrix.SpecialLinearGroup (Fin 6) K) = 1 := by
      rw [← hρ, hx, Subgroup.coe_one]
    exact Subtype.ext (HS_center_inj hnr S x.1 x.2 hx')
  have hρsurj : Function.Surjective ρ := by
    intro y
    obtain ⟨h', hh', hy⟩ := Subgroup.mem_map.mp y.2
    refine ⟨⟨h', hh'⟩, Subtype.ext ?_⟩
    rw [hρ]
    exact hy
  let φ : ↥(HS K hnr S) ≃* ↥((HS K hnr S).map (piSL6 K)) :=
    MulEquiv.ofBijective ρ ⟨hρinj, hρsurj⟩
  have hqH : CFSG.Open.IsQuasisimple ↥((HS K hnr S).map (piSL6 K)) :=
    CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.isQuasisimple_equiv φ (HS_isQuasisimple K hnr S)
  have hdvdH : 3 ∣ Nat.card (↥((HS K hnr S).map (piSL6 K)) ⧸
      Subgroup.center ↥((HS K hnr S).map (piSL6 K))) := by
    rw [← CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.card_quotient_center_equiv φ]
    exact HS_three_dvd K hnr S
  exact ⟨F, hFE, hFcard, (HS K hnr S).map (piSL6 K), hHC, hsub, hqH, hdvdH⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

end
