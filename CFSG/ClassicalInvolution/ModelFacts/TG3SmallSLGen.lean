module

public import CFSG.LinearAlgebra.LinearGroups.Generation
public import CFSG.ClassicalInvolution.Models.LinearPairs.Intrinsic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction

public section

namespace CFSG.ClassicalInvolution.ModelFacts.TG3

open Matrix CFSG.ClassicalInvolution.Models
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open scoped MatrixGroups commutatorElement

section Std

variable {K : Type} [Field K]

def sl4NegDiag : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal ![-1, -1, 1, 1]

def sl4Cx : Matrix (Fin 4) (Fin 4) K := !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0]

theorem det_sl4NegDiag : (sl4NegDiag : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  simp [sl4NegDiag, Matrix.det_diagonal, Fin.prod_univ_four]

theorem det_sl4Cx : (sl4Cx : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  simp [sl4Cx, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

def sl4NegDiagSL : SL(4, K) := ⟨sl4NegDiag, det_sl4NegDiag⟩

def sl4CxSL : SL(4, K) := ⟨sl4Cx, det_sl4Cx⟩

theorem single_mul_diagonal_comm (d : Fin 4 → K) (i j : Fin 4) (c : K) (h : d i = d j) :
    Matrix.single i j c * Matrix.diagonal d = Matrix.diagonal d * Matrix.single i j c := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hab : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := hab
    simp [h, mul_comm]
  · simp [hab]

theorem transvection_comm_sl4NegDiagSL {i j : Fin 4} (hij : i ≠ j)
    (h : (![-1, -1, 1, 1] : Fin 4 → K) i = (![-1, -1, 1, 1] : Fin 4 → K) j) (c : K) :
    SpecialLinearGroup.transvection hij c * sl4NegDiagSL =
      sl4NegDiagSL * SpecialLinearGroup.transvection hij c := by
  have hm : (1 + Matrix.single i j c) * sl4NegDiag = sl4NegDiag * (1 + Matrix.single i j c) := by
    rw [sl4NegDiag, add_mul, mul_add, one_mul, mul_one, single_mul_diagonal_comm _ i j c h]
  exact Matrix.SpecialLinearGroup.ext _ _ fun a b => congrFun (congrFun hm a) b

theorem sl4_T1_mat : ((1 + Matrix.single (0 : Fin 4) (2 : Fin 4) (1 : K)) *
    (1 + Matrix.single (1 : Fin 4) (3 : Fin 4) (1 : K))) * sl4Cx =
    sl4Cx * ((1 + Matrix.single (0 : Fin 4) (2 : Fin 4) (1 : K)) *
      (1 + Matrix.single (1 : Fin 4) (3 : Fin 4) (1 : K))) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [sl4Cx, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply]

theorem sl4_T2_mat : ((1 + Matrix.single (2 : Fin 4) (0 : Fin 4) (1 : K)) *
    (1 + Matrix.single (3 : Fin 4) (1 : Fin 4) (1 : K))) * sl4Cx =
    sl4Cx * ((1 + Matrix.single (2 : Fin 4) (0 : Fin 4) (1 : K)) *
      (1 + Matrix.single (3 : Fin 4) (1 : Fin 4) (1 : K))) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [sl4Cx, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply]

theorem sl4_T1_comm :
    (SpecialLinearGroup.transvection (show (0 : Fin 4) ≠ 2 by decide) (1 : K) *
      SpecialLinearGroup.transvection (show (1 : Fin 4) ≠ 3 by decide) (1 : K)) * sl4CxSL =
    sl4CxSL * (SpecialLinearGroup.transvection (show (0 : Fin 4) ≠ 2 by decide) (1 : K) *
      SpecialLinearGroup.transvection (show (1 : Fin 4) ≠ 3 by decide) (1 : K)) :=
  Matrix.SpecialLinearGroup.ext _ _ fun a b => congrFun (congrFun sl4_T1_mat a) b

theorem sl4_T2_comm :
    (SpecialLinearGroup.transvection (show (2 : Fin 4) ≠ 0 by decide) (1 : K) *
      SpecialLinearGroup.transvection (show (3 : Fin 4) ≠ 1 by decide) (1 : K)) * sl4CxSL =
    sl4CxSL * (SpecialLinearGroup.transvection (show (2 : Fin 4) ≠ 0 by decide) (1 : K) *
      SpecialLinearGroup.transvection (show (3 : Fin 4) ≠ 1 by decide) (1 : K)) :=
  Matrix.SpecialLinearGroup.ext _ _ fun a b => congrFun (congrFun sl4_T2_mat a) b

theorem commutatorElement_mul_of_commute {G : Type*} [Group G] {x y z : G} (hxz : Commute x z) :
    ⁅x, y * z⁆ = ⁅x, y⁆ := by
  simp only [commutatorElement_def]
  have h : z * x⁻¹ = x⁻¹ * z := hxz.inv_left.eq.symm
  calc x * (y * z) * x⁻¹ * (y * z)⁻¹ = x * y * (z * x⁻¹) * z⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * z) * z⁻¹ * y⁻¹ := by rw [h]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem sl4_std_gen (hK : ∀ c : K, c = 0 ∨ c = 1 ∨ c = -1) :
    Subgroup.centralizer ({sl4NegDiagSL} : Set SL(4, K)) ⊔
      Subgroup.centralizer ({sl4CxSL} : Set SL(4, K)) = ⊤ := by
  set H : Subgroup SL(4, K) := Subgroup.centralizer ({sl4NegDiagSL} : Set SL(4, K)) ⊔
    Subgroup.centralizer ({sl4CxSL} : Set SL(4, K)) with hH
  have hD : ∀ g : SL(4, K), g * sl4NegDiagSL = sl4NegDiagSL * g → g ∈ H := fun g hg =>
    Subgroup.mem_sup_left (Subgroup.mem_centralizer_singleton_iff.mpr hg)
  have hJ : ∀ g : SL(4, K), g * sl4CxSL = sl4CxSL * g → g ∈ H := fun g hg =>
    Subgroup.mem_sup_right (Subgroup.mem_centralizer_singleton_iff.mpr hg)
  have hcm : ∀ {x y : SL(4, K)}, x ∈ H → y ∈ H → ⁅x, y⁆ ∈ H := fun hx hy => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)
  have n01 : (0 : Fin 4) ≠ 1 := by decide
  have n02 : (0 : Fin 4) ≠ 2 := by decide
  have n03 : (0 : Fin 4) ≠ 3 := by decide
  have n10 : (1 : Fin 4) ≠ 0 := by decide
  have n12 : (1 : Fin 4) ≠ 2 := by decide
  have n13 : (1 : Fin 4) ≠ 3 := by decide
  have n20 : (2 : Fin 4) ≠ 0 := by decide
  have n21 : (2 : Fin 4) ≠ 1 := by decide
  have n23 : (2 : Fin 4) ≠ 3 := by decide
  have n30 : (3 : Fin 4) ≠ 0 := by decide
  have n31 : (3 : Fin 4) ≠ 1 := by decide
  have n32 : (3 : Fin 4) ≠ 2 := by decide
  have b01 : SpecialLinearGroup.transvection n01 (1 : K) ∈ H :=
    hD _ (transvection_comm_sl4NegDiagSL n01 (by simp) 1)
  have b10 : SpecialLinearGroup.transvection n10 (1 : K) ∈ H :=
    hD _ (transvection_comm_sl4NegDiagSL n10 (by simp) 1)
  have b23 : SpecialLinearGroup.transvection n23 (1 : K) ∈ H :=
    hD _ (transvection_comm_sl4NegDiagSL n23 (by simp) 1)
  have b32 : SpecialLinearGroup.transvection n32 (1 : K) ∈ H :=
    hD _ (transvection_comm_sl4NegDiagSL n32 (by simp) 1)
  have hT1 : SpecialLinearGroup.transvection n02 (1 : K) *
      SpecialLinearGroup.transvection n13 (1 : K) ∈ H := hJ _ sl4_T1_comm
  have hT2 : SpecialLinearGroup.transvection n20 (1 : K) *
      SpecialLinearGroup.transvection n31 (1 : K) ∈ H := hJ _ sl4_T2_comm
  have h12 : SpecialLinearGroup.transvection n12 (1 : K) ∈ H := by
    have hc := SpecialLinearGroup.commute_transvection n10 n13 (by decide : (0 : Fin 4) ≠ 1)
      (by decide : (3 : Fin 4) ≠ 1) (1 : K) (1 : K)
    have h1 := SpecialLinearGroup.commutatorElement_transvection n10 n02 n12 (1 : K) 1
    rw [mul_one] at h1
    rw [← h1, ← commutatorElement_mul_of_commute hc]
    exact hcm b10 hT1
  have h13 : SpecialLinearGroup.transvection n13 (1 : K) ∈ H := by
    have h1 := SpecialLinearGroup.commutatorElement_transvection n12 n23 n13 (1 : K) 1
    rw [mul_one] at h1
    rw [← h1]
    exact hcm h12 b23
  have h02 : SpecialLinearGroup.transvection n02 (1 : K) ∈ H := by
    have := H.mul_mem hT1 (H.inv_mem h13)
    rwa [mul_inv_cancel_right] at this
  have h03 : SpecialLinearGroup.transvection n03 (1 : K) ∈ H := by
    have h1 := SpecialLinearGroup.commutatorElement_transvection n02 n23 n03 (1 : K) 1
    rw [mul_one] at h1
    rw [← h1]
    exact hcm h02 b23
  have h30 : SpecialLinearGroup.transvection n30 (1 : K) ∈ H := by
    have hc := SpecialLinearGroup.commute_transvection n32 n31 (by decide : (2 : Fin 4) ≠ 3)
      (by decide : (1 : Fin 4) ≠ 3) (1 : K) (1 : K)
    have h1 := SpecialLinearGroup.commutatorElement_transvection n32 n20 n30 (1 : K) 1
    rw [mul_one] at h1
    rw [← h1, ← commutatorElement_mul_of_commute hc]
    exact hcm b32 hT2
  have h31 : SpecialLinearGroup.transvection n31 (1 : K) ∈ H := by
    have h1 := SpecialLinearGroup.commutatorElement_transvection n30 n01 n31 (1 : K) 1
    rw [mul_one] at h1
    rw [← h1]
    exact hcm h30 b01
  have h20 : SpecialLinearGroup.transvection n20 (1 : K) ∈ H := by
    have := H.mul_mem hT2 (H.inv_mem h31)
    rwa [mul_inv_cancel_right] at this
  have h21 : SpecialLinearGroup.transvection n21 (1 : K) ∈ H := by
    have h1 := SpecialLinearGroup.commutatorElement_transvection n20 n01 n21 (1 : K) 1
    rw [mul_one] at h1
    rw [← h1]
    exact hcm h20 b01
  have hall : ∀ (i j : Fin 4) (hij : i ≠ j) (c : K),
      SpecialLinearGroup.transvection hij c ∈ H := by
    intro i j hij c
    have h1 : SpecialLinearGroup.transvection hij (1 : K) ∈ H := by
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact b01
      · exact h02
      · exact h03
      · exact b10
      · exact absurd rfl hij
      · exact h12
      · exact h13
      · exact h20
      · exact h21
      · exact absurd rfl hij
      · exact b23
      · exact h30
      · exact h31
      · exact b32
      · exact absurd rfl hij
    rcases hK c with rfl | rfl | rfl
    · rw [SpecialLinearGroup.transvection_coeff_zero]
      exact H.one_mem
    · exact h1
    · rw [← SpecialLinearGroup.transvection_inv]
      exact H.inv_mem h1
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 4) (K := K)]
  refine (Subgroup.closure_le H).2 ?_
  rintro _ ⟨i, j, hij, c, rfl⟩
  exact hall i j hij c

end Std

section Transport

variable {K : Type} [Field K]

theorem linearIndependent_pair_of_end_sq_neg_one {V : Type*} [AddCommGroup V] [Module K V]
    (f : V →ₗ[K] V) (hf : ∀ v, f (f v) = -v) (hno : ∀ a : K, a * a ≠ -1) {x : V} (hx0 : x ≠ 0) :
    LinearIndependent K ![x, f x] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right hx0, rfl⟩
  · exfalso
    have h1 : f x = (-(s / t)) • x := by
      have : t • f x = (-s) • x := by
        rw [neg_smul]
        exact eq_neg_of_add_eq_zero_right hst
      calc f x = t⁻¹ • (t • f x) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = t⁻¹ • ((-s) • x) := by rw [this]
        _ = (-(s / t)) • x := by rw [smul_smul]; congr 1; field_simp
    have h2 : f (f x) = ((-(s / t)) * (-(s / t))) • x := by
      rw [h1, map_smul, h1, smul_smul]
    rw [hf x] at h2
    have h3 : (((-(s / t)) * (-(s / t))) + 1) • x = 0 := by
      rw [add_smul, one_smul, ← h2]; simp
    have h4 := (smul_eq_zero.mp h3).resolve_right hx0
    exact hno (-(s / t)) (by linear_combination h4)

theorem sl4_gen (hK : ∀ c : K, c = 0 ∨ c = 1 ∨ c = -1) (hno : ∀ a : K, a * a ≠ -1)
    (h2 : (2 : K) ≠ 0) (i J : SL(4, K)) (hi : i * i = 1) (hiJ : i * J = J * i)
    (hJ : (J : Matrix (Fin 4) (Fin 4) K) * J = -1)
    (hd : Module.finrank K (eigSpace (i : Matrix (Fin 4) (Fin 4) K) (-1)) = 2) :
    Subgroup.centralizer ({i} : Set SL(4, K)) ⊔ Subgroup.centralizer ({J} : Set SL(4, K)) = ⊤ := by
  classical
  set A : Matrix (Fin 4) (Fin 4) K := (i : Matrix (Fin 4) (Fin 4) K) with hA
  set Jm : Matrix (Fin 4) (Fin 4) K := (J : Matrix (Fin 4) (Fin 4) K) with hJm
  have hAA : A * A = 1 := by
    rw [hA, ← Matrix.SpecialLinearGroup.coe_mul, hi, Matrix.SpecialLinearGroup.coe_one]
  have hAJ : A * Jm = Jm * A := by
    rw [hA, hJm, ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hiJ]
  have hJJ : ∀ v, Jm *ᵥ (Jm *ᵥ v) = -v := fun v => by
    rw [Matrix.mulVec_mulVec, hJ, Matrix.neg_mulVec, Matrix.one_mulVec]
  have hcompl := isCompl_eigSpace h2 hAA
  have hAJv : ∀ v, A *ᵥ (Jm *ᵥ v) = Jm *ᵥ (A *ᵥ v) := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hAJ]
  have hJneg : ∀ v ∈ eigSpace A (-1), Jm *ᵥ v ∈ eigSpace A (-1) := fun v hv => by
    rw [mem_eigSpace_neg_one] at hv ⊢
    rw [hAJv, hv, Matrix.mulVec_neg]
  have hJpos : ∀ v ∈ eigSpace A 1, Jm *ᵥ v ∈ eigSpace A 1 := fun v hv => by
    rw [mem_eigSpace_one] at hv ⊢
    rw [hAJv, hv]
  obtain ⟨u, hu, hu0⟩ : ∃ u ∈ eigSpace A (-1), u ≠ 0 := by
    have : 0 < Module.finrank K (eigSpace A (-1)) := by rw [hd]; norm_num
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp this
    exact ⟨x, x.2, fun h => hx (Subtype.ext h)⟩
  obtain ⟨w, hw, hw0⟩ : ∃ w ∈ eigSpace A 1, w ≠ 0 := by
    have h4 := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [hd, Module.finrank_fin_fun] at h4
    have : 0 < Module.finrank K (eigSpace A 1) := by omega
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp this
    exact ⟨x, x.2, fun h => hx (Subtype.ext h)⟩
  have hf : ∀ v, Matrix.toLin' Jm (Matrix.toLin' Jm v) = -v := fun v => by
    simp only [Matrix.toLin'_apply]
    exact hJJ v
  have hind₁ : LinearIndependent K ![u, Jm *ᵥ u] :=
    linearIndependent_pair_of_end_sq_neg_one (Matrix.toLin' Jm) hf hno hu0
  have hind₂ : LinearIndependent K ![w, Jm *ᵥ w] :=
    linearIndependent_pair_of_end_sq_neg_one (Matrix.toLin' Jm) hf hno hw0
  set b : Fin 4 → Fin 4 → K := ![u, Jm *ᵥ u, w, Jm *ᵥ w] with hb
  set P : Matrix (Fin 4) (Fin 4) K := Matrix.of fun r c => b c r with hP
  have hPx : ∀ x : Fin 4 → K, P *ᵥ x = (x 0 • u + x 1 • Jm *ᵥ u) + (x 2 • w + x 3 • Jm *ᵥ w) := by
    intro x
    ext r
    simp only [hP, hb, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  have hker : ∀ x : Fin 4 → K, P *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [hPx] at hx
    have ha : x 0 • u + x 1 • Jm *ᵥ u ∈ eigSpace A (-1) :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ hu) (Submodule.smul_mem _ _ (hJneg u hu))
    have hc : x 2 • w + x 3 • Jm *ᵥ w ∈ eigSpace A 1 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ hw) (Submodule.smul_mem _ _ (hJpos w hw))
    have hsum : x 0 • u + x 1 • Jm *ᵥ u = -(x 2 • w + x 3 • Jm *ᵥ w) :=
      eq_neg_of_add_eq_zero_left hx
    have hmem : x 0 • u + x 1 • Jm *ᵥ u ∈ eigSpace A (-1) ⊓ eigSpace A 1 :=
      Submodule.mem_inf.mpr ⟨ha, by rw [hsum]; exact Submodule.neg_mem _ hc⟩
    rw [hcompl.inf_eq_bot, Submodule.mem_bot] at hmem
    have hc0 : x 2 • w + x 3 • Jm *ᵥ w = 0 := by
      rw [hmem, zero_add] at hx
      exact hx
    obtain ⟨h0, h1⟩ := LinearIndependent.pair_iff.mp hind₁ (x 0) (x 1) hmem
    obtain ⟨h2', h3⟩ := LinearIndependent.pair_iff.mp hind₂ (x 2) (x 3) hc0
    funext c
    fin_cases c
    · exact h0
    · exact h1
    · exact h2'
    · exact h3
  have hPinj : Function.Injective P.mulVec := by
    intro x y hxy
    have : P *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr hxy
    exact sub_eq_zero.mp (hker _ this)
  have hPu : IsUnit P := Matrix.mulVec_injective_iff_isUnit.mp hPinj
  have hbA : ∀ c : Fin 4, A *ᵥ b c = (![-1, -1, 1, 1] : Fin 4 → K) c • b c := by
    intro c
    fin_cases c
    · simpa [hb] using mem_eigSpace_neg_one.mp hu
    · simpa [hb] using mem_eigSpace_neg_one.mp (hJneg u hu)
    · simpa [hb] using mem_eigSpace_one.mp hw
    · simpa [hb] using mem_eigSpace_one.mp (hJpos w hw)
  have hAP : A * P = P * sl4NegDiag := by
    ext r c
    have e1 : (A * P) r c = (A *ᵥ b c) r := by
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hP, Matrix.of_apply]
    rw [e1, hbA c, sl4NegDiag, Matrix.mul_diagonal, Pi.smul_apply, smul_eq_mul, hP, Matrix.of_apply,
      mul_comm]
  have hJP : Jm * P = P * sl4Cx := by
    ext r c
    have e1 : (Jm * P) r c = (Jm *ᵥ b c) r := by
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hP, Matrix.of_apply]
    rw [e1]
    fin_cases c
    · simp [hb, hP, sl4Cx, Matrix.mul_apply, Fin.sum_univ_four]
    · simp [hb, hP, sl4Cx, Matrix.mul_apply, Fin.sum_univ_four, hJJ u]
    · simp [hb, hP, sl4Cx, Matrix.mul_apply, Fin.sum_univ_four]
    · simp [hb, hP, sl4Cx, Matrix.mul_apply, Fin.sum_univ_four, hJJ w]
  let Pu : Matrix.GeneralLinearGroup (Fin 4) K := hPu.unit
  have hPu_val : (Pu : Matrix (Fin 4) (Fin 4) K) = P := hPu.unit_spec
  have hmul :
      P * ((Pu⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← hPu_val]
    exact Units.mul_inv Pu
  have hσd : slConjugation 4 K Pu sl4NegDiagSL = i := by
    have hm : (slConjugation 4 K Pu sl4NegDiagSL : Matrix (Fin 4) (Fin 4) K) = A := by
      rw [slConjugation_matrix, hPu_val]
      change P * sl4NegDiag * _ = A
      rw [← hAP, Matrix.mul_assoc, hmul, Matrix.mul_one]
    exact Matrix.SpecialLinearGroup.ext _ _ fun a b => congrFun (congrFun hm a) b
  have hσj : slConjugation 4 K Pu sl4CxSL = J := by
    have hm : (slConjugation 4 K Pu sl4CxSL : Matrix (Fin 4) (Fin 4) K) = Jm := by
      rw [slConjugation_matrix, hPu_val]
      change P * sl4Cx * _ = Jm
      rw [← hJP, Matrix.mul_assoc, hmul, Matrix.mul_one]
    exact Matrix.SpecialLinearGroup.ext _ _ fun a b => congrFun (congrFun hm a) b
  set σ := slConjugation 4 K Pu with hσ
  have hle : (Subgroup.centralizer ({sl4NegDiagSL} : Set SL(4, K)) ⊔
      Subgroup.centralizer ({sl4CxSL} : Set SL(4, K))).map σ.toMonoidHom ≤
        Subgroup.centralizer ({i} : Set SL(4, K)) ⊔ Subgroup.centralizer ({J} : Set SL(4, K)) := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩
      have hg' := Subgroup.mem_centralizer_singleton_iff.mp hg
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      change σ g * i = i * σ g
      rw [← hσd, ← map_mul, ← map_mul, hg']
    · rintro _ ⟨g, hg, rfl⟩
      have hg' := Subgroup.mem_centralizer_singleton_iff.mp hg
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      change σ g * J = J * σ g
      rw [← hσj, ← map_mul, ← map_mul, hg']
  rw [eq_top_iff]
  intro g _
  have hg : σ.symm g ∈ (⊤ : Subgroup SL(4, K)) := Subgroup.mem_top _
  rw [← sl4_std_gen hK] at hg
  exact hle (Subgroup.mem_map.mpr ⟨σ.symm g, hg, σ.apply_symm_apply g⟩)

end Transport

end CFSG.ClassicalInvolution.ModelFacts.TG3
