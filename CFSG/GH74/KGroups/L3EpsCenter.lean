module

public import CFSG.GH74.KGroups.L3EpsTest
public import CFSG.GH74.KGroups.L3EpsAbs
public import CFSG.GH74.KGroups.L3EpsLin
public import CFSG.GH74.KGroups.L3EpsUni

public section

namespace CFSG.GH74.KGroups.L3Eps

open Subgroup Matrix
open scoped MatrixGroups

section Abstract

theorem isPGroup_closure_dihedral {G : Type*} [Group G] {e r : G} (he : e ^ 4 = 1) (hr : r ^ 2 = 1)
    (hrel : r * e * r⁻¹ = e⁻¹) : IsPGroup 2 (Subgroup.closure {e, r}) := by
  have hrr : r * r = 1 := by rw [← sq]; exact hr
  have hr' : r⁻¹ = r := inv_eq_of_mul_eq_one_right hrr
  have h3 : e⁻¹ = e ^ 3 := by
    apply inv_eq_of_mul_eq_one_right
    calc e * e ^ 3 = e ^ 4 := by rw [← pow_succ']
      _ = 1 := he
  have hre : r * e = e ^ 3 * r := by
    rw [hr', h3] at hrel
    calc r * e = r * e * r * r := by rw [mul_assoc (r * e) r r, hrr, mul_one]
      _ = e ^ 3 * r := by rw [hrel]
  have hree : ∀ l : ℕ, r * e ^ l = e ^ (3 * l) * r := by
    intro l
    induction l with
    | zero => simp
    | succ l ih =>
      calc r * e ^ (l + 1) = (r * e ^ l) * e := by rw [pow_succ, mul_assoc]
        _ = e ^ (3 * l) * (r * e) := by rw [ih, mul_assoc]
        _ = e ^ (3 * l) * (e ^ 3 * r) := by rw [hre]
        _ = e ^ (3 * (l + 1)) * r := by rw [← mul_assoc, ← pow_add]; congr 2
  have he4 : ∀ k : ℕ, e ^ (4 * k) = 1 := fun k => by rw [pow_mul, he, one_pow]
  have hmain : ∀ g ∈ Subgroup.closure ({e, r} : Set G), ∃ k : ℕ, g = e ^ k ∨ g = e ^ k * r := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨1, Or.inl (pow_one _).symm⟩
      · exact ⟨0, Or.inr (by simp)⟩
    | one => exact ⟨0, Or.inl (pow_zero _).symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨k, hk⟩ := hx
      obtain ⟨l, hl⟩ := hy
      rcases hk with rfl | rfl <;> rcases hl with rfl | rfl
      · exact ⟨k + l, Or.inl (pow_add _ _ _).symm⟩
      · exact ⟨k + l, Or.inr (by rw [pow_add, mul_assoc])⟩
      · exact ⟨k + 3 * l, Or.inr (by rw [mul_assoc, hree l, ← mul_assoc, ← pow_add])⟩
      · refine ⟨k + 3 * l, Or.inl ?_⟩
        calc e ^ k * r * (e ^ l * r) = e ^ k * (r * e ^ l) * r := by simp only [mul_assoc]
          _ = e ^ k * (e ^ (3 * l) * r) * r := by rw [hree l]
          _ = e ^ (k + 3 * l) * (r * r) := by simp only [mul_assoc, pow_add]
          _ = e ^ (k + 3 * l) := by rw [hrr, mul_one]
    | inv x _ hx =>
      obtain ⟨k, hk⟩ := hx
      rcases hk with rfl | rfl
      · refine ⟨3 * k, Or.inl ?_⟩
        apply inv_eq_of_mul_eq_one_right
        rw [← pow_add]
        have := he4 k
        rwa [show k + 3 * k = 4 * k by ring]
      · refine ⟨9 * k, Or.inr ?_⟩
        rw [_root_.mul_inv_rev, hr']
        have h1 : (e ^ k)⁻¹ = e ^ (3 * k) := by
          apply inv_eq_of_mul_eq_one_right
          rw [← pow_add]
          have := he4 k
          rwa [show k + 3 * k = 4 * k by ring]
        rw [h1, hree (3 * k)]
        congr 2
        ring
  intro g
  refine ⟨3, Subtype.ext ?_⟩
  obtain ⟨k, hk⟩ := hmain g g.2
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  show (g : G) ^ 8 = 1
  rcases hk with hk | hk
  · rw [hk, ← pow_mul, show k * 8 = 4 * (2 * k) by ring, he4]
  · have h2 : (e ^ k * r) ^ 2 = 1 := by
      calc (e ^ k * r) ^ 2 = e ^ k * (r * e ^ k) * r := by rw [sq]; simp only [mul_assoc]
        _ = e ^ k * (e ^ (3 * k) * r) * r := by rw [hree k]
        _ = e ^ (k + 3 * k) * (r * r) := by simp only [mul_assoc, pow_add]
        _ = 1 := by rw [hrr, mul_one, show k + 3 * k = 4 * k by ring, he4]
    rw [hk, show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, h2, one_pow]

theorem exists_conj_le_of_isPGroup {X : Type*} [Group X] [Finite X] {S E : Subgroup X}
    (hS : IsPGroup 2 S) (hmax : ∀ T : Subgroup X, IsPGroup 2 T → S ≤ T → T ≤ S)
    (hE : IsPGroup 2 E) : ∃ x : X, ∀ e ∈ E, x⁻¹ * e * x ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 X := ⟨S, hS, fun {Q} hQ hSQ => le_antisymm (hmax Q hQ hSQ) hSQ⟩
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X P Q
  refine ⟨x, fun e he => ?_⟩
  have he' : e ∈ (Q : Subgroup X) := hQ he
  rw [← hx] at he'
  have := (Subgroup.mem_pointwise_smul_iff_inv_smul_mem).1 he'
  simpa [mul_assoc] using this

theorem center_cyclic_exp {X : Type*} [Group X] {S T : Subgroup X} (hT : IsCyclic T) {N : ℕ}
    (hTN : ∀ t ∈ T, t ^ N = 1) {x : X}
    (hx : ∀ z ∈ S ⊓ Subgroup.centralizer (S : Set X), x * z * x⁻¹ ∈ T) :
    IsCyclic ↥(S ⊓ Subgroup.centralizer (S : Set X)) ∧
      ∀ z ∈ S ⊓ Subgroup.centralizer (S : Set X), z ^ N = 1 := by
  let ψ : ↥(S ⊓ Subgroup.centralizer (S : Set X)) →* T :=
    (((MulAut.conj x).toMonoidHom.comp (S ⊓ Subgroup.centralizer (S : Set X)).subtype)).codRestrict T
      (fun z => hx z z.2)
  have hψ : Function.Injective ψ := by
    intro a b hab
    have : x * (a : X) * x⁻¹ = x * (b : X) * x⁻¹ := congrArg Subtype.val hab
    apply Subtype.ext
    simpa using this
  refine ⟨isCyclic_of_injective ψ hψ, fun z hz => ?_⟩
  have h1 := hTN _ (hx z hz)
  have h2 : x * z ^ N * x⁻¹ = 1 := by
    rw [← MulAut.conj_apply, map_pow]
    exact h1
  have h3 : z ^ N = 1 := by
    calc z ^ N = x⁻¹ * (x * z ^ N * x⁻¹) * x := by group
      _ = 1 := by rw [h2]; group
  exact h3

end Abstract

section Matrices

variable {K : Type*} [Field K]

@[expose] def eMat : Matrix (Fin 3) (Fin 3) K := !![0, -1, 0; 1, 0, 0; 0, 0, 1]

@[expose] def rMat : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, -1, 0; 0, 0, -1]

theorem det_eMat : (eMat : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [eMat, Matrix.det_fin_three]

theorem det_rMat : (rMat : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [rMat, Matrix.det_fin_three]

@[expose] def eSL : SL(3, K) := ⟨eMat, det_eMat⟩

@[expose] def rSL : SL(3, K) := ⟨rMat, det_rMat⟩

theorem coe_eSL : ((eSL : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = eMat := rfl

theorem coe_rSL : ((rSL : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = rMat := rfl

theorem eSL_pow_four : (eSL : SL(3, K)) ^ 4 = 1 := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, coe_eSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eMat, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem rSL_mul_self : (rSL : SL(3, K)) * rSL = 1 := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, coe_rSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rMat, Matrix.mul_apply, Fin.sum_univ_succ]

theorem rSL_sq : (rSL : SL(3, K)) ^ 2 = 1 := by rw [sq]; exact rSL_mul_self

theorem rSL_inv : (rSL : SL(3, K))⁻¹ = rSL := inv_eq_of_mul_eq_one_right rSL_mul_self

theorem rSL_eSL : (rSL : SL(3, K)) * eSL * (rSL : SL(3, K))⁻¹ = (eSL : SL(3, K))⁻¹ := by
  rw [rSL_inv]
  apply eq_inv_of_mul_eq_one_left
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, coe_rSL, coe_eSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eMat, rMat, Matrix.mul_apply, Fin.sum_univ_succ]

@[expose] def d8 : Subgroup SL(3, K) := Subgroup.closure {eSL, rSL}

theorem isPGroup_d8 : IsPGroup 2 (d8 : Subgroup SL(3, K)) :=
  isPGroup_closure_dihedral eSL_pow_four rSL_sq rSL_eSL

theorem eSL_mem_d8 : (eSL : SL(3, K)) ∈ d8 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem rSL_mem_d8 : (rSL : SL(3, K)) ∈ d8 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem commute_diag (h2 : (2 : K) ≠ 0) {M : Matrix (Fin 3) (Fin 3) K}
    (he : M * eMat = eMat * M) (hr : M * rMat = rMat * M) :
    M = Matrix.diagonal ![M 0 0, M 0 0, M 2 2] := by
  have hr' := fun i j => congrFun (congrFun hr i) j
  have he' := fun i j => congrFun (congrFun he i) j
  have h01 : M 0 1 = 0 := by
    have := hr' 0 1
    simp [Matrix.mul_apply, Fin.sum_univ_succ, rMat] at this
    exact (mul_eq_zero.1 (by linear_combination -this : (2 : K) * M 0 1 = 0)).resolve_left h2
  have h02 : M 0 2 = 0 := by
    have := hr' 0 2
    simp [Matrix.mul_apply, Fin.sum_univ_succ, rMat] at this
    exact (mul_eq_zero.1 (by linear_combination -this : (2 : K) * M 0 2 = 0)).resolve_left h2
  have h10 : M 1 0 = 0 := by
    have := hr' 1 0
    simp [Matrix.mul_apply, Fin.sum_univ_succ, rMat] at this
    exact (mul_eq_zero.1 (by linear_combination this : (2 : K) * M 1 0 = 0)).resolve_left h2
  have h20 : M 2 0 = 0 := by
    have := hr' 2 0
    simp [Matrix.mul_apply, Fin.sum_univ_succ, rMat] at this
    exact (mul_eq_zero.1 (by linear_combination this : (2 : K) * M 2 0 = 0)).resolve_left h2
  have h12 : M 1 2 = 0 := by
    have := he' 0 2
    simp [Matrix.mul_apply, Fin.sum_univ_succ, eMat] at this
    linear_combination this - h02
  have h21 : M 2 1 = 0 := by
    have := he' 2 0
    simp [Matrix.mul_apply, Fin.sum_univ_succ, eMat] at this
    linear_combination this + h20
  have h11 : M 1 1 = M 0 0 := by
    have := he' 0 1
    simp [Matrix.mul_apply, Fin.sum_univ_succ, eMat] at this
    linear_combination -this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h20, h12, h21, h11]

end Matrices

section LinearCenter

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

@[expose] noncomputable def diagHom : Kˣ →* SL(3, K) where
  toFun a := diagSL (a : K) (a : K) (((a * a)⁻¹ : Kˣ) : K) (by
    rw [← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one])
  map_one' := by
    rw [← diagSL_one (by ring)]
    exact diagSL_congr (by simp) (by simp) (by simp)
  map_mul' a b := by
    rw [diagSL_mul]
    exact diagSL_congr (by simp) (by simp) (by
      rw [← Units.val_mul, mul_mul_mul_comm, mul_inv])

theorem coe_diagHom (a : Kˣ) :
    ((diagHom a : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![(a : K), (a : K), (((a * a)⁻¹ : Kˣ) : K)] := rfl

@[expose] noncomputable def psiLin : Kˣ →* projectiveSL 3 K := (proj 3 K).comp diagHom

variable [Finite K]

theorem lin_center (hK2 : ringChar K ≠ 2) {S : Subgroup (projectiveSL 3 K)} (hS : IsPGroup 2 S)
    (hmax : ∀ T : Subgroup (projectiveSL 3 K), IsPGroup 2 T → S ≤ T → T ≤ S) :
    IsCyclic ↥(S ⊓ Subgroup.centralizer (S : Set (projectiveSL 3 K))) ∧
      ∀ z ∈ S ⊓ Subgroup.centralizer (S : Set (projectiveSL 3 K)), z ^ (Nat.card K - 1) = 1 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  obtain ⟨x, hx⟩ := exists_conj_le_of_isPGroup hS hmax ((isPGroup_d8 (K := K)).map (proj 3 K))
  refine center_cyclic_exp (T := (psiLin (K := K)).range) ?_ ?_ (x := x) ?_
  · exact isCyclic_of_surjective (psiLin (K := K)).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ (Nat.card K - 1) = 1 := by
      rw [← Nat.card_units]; exact pow_card_eq_one'
    rw [this, map_one]
  · intro z hz
    have hc : ∀ e ∈ (d8 : Subgroup SL(3, K)).map (proj 3 K),
        (x * z * x⁻¹) * e = e * (x * z * x⁻¹) := by
      intro e he
      have h1 := hx e he
      have h2' := (Subgroup.mem_centralizer_iff.1 hz.2) _ h1
      calc x * z * x⁻¹ * e = x * (z * (x⁻¹ * e * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * e * x) * z) * x⁻¹ := by rw [← h2']
        _ = e * (x * z * x⁻¹) := by group
    obtain ⟨y, hy⟩ := proj_surjective 3 K (x * z * x⁻¹)
    have hcomm : ∀ g ∈ (d8 : Subgroup SL(3, K)), y * g = g * y := by
      intro g hg
      obtain ⟨j, hj⟩ := isPGroup_d8 (K := K) ⟨g, hg⟩
      have hgj : g ^ 2 ^ j = 1 := congrArg Subtype.val hj
      have hmem : proj 3 K g ∈ (d8 : Subgroup SL(3, K)).map (proj 3 K) := ⟨g, hg, rfl⟩
      have h3 := hc _ hmem
      rw [← hy, ← map_mul, ← map_mul] at h3
      have h4 : proj 3 K (y * g * y⁻¹) = proj 3 K g := by
        rw [map_mul, h3, ← map_mul]
        congr 1
        group
      have h5 : (y * g * y⁻¹) ^ 2 ^ j = 1 := by
        have : y * g * y⁻¹ = MulAut.conj y g := rfl
        rw [this, ← map_pow, hgj, map_one]
      have h6 := eq_of_proj_eq h5 hgj h4
      calc y * g = y * g * y⁻¹ * y := by group
        _ = g * y := by rw [h6]
    have hye : (y : Matrix (Fin 3) (Fin 3) K) * eMat = eMat * (y : Matrix (Fin 3) (Fin 3) K) := by
      have := congrArg (fun m : SL(3, K) => (m : Matrix (Fin 3) (Fin 3) K))
        (hcomm eSL eSL_mem_d8)
      simp only [Matrix.SpecialLinearGroup.coe_mul] at this
      exact this
    have hyr : (y : Matrix (Fin 3) (Fin 3) K) * rMat = rMat * (y : Matrix (Fin 3) (Fin 3) K) := by
      have := congrArg (fun m : SL(3, K) => (m : Matrix (Fin 3) (Fin 3) K))
        (hcomm rSL rSL_mem_d8)
      simp only [Matrix.SpecialLinearGroup.coe_mul] at this
      exact this
    have hdiag := commute_diag h2 hye hyr
    have hdet : (y : Matrix (Fin 3) (Fin 3) K).det = 1 := y.2
    set a : K := (y : Matrix (Fin 3) (Fin 3) K) 0 0 with ha
    set b : K := (y : Matrix (Fin 3) (Fin 3) K) 2 2 with hb
    rw [hdiag, Matrix.det_diagonal] at hdet
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      mul_one] at hdet
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0] at hdet
      simp at hdet
    have hb' : b = (a * a)⁻¹ := by
      field_simp
      linear_combination hdet
    refine ⟨Units.mk0 a ha0, ?_⟩
    rw [← hy]
    show proj 3 K (diagHom (Units.mk0 a ha0)) = proj 3 K y
    congr 1
    apply Subtype.ext
    rw [coe_diagHom]
    conv_rhs => rw [hdiag]
    congr 1
    ext i
    fin_cases i
    · rfl
    · rfl
    · show (((Units.mk0 a ha0 * Units.mk0 a ha0)⁻¹ : Kˣ) : K) = b
      rw [hb', Units.val_inv_eq_inv_val, Units.val_mul]
      rfl

end LinearCenter

section UnitaryCenter

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

local notation "𝟙" => ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

theorem eSL_unitary : ((((eSL : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
    ((eSL : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) = 1 := by
  simp only [coe_eSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eMat, Matrix.mul_apply, Fin.sum_univ_succ]

theorem rSL_unitary : ((((rSL : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
    ((rSL : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) = 1 := by
  simp only [coe_rSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rMat, Matrix.mul_apply, Fin.sum_univ_succ]

theorem toGL_mem_gramSU {g : SL(3, K)}
    (hg : ((g : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (g : Matrix (Fin 3) (Fin 3) K) = 1) :
    Matrix.SpecialLinearGroup.toGL g ∈ gramSU h 𝟙 := by
  rw [mem_gramSU]
  exact ⟨by rw [Units.val_one, Matrix.mul_one]; exact hg, g.2⟩

@[expose] def eU : gramSU h 𝟙 := ⟨Matrix.SpecialLinearGroup.toGL eSL, toGL_mem_gramSU h (eSL_unitary h)⟩

@[expose] def rU : gramSU h 𝟙 := ⟨Matrix.SpecialLinearGroup.toGL rSL, toGL_mem_gramSU h (rSL_unitary h)⟩

theorem eU_pow_four : (eU h) ^ 4 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow]
  change (Matrix.SpecialLinearGroup.toGL (eSL : SL(3, K))) ^ 4 = 1
  rw [← map_pow, eSL_pow_four, map_one]

theorem rU_sq : (rU h) ^ 2 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow]
  change (Matrix.SpecialLinearGroup.toGL (rSL : SL(3, K))) ^ 2 = 1
  rw [← map_pow, rSL_sq, map_one]

theorem rU_eU : (rU h) * (eU h) * (rU h)⁻¹ = (eU h)⁻¹ := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
  change Matrix.SpecialLinearGroup.toGL (rSL : SL(3, K)) * Matrix.SpecialLinearGroup.toGL eSL *
    (Matrix.SpecialLinearGroup.toGL (rSL : SL(3, K)))⁻¹ = (Matrix.SpecialLinearGroup.toGL eSL)⁻¹
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, rSL_eSL]

@[expose] def d8U : Subgroup (gramSU h 𝟙) := Subgroup.closure {eU h, rU h}

theorem isPGroup_d8U : IsPGroup 2 (d8U h) :=
  isPGroup_closure_dihedral (eU_pow_four h) (rU_sq h) (rU_eU h)

theorem eU_mem_d8U : eU h ∈ d8U h := Subgroup.subset_closure (Set.mem_insert _ _)

theorem rU_mem_d8U : rU h ∈ d8U h :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

@[expose] def normOneUnits : Subgroup Kˣ := (powMonoidHom (p ^ f + 1) : Kˣ →* Kˣ).ker

theorem mem_normOneUnits {a : Kˣ} : a ∈ normOneUnits (p := p) (f := f) (K := K) ↔
    a ^ (p ^ f + 1) = 1 := by
  rw [normOneUnits, MonoidHom.mem_ker]
  rfl

theorem bar_mul_self_of_mem {a : Kˣ} (ha : a ∈ normOneUnits (p := p) (f := f) (K := K)) :
    h.bar (a : K) * (a : K) = 1 := by
  rw [mem_normOneUnits] at ha
  rw [h.bar_apply, ← pow_succ]
  have := congrArg (fun u : Kˣ => (u : K)) ha
  simpa using this

theorem diagHom_unitary {a : Kˣ} (ha : a ∈ normOneUnits (p := p) (f := f) (K := K)) :
    (((diagHom a : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
      ((diagHom a : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = 1 := by
  have hb : (a * a)⁻¹ ∈ normOneUnits (p := p) (f := f) (K := K) :=
    Subgroup.inv_mem _ (Subgroup.mul_mem _ ha ha)
  exact diagSL_unitary h (a : K) (a : K) (((a * a)⁻¹ : Kˣ) : K) (by
    rw [← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one])
    (bar_mul_self_of_mem h ha) (bar_mul_self_of_mem h ha) (bar_mul_self_of_mem h hb)

@[expose] noncomputable def diagUHom : (normOneUnits (p := p) (f := f) (K := K)) →* gramSU h 𝟙 where
  toFun a := ⟨Matrix.SpecialLinearGroup.toGL (diagHom (a : Kˣ)), toGL_mem_gramSU h (diagHom_unitary h a.2)⟩
  map_one' := by
    apply Subtype.ext
    change Matrix.SpecialLinearGroup.toGL (diagHom ((1 : normOneUnits (p := p) (f := f) (K := K)) : Kˣ)) = 1
    rw [Subgroup.coe_one, map_one, map_one]
  map_mul' a b := by
    apply Subtype.ext
    change Matrix.SpecialLinearGroup.toGL (diagHom ((a * b : normOneUnits (p := p) (f := f) (K := K)) : Kˣ)) =
      Matrix.SpecialLinearGroup.toGL (diagHom (a : Kˣ)) * Matrix.SpecialLinearGroup.toGL (diagHom (b : Kˣ))
    rw [Subgroup.coe_mul, map_mul, map_mul]

theorem coe_diagUHom (a : normOneUnits (p := p) (f := f) (K := K)) :
    (((diagUHom h a : gramSU h 𝟙) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![((a : Kˣ) : K), ((a : Kˣ) : K), ((((a : Kˣ) * (a : Kˣ))⁻¹ : Kˣ) : K)] := rfl

@[expose] noncomputable def psiUni :
    (normOneUnits (p := p) (f := f) (K := K)) →* primeFormP h 𝟙 :=
  (QuotientGroup.mk' (normOneScalars h (gramSU h 𝟙) 3)).comp (diagUHom h)

theorem uni_center (hp2 : p ≠ 2) {S : Subgroup (primeFormP h 𝟙)} (hS : IsPGroup 2 S)
    (hmax : ∀ T : Subgroup (primeFormP h 𝟙), IsPGroup 2 T → S ≤ T → T ≤ S) :
    IsCyclic ↥(S ⊓ Subgroup.centralizer (S : Set (primeFormP h 𝟙))) ∧
      ∀ z ∈ S ⊓ Subgroup.centralizer (S : Set (primeFormP h 𝟙)), z ^ (p ^ f + 1) = 1 := by
  have : Finite K := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have h2 : (2 : K) ≠ 0 := by
    intro h2
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h2
    have := (CharP.cast_eq_zero_iff K p 2).1 this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this)
  obtain ⟨x, hx⟩ := exists_conj_le_of_isPGroup hS hmax
    ((isPGroup_d8U h).map (QuotientGroup.mk' (normOneScalars h (gramSU h 𝟙) 3)))
  refine center_cyclic_exp (T := (psiUni h).range) ?_ ?_ (x := x) ?_
  · have : IsCyclic (normOneUnits (p := p) (f := f) (K := K)) := inferInstance
    exact isCyclic_of_surjective (psiUni h).rangeRestrict (MonoidHom.rangeRestrict_surjective _)
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ (p ^ f + 1) = 1 := by
      apply Subtype.ext
      exact mem_normOneUnits.1 a.2
    rw [this, map_one]
  · intro z hz
    have hc : ∀ e ∈ (d8U h).map (QuotientGroup.mk' (normOneScalars h (gramSU h 𝟙) 3)),
        (x * z * x⁻¹) * e = e * (x * z * x⁻¹) := by
      intro e he
      have h1 := hx e he
      have h2' := (Subgroup.mem_centralizer_iff.1 hz.2) _ h1
      calc x * z * x⁻¹ * e = x * (z * (x⁻¹ * e * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * e * x) * z) * x⁻¹ := by rw [← h2']
        _ = e * (x * z * x⁻¹) := by group
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (x * z * x⁻¹)
    have hcomm : ∀ g ∈ d8U h, y * g = g * y := by
      intro g hg
      obtain ⟨j, hj⟩ := isPGroup_d8U h ⟨g, hg⟩
      have hgj : g ^ 2 ^ j = 1 := congrArg Subtype.val hj
      have hmem : (g : primeFormP h 𝟙) ∈
          (d8U h).map (QuotientGroup.mk' (normOneScalars h (gramSU h 𝟙) 3)) := ⟨g, hg, rfl⟩
      have h3 := hc _ hmem
      rw [← hy, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at h3
      have h4 : ((y * g * y⁻¹ : gramSU h 𝟙) : primeFormP h 𝟙) = (g : primeFormP h 𝟙) := by
        rw [QuotientGroup.mk_mul, h3, ← QuotientGroup.mk_mul]
        congr 1
        group
      have h5 : (y * g * y⁻¹) ^ 2 ^ j = 1 := by
        have : y * g * y⁻¹ = MulAut.conj y g := rfl
        rw [this, ← map_pow, hgj, map_one]
      have h6 := eq_of_mk_eq_u h h5 hgj h4
      calc y * g = y * g * y⁻¹ * y := by group
        _ = g * y := by rw [h6]
    have hye : (((y : gramSU h 𝟙) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * eMat =
        eMat * (((y : gramSU h 𝟙) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      have := congrArg (fun m : gramSU h 𝟙 => ((m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
        (hcomm (eU h) (eU_mem_d8U h))
      simp only [Subgroup.coe_mul, Units.val_mul] at this
      exact this
    have hyr : (((y : gramSU h 𝟙) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * rMat =
        rMat * (((y : gramSU h 𝟙) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      have := congrArg (fun m : gramSU h 𝟙 => ((m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
        (hcomm (rU h) (rU_mem_d8U h))
      simp only [Subgroup.coe_mul, Units.val_mul] at this
      exact this
    have hdiag := commute_diag h2 hye hyr
    have hdet : (((y : gramSU h 𝟙) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := y.2.2
    have hun := y.2.1
    obtain ⟨Y, hY⟩ : ∃ Y : Matrix (Fin 3) (Fin 3) K,
        Y = (((y : gramSU h 𝟙) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := ⟨_, rfl⟩
    rw [← hY] at hdiag hdet hun
    rw [Units.val_one, Matrix.mul_one] at hun
    set a : K := Y 0 0 with ha
    set b : K := Y 2 2 with hb
    have hun00 := congrFun (congrFun hun 0) 0
    rw [hdiag] at hun00
    simp [Matrix.mul_apply, Fin.sum_univ_succ] at hun00
    rw [hdiag, Matrix.det_diagonal] at hdet
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      mul_one] at hdet
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0] at hdet
      simp at hdet
    have hb' : b = (a * a)⁻¹ := by
      field_simp
      linear_combination hdet
    have hnorm : Units.mk0 a ha0 ∈ normOneUnits (p := p) (f := f) (K := K) := by
      rw [mem_normOneUnits]
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, pow_succ]
      rw [h.bar_apply] at hun00
      exact hun00
    refine ⟨⟨Units.mk0 a ha0, hnorm⟩, ?_⟩
    rw [← hy]
    show (diagUHom h ⟨Units.mk0 a ha0, hnorm⟩ : primeFormP h 𝟙) = (y : primeFormP h 𝟙)
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [coe_diagUHom, ← hY]
    conv_rhs => rw [hdiag]
    congr 1
    ext i
    fin_cases i
    · rfl
    · rfl
    · show (((Units.mk0 a ha0 * Units.mk0 a ha0)⁻¹ : Kˣ) : K) = b
      rw [hb', Units.val_inv_eq_inv_val, Units.val_mul]
      rfl

end UnitaryCenter

end CFSG.GH74.KGroups.L3Eps
