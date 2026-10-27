module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3LinComp
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81.LinA3

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
open scoped commutatorElement

theorem eq_of_perfect_of_mul_inv_mem {G : Type*} [Group G] (L C : Subgroup G)
    (hL : commutator ↥L = ⊤) (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (φ : G →* G)
    (hδ : ∀ l ∈ L, φ l * l⁻¹ ∈ C) (hcomm : ∀ l ∈ L, ∀ c ∈ C, φ l * c = c * φ l) :
    ∀ l ∈ L, φ l = l := by
  haveI : IsMulCommutative ↥C := ⟨⟨fun a b => Subtype.ext (hC a a.2 b b.2)⟩⟩
  let δ : ↥L →* ↥C :=
    { toFun := fun l => ⟨φ l * (l : G)⁻¹, hδ l l.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun l m => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev]
        have h := hcomm l l.2 _ (hδ m m.2)
        calc φ l * φ m * ((m : G)⁻¹ * (l : G)⁻¹)
            = φ l * (φ m * (m : G)⁻¹) * (l : G)⁻¹ := by group
          _ = φ m * (m : G)⁻¹ * φ l * (l : G)⁻¹ := by rw [h]
          _ = φ m * (m : G)⁻¹ * (φ l * (l : G)⁻¹) := by group
          _ = φ l * (l : G)⁻¹ * (φ m * (m : G)⁻¹) := hC _ (hδ m m.2) _ (hδ l l.2) }
  have hker : commutator ↥L ≤ δ.ker := Abelianization.commutator_subset_ker δ
  intro l hl
  have h1 : (⟨l, hl⟩ : L) ∈ δ.ker := hker (hL ▸ Subgroup.mem_top _)
  rw [MonoidHom.mem_ker] at h1
  have h2 := congrArg Subtype.val h1
  simp only [δ, MonoidHom.coe_mk, OneHom.coe_mk, OneMemClass.coe_one] at h2
  exact mul_inv_eq_one.1 h2

variable {F : Type} [Field F] {p : ℕ} {μ : F}

private theorem trace_transvection_mul (a : F) :
    ((Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 4) ≠ 2) a *
      Matrix.SpecialLinearGroup.transvection (by decide : (2 : Fin 4) ≠ 1) 1 :
        SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).trace = 4 + a := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.single_mul_single_same, Matrix.trace_add, Matrix.trace_one, Fintype.card_fin,
    Matrix.trace_single_eq_of_ne _ _ _ (by decide : (1 : Fin 4) ≠ 2),
    Matrix.trace_single_eq_of_ne _ _ _ (by decide : (2 : Fin 4) ≠ 1),
    Matrix.trace_single_eq_same]
  push_cast
  ring

private theorem trace_map_ringEquiv (σ : F ≃+* F) (M : Matrix (Fin 4) (Fin 4) F) :
    (M.map σ).trace = σ M.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

private theorem entries_of_commute_transvection {A : Matrix (Fin 4) (Fin 4) F} {i j : Fin 4}
    (h : A * (1 + Matrix.single i j 1) = (1 + Matrix.single i j 1) * A) (k l : Fin 4) :
    A k i * (if j = l then 1 else 0) = (if k = i then 1 else 0) * A j l := by
  have hS : A * Matrix.single i j 1 = Matrix.single i j 1 * A := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
    exact add_left_cancel h
  have h1 := congrFun (congrFun hS k) l
  have e1 : (A * Matrix.single i j (1 : F)) k l = A k i * (if j = l then 1 else 0) := by
    by_cases hjl : j = l
    · subst hjl
      rw [mul_single_apply_same, if_pos rfl]
    · rw [mul_single_apply_of_ne (hbj := Ne.symm hjl), if_neg hjl, mul_zero]
  have e2 : (Matrix.single i j (1 : F) * A) k l = (if k = i then 1 else 0) * A j l := by
    by_cases hki : k = i
    · subst hki
      rw [single_mul_apply_same, if_pos rfl]
    · rw [single_mul_apply_of_ne (h := hki), if_neg hki, zero_mul]
  exact e1.symm.trans (h1.trans e2)

private theorem conjAut_fieldAut_mul {n : ℕ} (A B : GL (Fin n) F) (σ τ : F ≃+* F) :
    conjAut n F A * fieldAut n F σ * (conjAut n F B * fieldAut n F τ) =
      conjAut n F (A * GeneralLinearGroup.map (σ : F →+* F) B) * fieldAut n F (σ * τ) := by
  obtain ⟨-, -, hfc, -⟩ := (standard_automorphism_transport (n := n) (K := F))
  have h3 : fieldAut n F σ * conjAut n F B =
      conjAut n F (GeneralLinearGroup.map (σ : F →+* F) B) * fieldAut n F σ := by
    have := hfc σ B
    rwa [mul_inv_eq_iff_eq_mul] at this
  calc conjAut n F A * fieldAut n F σ * (conjAut n F B * fieldAut n F τ)
      = conjAut n F A * (fieldAut n F σ * conjAut n F B) * fieldAut n F τ := by
        simp only [mul_assoc]
    _ = conjAut n F A * (conjAut n F (GeneralLinearGroup.map (σ : F →+* F) B) *
          fieldAut n F σ) * fieldAut n F τ := by rw [h3]
    _ = (conjAut n F A * conjAut n F (GeneralLinearGroup.map (σ : F →+* F) B)) *
          (fieldAut n F σ * fieldAut n F τ) := by simp only [mul_assoc]
    _ = _ := by rw [map_mul, map_mul]

theorem exists_eq_conjAut_mul_fieldAut_of_odd_pow [Finite F] {n : ℕ} (hn : 3 ≤ n)
    {α : MulAut (projectiveSL n F)} {m : ℕ} (hm : Odd m) (hα : α ^ m = 1) :
    ∃ (A : GL (Fin n) F) (σ : F ≃+* F), α = conjAut n F A * fieldAut n F σ := by
  set S : Set (MulAut (projectiveSL n F)) :=
    {β | ∃ (A : GL (Fin n) F) (σ : F ≃+* F), β = conjAut n F A * fieldAut n F σ} with hS
  have hSmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := by
    rintro _ ⟨A, σ, rfl⟩ _ ⟨B, τ, rfl⟩
    exact ⟨_, _, conjAut_fieldAut_mul A B σ τ⟩
  have hSpow : ∀ x ∈ S, ∀ k : ℕ, x ^ (k + 1) ∈ S := by
    intro x hx k
    induction k with
    | zero => rwa [zero_add, pow_one]
    | succ k ih => rw [pow_succ]; exact hSmul _ ih _ hx
  obtain ⟨-, hform⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation (K := F) hn
  obtain ⟨A, σ, ε, hε, hαeq⟩ := hform α
  obtain ⟨-, -, -, hδδ, hδc, hδf, -⟩ := (standard_automorphism_transport (n := n) (K := F))
  have hsq : α ^ 2 ∈ S := by
    rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
    · rw [pow_zero, mul_one] at hαeq
      rw [hαeq, pow_two]
      exact hSmul _ ⟨A, σ, rfl⟩ _ ⟨A, σ, rfl⟩
    · rw [pow_one] at hαeq
      have hconj : dualAut n F * (conjAut n F A * fieldAut n F σ) * dualAut n F =
          conjAut n F (GeneralLinearGroup.inverseTranspose A) * fieldAut n F σ := by
        calc dualAut n F * (conjAut n F A * fieldAut n F σ) * dualAut n F
            = dualAut n F * conjAut n F A * (dualAut n F * dualAut n F) * fieldAut n F σ *
                dualAut n F := by rw [hδδ]; simp only [mul_assoc, mul_one]
          _ = (dualAut n F * conjAut n F A * dualAut n F) *
                (dualAut n F * fieldAut n F σ * dualAut n F) := by simp only [mul_assoc]
          _ = _ := by rw [hδc A, hδf σ]
      have : α ^ 2 = (conjAut n F A * fieldAut n F σ) *
          (dualAut n F * (conjAut n F A * fieldAut n F σ) * dualAut n F) := by
        rw [hαeq, pow_two]
        simp only [mul_assoc]
      rw [this, hconj]
      exact hSmul _ ⟨A, σ, rfl⟩ _ ⟨_, σ, rfl⟩
  obtain ⟨j, hj⟩ := hm
  have : α = (α ^ 2) ^ (j + 1) := by
    rw [← pow_mul, show 2 * (j + 1) = m + 1 by omega, pow_succ, hα, one_mul]
  rw [this]
  exact hSpow _ hsq j

section Main

variable [Finite F] (hp : p.Prime) (hp2 : p ≠ 2) (hμ : IsPrimitiveRoot μ p) (hF : 4 ≤ Nat.card F)
include hp hp2 hμ hF

private theorem core_le_center :
    GLAPPrimeCore p ↥(JH F) ≤ Subgroup.center ↥(JH F) := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple
    (isQuasisimple_JH hp hp2 hμ hF) (GLAPPrimeCore.normal p _) fun htop => ?_
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥(JH F))) := CFSG.pPrimeCore_coprime_card
  rw [htop, Subgroup.card_top] at hcop
  have hdvd : p ∣ Nat.card ↥(JH F) :=
    (dvd_card_JH hp hp2 hμ hF).trans (Subgroup.card_quotient_dvd_card _)
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop hdvd

private theorem fixes_JH {α : MulAut (projectiveSL 4 F)}
    (hcent : ∀ j ∈ JH F, α j * j⁻¹ ∈ GLAPPrimeCoreOf p (JH F)) : ∀ j ∈ JH F, α j = j := by
  set C : Subgroup (projectiveSL 4 F) := (Subgroup.center ↥(JH F)).map (JH F).subtype with hC
  have hCJ : ∀ c ∈ C, c ∈ JH F ∧ ∀ j ∈ JH F, c * j = j * c := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨c.2, fun j hj => ?_⟩
    have := Subgroup.mem_center_iff.1 hc ⟨j, hj⟩
    exact (congrArg Subtype.val this).symm
  have hδ : ∀ j ∈ JH F, α j * j⁻¹ ∈ C := by
    intro j hj
    have h := hcent j hj
    change α j * j⁻¹ ∈ (GLAPPrimeCore p ↥(JH F)).map (JH F).subtype at h
    exact Subgroup.map_mono (core_le_center hp hp2 hμ hF) h
  refine eq_of_perfect_of_mul_inv_mem (JH F) C (isQuasisimple_JH hp hp2 hμ hF).1
    (fun x hx y hy => (hCJ x hx).2 y (hCJ y hy).1) α.toMonoidHom hδ fun l hl c hc => ?_
  have hαl : α l ∈ JH F := by
    have h1 := (hCJ _ (hδ l hl)).1
    have h2 : α l = α l * l⁻¹ * l := by group
    rw [h2]
    exact mul_mem h1 hl
  exact ((hCJ c hc).2 _ hαl).symm

theorem aut_eq_conj_ySL_zpow (α : MulAut (projectiveSL 4 F)) (hα : α ^ p = 1)
    (hcent : ∀ j ∈ JH F, α j * j⁻¹ ∈ GLAPPrimeCoreOf p (JH F)) :
    ∃ k : ℤ, α = MulAut.conj (proj 4 F (ySL (ne_zero_of_root hp hp2 hμ)) ^ k) := by
  classical
  have hμ0 := ne_zero_of_root hp hp2 hμ
  have hfix := fixes_JH hp hp2 hμ hF hcent
  obtain ⟨A, σ, hασ⟩ := exists_eq_conjAut_mul_fieldAut_of_odd_pow (n := 4) (by norm_num)
    (hp.odd_of_ne_two hp2) hα
  subst hασ
  set β : SpecialLinearGroup (Fin 4) F →* SpecialLinearGroup (Fin 4) F :=
    (slConjugation 4 F A).toMonoidHom.comp (SpecialLinearGroup.map (σ : F →+* F)) with hβ
  have hβproj : ∀ g, proj 4 F (β g) = (conjAut 4 F A * fieldAut 4 F σ) (proj 4 F g) := by
    intro g
    rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj]
    rfl
  have hβfix : ∀ g ∈ coordBlockSL F blockJ, β g = g := by
    refine eq_of_perfect_of_mul_inv_mem (coordBlockSL F blockJ) (scalars 4 F)
      (isQuasisimple_coordBlockSL_blockJ hp hp2 hμ hF).1
      (fun x hx y _ => (Subgroup.mem_center_iff.1 (scalars_le_center 4 F hx) y).symm) β
      (fun g hg => ?_) (fun g _ c hc => Subgroup.mem_center_iff.1 (scalars_le_center 4 F hc) _)
    rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, hβproj,
      hfix _ (Subgroup.mem_map_of_mem _ hg), mul_inv_cancel]
  have hmat : ∀ g ∈ coordBlockSL F blockJ, (A : Matrix (Fin 4) (Fin 4) F) *
      ((g : Matrix (Fin 4) (Fin 4) F).map σ) * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (g : Matrix (Fin 4) (Fin 4) F) := by
    intro g hg
    have h := congrArg (fun x : SpecialLinearGroup (Fin 4) F => (x : Matrix (Fin 4) (Fin 4) F))
      (hβfix g hg)
    simp only [hβ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      coe_slConjugation, Matrix.SpecialLinearGroup.map_apply_coe] at h
    exact h
  have hσ : σ = 1 := by
    have htr : ∀ g ∈ coordBlockSL F blockJ,
        σ (g : Matrix (Fin 4) (Fin 4) F).trace = (g : Matrix (Fin 4) (Fin 4) F).trace := by
      intro g hg
      have hcyc : ((A : Matrix (Fin 4) (Fin 4) F) * ((g : Matrix (Fin 4) (Fin 4) F).map σ) *
          ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)).trace =
            ((g : Matrix (Fin 4) (Fin 4) F).map σ).trace := by
        rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mul]
      calc σ (g : Matrix (Fin 4) (Fin 4) F).trace
          = ((g : Matrix (Fin 4) (Fin 4) F).map σ).trace := (trace_map_ringEquiv σ _).symm
        _ = ((A : Matrix (Fin 4) (Fin 4) F) * ((g : Matrix (Fin 4) (Fin 4) F).map σ) *
              ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)).trace := hcyc.symm
        _ = (g : Matrix (Fin 4) (Fin 4) F).trace := by rw [hmat g hg]
    ext a
    have hg : Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 4) ≠ 2) a *
        Matrix.SpecialLinearGroup.transvection (by decide : (2 : Fin 4) ≠ 1) 1 ∈
          coordBlockSL F blockJ :=
      mul_mem (transvection_mem_coordBlockSL (by decide) (by decide) _ a)
        (transvection_mem_coordBlockSL (by decide) (by decide) _ 1)
    have h := htr _ hg
    rw [trace_transvection_mul, map_add] at h
    have h4 : σ 4 = 4 := map_ofNat σ 4
    rw [h4] at h
    simpa using add_left_cancel h
  subst hσ
  have hcomm : ∀ g ∈ coordBlockSL F blockJ, (A : Matrix (Fin 4) (Fin 4) F) *
      (g : Matrix (Fin 4) (Fin 4) F) =
        (g : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) := by
    intro g hg
    have h := hmat g hg
    have hσ1 : (g : Matrix (Fin 4) (Fin 4) F).map (1 : F ≃+* F) = g := by
      ext i j
      rfl
    rw [hσ1] at h
    calc (A : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F)
        = (A : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
            (((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
              (A : Matrix (Fin 4) (Fin 4) F)) := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      _ = (g : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) := by
          rw [← Matrix.mul_assoc, h]
  have hT : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → (hij : i ≠ j) → ∀ k l,
      (A : Matrix (Fin 4) (Fin 4) F) k i * (if j = l then 1 else 0) =
        (if k = i then 1 else 0) * (A : Matrix (Fin 4) (Fin 4) F) j l := by
    intro i j hi hj hij k l
    refine entries_of_commute_transvection ?_ k l
    have := hcomm _ (transvection_mem_coordBlockSL (mem_blockJ.2 hi) (mem_blockJ.2 hj) hij 1)
    rwa [Matrix.SpecialLinearGroup.transvection_coe] at this
  have hcol : ∀ i : Fin 4, i ≠ 0 → ∀ k, k ≠ i → (A : Matrix (Fin 4) (Fin 4) F) k i = 0 := by
    intro i hi k hki
    obtain ⟨j, hj, hji⟩ : ∃ j : Fin 4, j ≠ 0 ∧ j ≠ i := by
      fin_cases i
      · exact absurd rfl hi
      · exact ⟨2, by decide, by decide⟩
      · exact ⟨1, by decide, by decide⟩
      · exact ⟨1, by decide, by decide⟩
    have := hT i j hi hj (Ne.symm hji) k j
    simpa [hki] using this
  have hrow : ∀ j : Fin 4, j ≠ 0 → ∀ l, l ≠ j → (A : Matrix (Fin 4) (Fin 4) F) j l = 0 := by
    intro j hj l hlj
    obtain ⟨i, hi, hij⟩ : ∃ i : Fin 4, i ≠ 0 ∧ i ≠ j := by
      fin_cases j
      · exact absurd rfl hj
      · exact ⟨2, by decide, by decide⟩
      · exact ⟨1, by decide, by decide⟩
      · exact ⟨1, by decide, by decide⟩
    have := hT i j hi hj hij i l
    simpa [Ne.symm hlj] using this.symm
  have hdg : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → i ≠ j →
      (A : Matrix (Fin 4) (Fin 4) F) i i = (A : Matrix (Fin 4) (Fin 4) F) j j := by
    intro i j hi hj hij
    have := hT i j hi hj hij i j
    simpa using this
  set a := (A : Matrix (Fin 4) (Fin 4) F) 0 0 with ha
  set b := (A : Matrix (Fin 4) (Fin 4) F) 1 1 with hb
  have hAd : (A : Matrix (Fin 4) (Fin 4) F) = diagonal ![a, b, b, b] := by
    ext k l
    by_cases hkl : k = l
    · subst hkl
      fin_cases k
      · rfl
      · rfl
      · exact hdg 2 1 (by decide) (by decide) (by decide)
      · exact hdg 3 1 (by decide) (by decide) (by decide)
    · rw [diagonal_apply_ne _ hkl]
      by_cases hl : l = 0
      · subst hl
        exact hrow k hkl 0 (Ne.symm hkl)
      · exact hcol l hl k hkl
  have hdet : a * b ^ 3 ≠ 0 := by
    have h1 : (A : Matrix (Fin 4) (Fin 4) F).det ≠ 0 := by
      have := A.isUnit.map Matrix.detMonoidHom
      exact this.ne_zero
    rw [hAd, det_diagonal, Fin.prod_univ_four] at h1
    simpa [pow_succ, mul_assoc] using h1
  have hb0 : b ≠ 0 := fun h0 => hdet (by rw [h0]; ring)
  have ha0 : a ≠ 0 := fun h0 => hdet (by rw [h0]; ring)
  have hAp : conjAut 4 F (A ^ p) * fieldAut 4 F 1 = 1 := by
    rw [map_one, mul_one, map_pow]
    simpa [map_one, mul_one] using hα
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) (A ^ p) 1 hAp
  have hApd : ((A ^ p : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      diagonal ![a ^ p, b ^ p, b ^ p, b ^ p] := by
    rw [Units.val_pow_eq_pow_val, hAd, diagonal_pow]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hab : a ^ p = b ^ p := by
    have hcm := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F)) hc
    have h0 := congrFun (congrFun hcm 0) 0
    have h1 := congrFun (congrFun hcm 1) 1
    simp only [hApd, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq] at h0 h1
    have h0' : (c : F) = a ^ p := h0
    have h1' : (c : F) = b ^ p := h1
    rw [← h0', ← h1']
  have hν : (a / b) ^ p = 1 := by rw [div_pow, hab, div_self (pow_ne_zero _ hb0)]
  have hprim : IsPrimitiveRoot (μ⁻¹ ^ 4) p := by
    have hcop : Nat.Coprime 4 p := by
      have h2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
      have : Nat.Coprime (2 ^ 2) p := Nat.Coprime.pow_left 2 h2
      simpa using this
    exact hμ.inv.pow_of_coprime 4 hcop
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hν
  have hc' : b * μ⁻¹ ^ i ≠ 0 := mul_ne_zero hb0 (pow_ne_zero _ (inv_ne_zero hμ0))
  have hAy : A = GeneralLinearGroup.scalar (Fin 4) (Units.mk0 _ hc') *
      SpecialLinearGroup.toGL (ySL hμ0 ^ i) := by
    apply Units.ext
    rw [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.coe_pow, GeneralLinearGroup.coe_scalar, hAd]
    simp only [ySL, coe_diagSL, diagonal_pow, Units.val_mk0, scalar_apply, diagonal_mul_diagonal]
    congr 1
    funext k
    have hai : a = b * (μ⁻¹ ^ 4) ^ i := by
      rw [hi]
      field_simp
    fin_cases k
    · show a = b * μ⁻¹ ^ i * ((μ ^ 3)⁻¹) ^ i
      rw [hai, ← pow_mul, ← inv_pow, ← pow_mul, mul_assoc, ← pow_add]
      ring_nf
    all_goals
      show b = b * μ⁻¹ ^ i * μ ^ i
      rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hμ0, one_pow, mul_one]
  refine ⟨i, ?_⟩
  rw [map_one, mul_one, hAy, map_mul, conjAut_scalar, one_mul, conjAut_toGL, map_pow,
    zpow_natCast]

end Main

end CFSG.LocalAnalysis.GLTheoremA.H81.LinA3
