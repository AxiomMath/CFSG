module

public import CFSG.GH74.KGroups.L3EpsInvLin

public section

namespace CFSG.GH74.KGroups.L3Eps

open Matrix Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F]

theorem perfect_eq_of_central {G H : Type*} [Group G] [Group H]
    (hH : Group.IsPerfect H) (f g : H →* G) (a : G)
    (h : ∀ x : H, a * f x * a⁻¹ * (g x)⁻¹ ∈ Subgroup.center G) (x : H) : a * f x * a⁻¹ = g x := by
  let ρ : H →* Subgroup.center G :=
    { toFun := fun x => ⟨a * f x * a⁻¹ * (g x)⁻¹, h x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        have hy := Subgroup.mem_center_iff.1 (h y)
        show a * f (x * y) * a⁻¹ * (g (x * y))⁻¹ =
          (a * f x * a⁻¹ * (g x)⁻¹) * (a * f y * a⁻¹ * (g y)⁻¹)
        rw [map_mul, map_mul]
        calc a * (f x * f y) * a⁻¹ * (g x * g y)⁻¹
            = (a * f x * a⁻¹ * (g x)⁻¹) * (g x * (a * f y * a⁻¹ * (g y)⁻¹) * (g x)⁻¹) := by group
          _ = (a * f x * a⁻¹ * (g x)⁻¹) * (a * f y * a⁻¹ * (g y)⁻¹) := by
            rw [hy (g x)]; group }
  have hker : commutator H ≤ ρ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    have hc : ρ x * ρ y = ρ y * ρ x :=
      Subtype.ext (Subgroup.mem_center_iff.1 (ρ y).2 (ρ x))
    exact commutatorElement_eq_one_iff_mul_comm.2 hc
  rw [Group.isPerfect_def.mp hH] at hker
  have h1 : ρ x = 1 := MonoidHom.mem_ker.1 (hker (Subgroup.mem_top x))
  have h2 : a * f x * a⁻¹ * (g x)⁻¹ = 1 := congrArg Subtype.val h1
  calc a * f x * a⁻¹ = (a * f x * a⁻¹ * (g x)⁻¹) * g x := by group
    _ = g x := by rw [h2, one_mul]

theorem central_of_proj_conj₂ (A : GL (Fin 3) F) (g₁ g₂ : SL(3, F))
    (h : proj 3 F (CatalogueBHigherLinearAction.slConjugation 3 F A g₁) = proj 3 F g₂) :
    A * Matrix.SpecialLinearGroup.toGL g₁ * A⁻¹ * (Matrix.SpecialLinearGroup.toGL g₂)⁻¹ ∈
      Subgroup.center (GL (Fin 3) F) := by
  have hz := scalars_toGL_mem_center (proj_eq_proj_iff.1 h)
  rw [map_mul, map_inv, slConj_toGL] at hz
  set w : GL (Fin 3) F := A * Matrix.SpecialLinearGroup.toGL g₁ * A⁻¹ with hw
  set γ : GL (Fin 3) F := Matrix.SpecialLinearGroup.toGL g₂ with hγ
  have hc : γ * (w⁻¹ * γ) = (w⁻¹ * γ) * γ := Subgroup.mem_center_iff.1 hz γ
  have hwγ : γ * w⁻¹ = w⁻¹ * γ := mul_right_cancel (by rw [mul_assoc, hc, mul_assoc])
  have : w * γ⁻¹ = (w⁻¹ * γ)⁻¹ := by
    have h' := congrArg (fun x => x⁻¹) hwγ
    simpa [_root_.mul_inv_rev] using h'
  rw [this]
  exact Subgroup.inv_mem _ hz


theorem map_bSL (τ : F ≃+* F) (B : SL(2, F)) :
    Matrix.SpecialLinearGroup.map τ.toRingHom (bSL B) =
      bSL (Matrix.SpecialLinearGroup.map τ.toRingHom B) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [coe_bSL]

theorem fieldAut_blockEmb (τ : F ≃+* F) (B : SL(2, F)) :
    fieldAut 3 F τ (blockEmb B) = blockEmb (Matrix.SpecialLinearGroup.map τ.toRingHom B) := by
  rw [blockEmb_apply, fieldAut_proj, map_bSL]
  rfl

@[expose] def tvSL (x : F) : SL(2, F) := ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_tvSL (x : F) : ((tvSL x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, x; 0, 1] := rfl

theorem map_tvSL (τ : F ≃+* F) (x : F) :
    Matrix.SpecialLinearGroup.map τ.toRingHom (tvSL x) = tvSL (τ x) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [coe_tvSL]

theorem tr1_eq_tvSL : (tr1 : SL(2, F)) = tvSL 1 := rfl

theorem map_tr2 (τ : F ≃+* F) :
    Matrix.SpecialLinearGroup.map τ.toRingHom (tr2 : SL(2, F)) = tr2 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [coe_tr2]

theorem map_jSL (τ : F ≃+* F) :
    Matrix.SpecialLinearGroup.map τ.toRingHom (jSL : SL(2, F)) = jSL := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [coe_jSL]


section Tau

theorem commute_bM_of_form {A : Matrix (Fin 3) (Fin 3) F}
    (h01 : A 0 1 = 0) (h10 : A 1 0 = 0) (h02 : A 0 2 = 0) (h12 : A 1 2 = 0) (h20 : A 2 0 = 0)
    (h21 : A 2 1 = 0) (h00 : A 0 0 = A 1 1) (X : Matrix (Fin 2) (Fin 2) F) :
    A * bM X = bM X * A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bM, Matrix.mul_apply, Fin.sum_univ_three, h01, h10, h02, h12, h20, h21, h00] <;> ring

theorem tau_eq_one_of_conj_map [Finite F] (h4 : 4 ≤ Nat.card F) (A₁ : GL (Fin 3) F) (τ : F ≃+* F)
    (hfix : ∀ B : SL(2, F),
      conjAut 3 F A₁ (blockEmb (Matrix.SpecialLinearGroup.map τ.toRingHom B)) = blockEmb B) : τ = 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have h4' : ∃ s : Finset F, s.card = 4 := by
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    exact ⟨t, ht⟩
  have hperf := CFSG.LinearGroups.special_linear_isPerfect (K := F) (n := 2) le_rfl (Or.inr h4')
  let mapτ : SL(2, F) →* SL(2, F) := Matrix.SpecialLinearGroup.map τ.toRingHom
  have key := perfect_eq_of_central hperf (bGL.comp mapτ) bGL A₁ (fun B => by
    have := central_of_proj_conj₂ A₁ (bSL (mapτ B)) (bSL B) (by
      rw [← conjAut_proj]
      exact hfix B)
    exact this)
  have hcomm1 : (A₁ : Matrix (Fin 3) (Fin 3) F) * bM ((tr1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      bM ((tr1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * A₁ := by
    have e := key tr1
    have e' : mapτ tr1 = tr1 := by
      rw [tr1_eq_tvSL]
      show Matrix.SpecialLinearGroup.map τ.toRingHom (tvSL 1) = tvSL 1
      rw [map_tvSL]
      simp
    simp only [MonoidHom.comp_apply, e'] at e
    have e2 := mul_inv_eq_iff_eq_mul.1 e
    have e3 := congrArg (fun u : GL (Fin 3) F => (u : Matrix (Fin 3) (Fin 3) F)) e2
    simpa [Units.val_mul, coe_bGL] using e3
  have hcomm2 : (A₁ : Matrix (Fin 3) (Fin 3) F) * bM ((tr2 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      bM ((tr2 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * A₁ := by
    have e := key tr2
    have e' : mapτ tr2 = tr2 := map_tr2 τ
    simp only [MonoidHom.comp_apply, e'] at e
    have e2 := mul_inv_eq_iff_eq_mul.1 e
    have e3 := congrArg (fun u : GL (Fin 3) F => (u : Matrix (Fin 3) (Fin 3) F)) e2
    simpa [Units.val_mul, coe_bGL] using e3
  obtain ⟨h01, h10, h02, h12, h20, h21, h00⟩ := form_of_commute_bM hcomm1 hcomm2
  ext x
  have e := key (tvSL x)
  simp only [MonoidHom.comp_apply] at e
  have hc : (A₁ : Matrix (Fin 3) (Fin 3) F) * bM ((mapτ (tvSL x) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      bM ((mapτ (tvSL x) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * A₁ :=
    commute_bM_of_form h01 h10 h02 h12 h20 h21 h00 _
  have e1' : A₁ * bGL (mapτ (tvSL x)) * A₁⁻¹ = bGL (mapτ (tvSL x)) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    show (A₁ : Matrix (Fin 3) (Fin 3) F) * bM ((mapτ (tvSL x) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
        ((A₁⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = bM ((mapτ (tvSL x) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
    rw [hc, Matrix.mul_assoc]
    have : (A₁ : Matrix (Fin 3) (Fin 3) F) * ((A₁⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [this, Matrix.mul_one]
  have e1 : bGL (mapτ (tvSL x)) = bGL (tvSL x) := by rw [← e1', e]
  have e2 := congrArg (fun u : GL (Fin 3) F => (u : Matrix (Fin 3) (Fin 3) F) 0 1) e1
  simpa [coe_bGL, bM, mapτ, map_tvSL, coe_tvSL] using e2


open CFSG.LocalAnalysis.ComponentInitial.OddHigherLinear in
theorem lin_cases_of_fixes_block [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    {c : MulAut (projectiveSL 3 F)} (hc2 : c * c = 1)
    (hfix : ∀ s ∈ (blockSub : Subgroup (projectiveSL 3 F)), c s = s) :
    (∃ (A : GL (Fin 3) F) (u : Fˣ), (A : Matrix (Fin 3) (Fin 3) F) * A = (u : F) • 1 ∧
        c = conjAut 3 F A) ∨
      ∃ A : GL (Fin 3) F, (A : Matrix (Fin 3) (Fin 3) F)ᵀ = A ∧ c = conjAut 3 F A * dualAut 3 F := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 3) le_rfl
  obtain ⟨A, τ, ε, hε, hcA⟩ := hform c
  have hτ : τ = 1 := by
    interval_cases ε
    · refine tau_eq_one_of_conj_map h4 A τ (fun B => ?_)
      have := hfix _ (blockEmb_mem B)
      rw [hcA, pow_zero, mul_one, MulAut.mul_apply, fieldAut_blockEmb] at this
      exact this
    · refine tau_eq_one_of_conj_map h4 (A * bGL jSL) τ (fun B => ?_)
      have := hfix _ (blockEmb_mem B)
      have hm : Matrix.SpecialLinearGroup.map τ.toRingHom (jSL * B * jSL⁻¹) =
          jSL * Matrix.SpecialLinearGroup.map τ.toRingHom B * jSL⁻¹ := by
        rw [map_mul, map_mul, map_inv, map_jSL]
      rw [hcA, pow_one, MulAut.mul_apply, dualAut_blockEmb, MulAut.mul_apply, fieldAut_blockEmb, hm] at this
      rw [map_mul, MulAut.mul_apply, conjAut_bGL_blockEmb]
      exact this
  rw [hτ] at hcA
  interval_cases ε
  · left
    rw [pow_zero, mul_one, map_one, mul_one] at hcA
    have hsq : conjAut 3 F A * conjAut 3 F A = 1 := by rw [← hcA]; exact hc2
    have h1 : conjAut 3 F (A * A) * fieldAut 3 F 1 = 1 := by
      rw [map_one, mul_one, map_mul]; exact hsq
    obtain ⟨-, u, hu⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl (A * A) 1 h1
    have hscal : ((GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = (u : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
      rw [smul_one_eq_diagonal]; rfl
    have hAA : (A : Matrix (Fin 3) (Fin 3) F) * A = (u : F) • 1 := by
      rw [← hscal, hu, Units.val_mul]
    exact ⟨A, u, hAA, hcA⟩
  · right
    rw [pow_one, map_one, mul_one] at hcA
    refine ⟨A, ?_, hcA⟩
    have hsq : (conjAut 3 F A * fieldAut 3 F 1 * dualAut 3 F) ^ 2 = 1 := by
      rw [map_one, mul_one, pow_two, ← hcA]; exact hc2
    rcases transpose_eq_or_eq_neg_of_sq le_rfl A hsq with h | h
    · exact h
    · exfalso
      have hdet := congrArg Matrix.det h
      rw [Matrix.det_transpose, Matrix.det_neg] at hdet
      have hd0 : (A : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
        ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit A)).ne_zero
      simp only [Fintype.card_fin] at hdet
      apply hd0
      have h22 : (2 : F) * (A : Matrix (Fin 3) (Fin 3) F).det = 0 := by
        linear_combination hdet
      exact (mul_eq_zero.1 h22).resolve_left h2


open CFSG.LocalAnalysis.ComponentInitial.OddHigherLinear in
theorem aut_fixing_blockSub_all [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    {σ : MulAut (projectiveSL 3 F)} (hσ2 : σ * σ = 1)
    (hfix : ∀ s ∈ (blockSub : Subgroup (projectiveSL 3 F)), σ s = s) :
    σ = 1 ∨ σ = MulAut.conj tInv := by
  rcases lin_cases_of_fixes_block h2 h4 hσ2 hfix with ⟨A, u, hAA, rfl⟩ | ⟨A, hAs, rfl⟩
  · have hcomm := commute_blocks_of_fixes h4 A (fun B => hfix _ (blockEmb_mem B))
    obtain ⟨h01, h10, h02, h12, h20, h21, h00⟩ := form_of_commute_blocks hcomm
    have e00 := congrFun (congrFun hAA 0) 0
    have e22 := congrFun (congrFun hAA 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, h01, h10, h02, h12, h20, h21] at e00 e22
    have hu0 : (u : F) ≠ 0 := u.ne_zero
    have ha0 : (A : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := by
      intro h
      rw [h] at e00
      simp at e00
      exact hu0 e00.symm
    have hm : ((A : Matrix (Fin 3) (Fin 3) F) 2 2 - (A : Matrix (Fin 3) (Fin 3) F) 0 0) *
        ((A : Matrix (Fin 3) (Fin 3) F) 2 2 + (A : Matrix (Fin 3) (Fin 3) F) 0 0) = 0 := by
      linear_combination e22 - e00
    rcases mul_eq_zero.1 hm with hm | hm
    · left
      have hA : A = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 _ ha0) := by
        apply Units.ext
        rw [coe_scalar_GL]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [h01, h10, h02, h12, h20, h21, h00]
        all_goals linear_combination hm + h00
      rw [hA, conjAut_scalar]
    · right
      have hA : A = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (-(A : Matrix (Fin 3) (Fin 3) F) 0 0) (neg_ne_zero.2 ha0)) *
          Matrix.SpecialLinearGroup.toGL dNeg := by
        apply Units.ext
        rw [Units.val_mul, coe_scalar_GL]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [h01, h10, h02, h12, h20, h21, h00, coe_dNeg]
        all_goals first | linear_combination hm + h00 | linear_combination hm - h00
      rw [hA, map_mul, conjAut_scalar, one_mul, conjAut_toGL]
      rfl
  · exfalso
    set A₁ : GL (Fin 3) F := A * bGL jSL with hA₁
    have hfix₁ : ∀ B : SL(2, F), conjAut 3 F A₁ (blockEmb B) = blockEmb B := by
      intro B
      rw [hA₁, map_mul, MulAut.mul_apply, conjAut_bGL_blockEmb, ← dualAut_blockEmb]
      exact hfix _ (blockEmb_mem B)
    have hcomm := commute_blocks_of_fixes h4 A₁ hfix₁
    obtain ⟨h01, h10, h02, h12, h20, h21, h00⟩ := form_of_commute_blocks hcomm
    have hA₁m : (A₁ : Matrix (Fin 3) (Fin 3) F) = (A : Matrix (Fin 3) (Fin 3) F) * bM (jSL : SL(2, F)).1 := by
      rw [hA₁, Units.val_mul]
      rfl
    rw [hA₁m] at h01 h10 h02 h00
    simp [Matrix.mul_apply, Fin.sum_univ_three, bM, coe_jSL] at h01 h10 h02 h00
    have hs01 := congrFun (congrFun hAs 0) 1
    simp only [Matrix.transpose_apply] at hs01
    have hA01 : (A : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := by
      have : (2 : F) * (A : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := by linear_combination -h00 - hs01
      exact (mul_eq_zero.1 this).resolve_left h2
    apply det_ne_zero_GL A
    apply Matrix.det_eq_zero_of_row_eq_zero 0
    intro j
    fin_cases j
    · exact h01
    · exact hA01
    · exact h02

end Tau

structure InvDataB4 (q : ℕ) (K : Type*) [Group K] (t : K) (S : Subgroup K) : Prop where
  card : Nat.card ↥S = q * (q ^ 2 - 1)
  quasisimple : CFSG.IsQuasisimple ↥S
  mem : t ∈ S
  le_centralizer : S ≤ Subgroup.centralizer ({t} : Set K)
  conj_mem : ∀ x ∈ Subgroup.centralizer ({t} : Set K), ∀ s ∈ S, x * s * x⁻¹ ∈ S
  commutator_mem : ∀ x ∈ Subgroup.centralizer ({t} : Set K), ∀ y ∈ Subgroup.centralizer ({t} : Set K),
    ⁅x, y⁆ ∈ S
  involution : ∀ s ∈ S, s * s = 1 → s = 1 ∨ s = t
  center : ∀ s : ↥S, s ∈ Subgroup.center ↥S → (s : K) = 1 ∨ (s : K) = t
  aut_fixing : ∀ σ : MulAut K, σ * σ = 1 → (∀ s ∈ S, σ s = s) → σ = 1 ∨ σ = MulAut.conj t

theorem InvData.toB4 {q : ℕ} {K : Type*} [Group K] {t : K} {S : Subgroup K} (h : InvData q K t S) :
    InvDataB4 q K t S :=
  ⟨h.card, h.quasisimple, h.mem, h.le_centralizer, h.conj_mem, h.commutator_mem, h.involution, h.center,
    h.aut_fixing⟩

section Transport

variable {K : Type*} [Group K]

theorem mem_map_symm_iff {X : Type*} [Group X] (e : K ≃* X) (S : Subgroup X) (x : K) :
    x ∈ Subgroup.map (e.symm : X →* K) S ↔ e x ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨e x, h, by simp⟩

theorem invDataB4_of_equiv [Finite F] {p f : ℕ} (hFc : Nat.card F = p ^ f)
    (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) (e : K ≃* projectiveSL 3 F) {t : K} (ht : e t = tInv) :
    InvDataB4 (p ^ f) K t (Subgroup.map (e.symm : projectiveSL 3 F →* K) blockSub) := by
  have hF2 : ringChar F ≠ 2 := fun h => h2 (by
    have : CharP F 2 := h ▸ ringChar.charP F
    exact CharTwo.two_eq_zero)
  have hcen : ∀ x : K, x ∈ Subgroup.centralizer ({t} : Set K) ↔
      e x ∈ Subgroup.centralizer ({tInv} : Set (projectiveSL 3 F)) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← ht, ← map_mul,
      ← map_mul]
    exact ⟨fun h => by rw [h], fun h => e.injective h⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e1 : ↥(Subgroup.map (e.symm : projectiveSL 3 F →* K) blockSub) ≃* ↥(blockSub : Subgroup (projectiveSL 3 F)) :=
      (MulEquiv.subgroupMap e.symm blockSub).symm
    have e2 : SL(2, F) ≃* ↥(blockSub : Subgroup (projectiveSL 3 F)) :=
      MonoidHom.ofInjective (blockEmb_injective (F := F))
    rw [Nat.card_congr e1.toEquiv, ← Nat.card_congr e2.toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hFc]
  · exact LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupMap e.symm blockSub)
      (isQuasisimple_blockSub h4)
  · rw [mem_map_symm_iff, ht]
    exact tInv_mem_blockSub
  · intro s hs
    rw [mem_map_symm_iff] at hs
    rw [hcen]
    exact blockSub_le_centralizer hs
  · intro x hx s hs
    rw [hcen] at hx
    rw [mem_map_symm_iff] at hs ⊢
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_blockSub h2 hx hs
  · intro x hx y hy
    rw [hcen] at hx hy
    rw [mem_map_symm_iff, map_commutatorElement]
    exact commutator_mem_blockSub h2 hx hy
  · intro s hs hs2
    rw [mem_map_symm_iff] at hs
    have h1 : e s * e s = 1 := by rw [← map_mul, hs2, map_one]
    rcases blockSub_involution hF2 hs h1 with h | h
    · left
      exact e.injective (h.trans (map_one e).symm)
    · right
      exact e.injective (h.trans ht.symm)
  · intro s hs
    have hs' : (⟨e s, (mem_map_symm_iff e blockSub s).1 s.2⟩ : ↥(blockSub : Subgroup (projectiveSL 3 F))) ∈
        Subgroup.center ↥(blockSub : Subgroup (projectiveSL 3 F)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hy : e.symm y ∈ Subgroup.map (e.symm : projectiveSL 3 F →* K) blockSub := by
        rw [mem_map_symm_iff, MulEquiv.apply_symm_apply]
        exact y.2
      have := Subgroup.mem_center_iff.1 hs ⟨e.symm y, hy⟩
      apply Subtype.ext
      have h' := congrArg Subtype.val this
      simp only [Subgroup.coe_mul] at h'
      show (y : projectiveSL 3 F) * e s = e s * (y : projectiveSL 3 F)
      have := congrArg e h'
      simpa [map_mul] using this
    rcases blockSub_center hs' with h | h
    · left
      exact e.injective (h.trans (map_one e).symm)
    · right
      exact e.injective (h.trans ht.symm)
  · intro σ hσ2 hfix
    have hfix' : ∀ s ∈ (blockSub : Subgroup (projectiveSL 3 F)), conjAutEquiv e σ s = s := by
      intro s hs
      obtain ⟨x, rfl⟩ := e.surjective s
      rw [conjAutEquiv_apply]
      congr 1
      exact hfix x ((mem_map_symm_iff e blockSub x).2 hs)
    have hσ2' : conjAutEquiv e σ * conjAutEquiv e σ = 1 := by
      rw [← conjAutEquiv_mul, hσ2, conjAutEquiv_one]
    rcases aut_fixing_blockSub_all h2 h4 hσ2' hfix' with h | h
    · left
      exact (conjAutEquiv_eq_one_iff e σ).1 h
    · right
      have : conjAutEquiv e σ = conjAutEquiv e (MulAut.conj t) := by rw [h, conjAutEquiv_conj, ht]
      ext x
      have := congrArg (fun τ : MulAut (projectiveSL 3 F) => τ (e x)) this
      simp only [conjAutEquiv_apply] at this
      exact e.injective this

end Transport


end CFSG.GH74.KGroups.L3Eps
