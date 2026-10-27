module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
public import CFSG.LieType.SeitzGeneration.SingerTorusLinear
public import CFSG.LieType.SeitzGeneration.HeisTorusGen

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Twist

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
open scoped MatrixGroups commutatorElement

section Monomial

variable {K : Type} [Field K] {G : Type*} [Group G]

theorem monomial_closure_split {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (ρ : SL(5, K) →* G) (y : G)
    (du : Fin 5 → Kˣ)
    (hconj : ∀ A : SL(5, K), y * ρ A * y⁻¹ = ρ (rotSL * conjDiagn du A * rotSL⁻¹))
    {c : K} (hc : c ^ 5 = ∏ i, (du i : K)) (H : Subgroup G)
    (hdiag : ∀ A : SL(5, K), (∃ t : Fin 5 → K, (A : Matrix (Fin 5) (Fin 5) K) = diagonal t) →
      ρ A ∈ H)
    (hcomm : ∀ A : SL(5, K), y * ρ A = ρ A * y → ρ A ∈ H) :
    ∀ A : SL(5, K), ρ A ∈ H := by
  classical
  set σ : Equiv.Perm (Fin 5) := finRotate 5 with hσdef
  set d : Fin 5 → K := fun i => (du i : K) with hd
  have hdne : ∀ i, d i ≠ 0 := fun i => (du i).ne_zero
  have hc' : c ^ 5 = d 0 * d 1 * d 2 * d 3 * d 4 := by
    rw [hc, Fin.prod_univ_five]
  have hcne : c ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num)] at hc'
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (hdne 0) (hdne 1)) (hdne 2))
      (hdne 3)) (hdne 4) hc'.symm
  set f : Fin 5 → K := ![1, c / d 0, c ^ 2 / (d 0 * d 1), c ^ 3 / (d 0 * d 1 * d 2),
    c ^ 4 / (d 0 * d 1 * d 2 * d 3)] with hf
  have hfne : ∀ i, f i ≠ 0 := by
    intro i
    fin_cases i <;> simp [hf, hcne, hdne]
  have hfσ : ∀ i, f (σ i) * d i = c * f i := by
    have h0 := hdne 0
    have h1 := hdne 1
    have h2 := hdne 2
    have h3 := hdne 3
    have h4 := hdne 4
    intro i
    fin_cases i
    · change f 1 * d 0 = c * f 0
      have e1 : f 1 = c / d 0 := rfl
      have e0 : f 0 = 1 := rfl
      rw [e1, e0]
      field_simp
    · change f 2 * d 1 = c * f 1
      have e2 : f 2 = c ^ 2 / (d 0 * d 1) := rfl
      have e1 : f 1 = c / d 0 := rfl
      rw [e2, e1]
      field_simp
    · change f 3 * d 2 = c * f 2
      have e3 : f 3 = c ^ 3 / (d 0 * d 1 * d 2) := rfl
      have e2 : f 2 = c ^ 2 / (d 0 * d 1) := rfl
      rw [e3, e2]
      field_simp
    · change f 4 * d 3 = c * f 3
      have e4 : f 4 = c ^ 4 / (d 0 * d 1 * d 2 * d 3) := rfl
      have e3 : f 3 = c ^ 3 / (d 0 * d 1 * d 2) := rfl
      rw [e4, e3]
      field_simp
    · change f 0 * d 4 = c * f 4
      have e4 : f 4 = c ^ 4 / (d 0 * d 1 * d 2 * d 3) := rfl
      have e0 : f 0 = 1 := rfl
      rw [e4, e0]
      field_simp
      rw [hc']
      ring
  set fu : Fin 5 → Kˣ := fun i => Units.mk0 (f i) (hfne i) with hfu
  have hnorm : ∀ A : SL(5, K),
      conjDiagn fu (rotSL * conjDiagn du A * rotSL⁻¹) = rotSL * conjDiagn fu A * rotSL⁻¹ := by
    intro A
    have h : (conjDiagnHom fu).comp
          ((MulAut.conj (rotSL : SL(5, K))).toMonoidHom.comp (conjDiagnHom du)) =
        ((MulAut.conj (rotSL : SL(5, K))).toMonoidHom.comp (conjDiagnHom fu)) := by
      refine MonoidHom.eq_of_eqOn_dense
        (CFSG.LinearGroups.special_linear_elementary_generation (n := 5) (K := K)) ?_
      rintro _ ⟨i, j, hij, t, rfl⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        conjDiagnHom_apply]
      rw [conjDiagn_transvection, rotSL_conj_tv, conjDiagn_transvection, conjDiagn_transvection,
        rotSL_conj_tv]
      congr 1
      simp only [hfu, Units.val_mk0, Units.val_inv_eq_inv_val]
      have hi := hfσ i
      have hj := hfσ j
      have hdj : d j ≠ 0 := hdne j
      calc f (σ i) * ((du i : K) * t * (du j : K)⁻¹) * (f (σ j))⁻¹ =
            (f (σ i) * d i) * t * (f (σ j) * d j)⁻¹ := by
              simp only [hd]
              rw [_root_.mul_inv]
              ring
        _ = (c * f i) * t * (c * f j)⁻¹ := by rw [hi, hj]
        _ = f i * t * (f j)⁻¹ := by
          rw [_root_.mul_inv]
          field_simp
    have := DFunLike.congr_fun h A
    simpa [MulAut.conj_apply, conjDiagnHom_apply] using this
  set H₀ : Subgroup SL(5, K) := (H.comap ρ).comap (conjDiagnHom fu⁻¹) with hH₀
  have hH₀diag : ∀ B : SL(5, K),
      (∃ t : Fin 5 → K, (B : Matrix (Fin 5) (Fin 5) K) = diagonal t) → B ∈ H₀ := by
    rintro B ⟨t, ht⟩
    simp only [hH₀, Subgroup.mem_comap, conjDiagnHom_apply]
    rw [conjDiagn_of_diagonal _ ht]
    exact hdiag B ⟨t, ht⟩
  have hH₀four : ∀ B : SL(5, K),
      (∃ t : Fin 5 → K, (B : Matrix (Fin 5) (Fin 5) K) * heisFourierMat ζ =
        heisFourierMat ζ * diagonal t) → B ∈ H₀ := by
    rintro B ⟨t, ht⟩
    simp only [hH₀, Subgroup.mem_comap, conjDiagnHom_apply]
    set A := conjDiagn fu⁻¹ B with hA
    apply hcomm A
    have hBQ := fourier_comm_rotSL hζ ht
    have hfA : conjDiagn fu A = B := conjDiagn_conjDiagn_inv fu B
    have hφA : rotSL * conjDiagn du A * rotSL⁻¹ = A := by
      have h1 := hnorm A
      rw [hfA] at h1
      have h2 : rotSL * B * rotSL⁻¹ = B := by
        rw [← hBQ, mul_assoc, mul_inv_cancel, mul_one]
      rw [h2] at h1
      have h3 := congrArg (conjDiagn fu⁻¹) h1
      rw [conjDiagn_inv_conjDiagn] at h3
      rw [h3]
    have := hconj A
    rw [hφA] at this
    calc y * ρ A = y * ρ A * y⁻¹ * y := by group
      _ = ρ A * y := by rw [this]
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have htop : H₀ = ⊤ := torusFourierGen_of_prime (p := 5) (F := K)
    (by norm_num) ζ hζ H₀ hH₀diag hH₀four
  intro A
  have hmem : conjDiagn fu A ∈ H₀ := by rw [htop]; exact Subgroup.mem_top _
  simp only [hH₀, Subgroup.mem_comap, conjDiagnHom_apply] at hmem
  rwa [conjDiagn_inv_conjDiagn] at hmem

theorem rotSL_conjDiagn_eq_of_comm (d : Fin 5 → Kˣ) {A : SL(5, K)}
    (hA : (A : Matrix (Fin 5) (Fin 5) K) *
        ((((finRotate 5)⁻¹ : Equiv.Perm (Fin 5)).permMatrix K) * diagonal fun i => (d i : K)) =
      ((((finRotate 5)⁻¹ : Equiv.Perm (Fin 5)).permMatrix K) * diagonal fun i => (d i : K)) *
        (A : Matrix (Fin 5) (Fin 5) K)) :
    rotSL * conjDiagn d A * rotSL⁻¹ = A := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  set P : Matrix (Fin 5) (Fin 5) K := ((finRotate 5)⁻¹ : Equiv.Perm (Fin 5)).permMatrix K with hP
  set D : Matrix (Fin 5) (Fin 5) K := diagonal fun i => (d i : K) with hD
  set D' : Matrix (Fin 5) (Fin 5) K := diagonal fun i => (((d i)⁻¹ : Kˣ) : K) with hD'
  have hDD' : D * D' = 1 := by
    rw [hD, hD', diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hc : ((conjDiagn d A : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) =
      D * (A : Matrix (Fin 5) (Fin 5) K) * D' := by
    rw [coe_conjDiagn]
    rfl
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_rotSL, hc]
  calc P * (D * (A : Matrix (Fin 5) (Fin 5) K) * D') =
        P * D * (A : Matrix (Fin 5) (Fin 5) K) * D' := by simp only [Matrix.mul_assoc]
    _ = (A : Matrix (Fin 5) (Fin 5) K) * (P * D) * D' := by rw [← hA]
    _ = (A : Matrix (Fin 5) (Fin 5) K) * P * (D * D') := by simp only [Matrix.mul_assoc]
    _ = (A : Matrix (Fin 5) (Fin 5) K) * P := by rw [hDD', Matrix.mul_one]

theorem monomial_closure_singer [Finite K] (h5 : 5 ∣ Nat.card K - 1) (ρ : SL(5, K) →* G)
    (y : G) (du : Fin 5 → Kˣ)
    (hconj : ∀ A : SL(5, K), y * ρ A * y⁻¹ = ρ (rotSL * conjDiagn du A * rotSL⁻¹))
    (hns : ¬ ∃ μ : Kˣ, μ ^ 5 = ∏ i, du i) (H : Subgroup G)
    (hdiag : ∀ A : SL(5, K), (∃ t : Fin 5 → K, (A : Matrix (Fin 5) (Fin 5) K) = diagonal t) →
      ρ A ∈ H)
    (hcomm : ∀ A : SL(5, K), y * ρ A = ρ A * y → ρ A ∈ H) :
    ∀ A : SL(5, K), ρ A ∈ H := by
  classical
  set σ : Equiv.Perm (Fin 5) := finRotate 5 with hσdef
  set cu : Kˣ := ∏ i, du i with hcu
  set d : Fin 5 → K := fun i => (du i : K) with hd
  have hdne : ∀ i, d i ≠ 0 := fun i => (du i).ne_zero
  have hc' : (cu : K) = d 0 * d 1 * d 2 * d 3 * d 4 := by
    rw [hcu, Units.coe_prod, Fin.prod_univ_five]
  set f : Fin 5 → K := ![1, (d 0)⁻¹, (d 0 * d 1)⁻¹, (d 0 * d 1 * d 2)⁻¹,
    (d 0 * d 1 * d 2 * d 3)⁻¹] with hf
  have hfne : ∀ i, f i ≠ 0 := by
    intro i
    fin_cases i <;> simp [hf, hdne]
  set c4 : Fin 5 → K := ![1, 1, 1, 1, (cu : K)] with hc4
  have hc4ne : ∀ i, c4 i ≠ 0 := by
    intro i
    fin_cases i <;> simp [hc4, cu.ne_zero]
  have hfσ : ∀ i, f (σ i) * d i = c4 i * f i := by
    have h0 := hdne 0
    have h1 := hdne 1
    have h2 := hdne 2
    have h3 := hdne 3
    have h4 := hdne 4
    intro i
    fin_cases i
    · change f 1 * d 0 = c4 0 * f 0
      have e1 : f 1 = (d 0)⁻¹ := rfl
      have e0 : f 0 = 1 := rfl
      have c0 : c4 0 = 1 := rfl
      rw [e1, e0, c0]
      field_simp
    · change f 2 * d 1 = c4 1 * f 1
      have e2 : f 2 = (d 0 * d 1)⁻¹ := rfl
      have e1 : f 1 = (d 0)⁻¹ := rfl
      have c1 : c4 1 = 1 := rfl
      rw [e2, e1, c1]
      field_simp
    · change f 3 * d 2 = c4 2 * f 2
      have e3 : f 3 = (d 0 * d 1 * d 2)⁻¹ := rfl
      have e2 : f 2 = (d 0 * d 1)⁻¹ := rfl
      have c2 : c4 2 = 1 := rfl
      rw [e3, e2, c2]
      field_simp
    · change f 4 * d 3 = c4 3 * f 3
      have e4 : f 4 = (d 0 * d 1 * d 2 * d 3)⁻¹ := rfl
      have e3 : f 3 = (d 0 * d 1 * d 2)⁻¹ := rfl
      have c3 : c4 3 = 1 := rfl
      rw [e4, e3, c3]
      field_simp
    · change f 0 * d 4 = c4 4 * f 4
      have e4 : f 4 = (d 0 * d 1 * d 2 * d 3)⁻¹ := rfl
      have e0 : f 0 = 1 := rfl
      have c4v : c4 4 = (cu : K) := rfl
      rw [e4, e0, c4v, hc']
      field_simp
  set fu : Fin 5 → Kˣ := fun i => Units.mk0 (f i) (hfne i) with hfu
  set c4u : Fin 5 → Kˣ := fun i => Units.mk0 (c4 i) (hc4ne i) with hc4u
  have hnorm : ∀ A : SL(5, K),
      conjDiagn fu (rotSL * conjDiagn du A * rotSL⁻¹) =
        rotSL * conjDiagn c4u (conjDiagn fu A) * rotSL⁻¹ := by
    intro A
    have h : (conjDiagnHom fu).comp
          ((MulAut.conj (rotSL : SL(5, K))).toMonoidHom.comp (conjDiagnHom du)) =
        ((MulAut.conj (rotSL : SL(5, K))).toMonoidHom.comp
          ((conjDiagnHom c4u).comp (conjDiagnHom fu))) := by
      refine MonoidHom.eq_of_eqOn_dense
        (CFSG.LinearGroups.special_linear_elementary_generation (n := 5) (K := K)) ?_
      rintro _ ⟨i, j, hij, t, rfl⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        conjDiagnHom_apply]
      rw [conjDiagn_transvection, rotSL_conj_tv, conjDiagn_transvection, conjDiagn_transvection,
        conjDiagn_transvection, rotSL_conj_tv]
      congr 1
      simp only [hfu, hc4u, Units.val_mk0, Units.val_inv_eq_inv_val]
      have hi := hfσ i
      have hj := hfσ j
      have hdj : d j ≠ 0 := hdne j
      have hfj : f j ≠ 0 := hfne j
      have hcj : c4 j ≠ 0 := hc4ne j
      calc f (σ i) * ((du i : K) * t * (du j : K)⁻¹) * (f (σ j))⁻¹ =
            (f (σ i) * d i) * t * (f (σ j) * d j)⁻¹ := by
              simp only [hd]
              rw [_root_.mul_inv]
              ring
        _ = (c4 i * f i) * t * (c4 j * f j)⁻¹ := by rw [hi, hj]
        _ = c4 i * (f i * t * (f j)⁻¹) * (c4 j)⁻¹ := by
          rw [_root_.mul_inv]
          ring
    have := DFunLike.congr_fun h A
    simpa [MulAut.conj_apply, conjDiagnHom_apply] using this
  have hcomp : companionMat 5 (cu : K) =
      ((finRotate 5)⁻¹ : Equiv.Perm (Fin 5)).permMatrix K * diagonal fun i => (c4u i : K) := by
    rw [companionMat]
    congr 1
    congr 1
    funext j
    simp only [hc4u, Units.val_mk0]
    fin_cases j <;> rfl
  set H₀ : Subgroup SL(5, K) := (H.comap ρ).comap (conjDiagnHom fu⁻¹) with hH₀
  have hH₀diag : ∀ B : SL(5, K),
      (∃ t : Fin 5 → K, (B : Matrix (Fin 5) (Fin 5) K) = diagonal t) → B ∈ H₀ := by
    rintro B ⟨t, ht⟩
    simp only [hH₀, Subgroup.mem_comap, conjDiagnHom_apply]
    rw [conjDiagn_of_diagonal _ ht]
    exact hdiag B ⟨t, ht⟩
  have hH₀comm : ∀ B : SL(5, K),
      (B : Matrix (Fin 5) (Fin 5) K) * companionMat 5 (cu : K) =
        companionMat 5 (cu : K) * (B : Matrix (Fin 5) (Fin 5) K) → B ∈ H₀ := by
    intro B hB
    simp only [hH₀, Subgroup.mem_comap, conjDiagnHom_apply]
    set A := conjDiagn fu⁻¹ B with hA
    apply hcomm A
    have hfA : conjDiagn fu A = B := conjDiagn_conjDiagn_inv fu B
    have hBC : rotSL * conjDiagn c4u B * rotSL⁻¹ = B := by
      rw [hcomp] at hB
      exact rotSL_conjDiagn_eq_of_comm c4u hB
    have hφA : rotSL * conjDiagn du A * rotSL⁻¹ = A := by
      have h1 := hnorm A
      rw [hfA, hBC] at h1
      have h3 := congrArg (conjDiagn fu⁻¹) h1
      rw [conjDiagn_inv_conjDiagn] at h3
      rw [h3]
    have := hconj A
    rw [hφA] at this
    calc y * ρ A = y * ρ A * y⁻¹ * y := by group
      _ = ρ A * y := by rw [this]
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have htop : H₀ = ⊤ :=
    singerTorusGen_of_prime (p := 5) (F := K) (by norm_num) h5 cu hns H₀ hH₀diag hH₀comm
  intro A
  have hmem : conjDiagn fu A ∈ H₀ := by rw [htop]; exact Subgroup.mem_top _
  simp only [hH₀, Subgroup.mem_comap, conjDiagnHom_apply] at hmem
  rwa [conjDiagn_inv_conjDiagn] at hmem

theorem monomial_closure [Finite K] (h5 : 5 ∣ Nat.card K - 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ 5) (ρ : SL(5, K) →* G) (y : G) (du : Fin 5 → Kˣ)
    (hconj : ∀ A : SL(5, K), y * ρ A * y⁻¹ = ρ (rotSL * conjDiagn du A * rotSL⁻¹))
    (H : Subgroup G)
    (hdiag : ∀ A : SL(5, K), (∃ t : Fin 5 → K, (A : Matrix (Fin 5) (Fin 5) K) = diagonal t) →
      ρ A ∈ H)
    (hcomm : ∀ A : SL(5, K), y * ρ A = ρ A * y → ρ A ∈ H) :
    ∀ A : SL(5, K), ρ A ∈ H := by
  by_cases hs : ∃ μ : Kˣ, μ ^ 5 = ∏ i, du i
  · obtain ⟨μ, hμ⟩ := hs
    refine monomial_closure_split hζ ρ y du hconj (c := (μ : K)) ?_ H hdiag hcomm
    rw [← Units.val_pow_eq_pow_val, hμ, Units.coe_prod]
  · exact monomial_closure_singer h5 ρ y du hconj hs H hdiag hcomm

end Monomial

section MonomialConj

variable {K : Type} [Field K]

set_option linter.unusedSectionVars false

theorem exists_monomial_conj (ρ : SL(5, K) →* ModGL Tag.E8 K) (hρi : Function.Injective ρ)
    (r : Fin 5 → Fin 5 → Fin Tag.E8.rank → ℤ)
    (hr : ∀ i j, i ≠ j → IsRoot Tag.E8 (r i j))
    (hρ : ∀ i j (hij : i ≠ j), ∃ ε : Kˣ, ∀ t : K,
      ρ (SpecialLinearGroup.transvection hij t) = pinnedX Tag.E8 K (r i j) ((ε : K) * t))
    {y : ModGL Tag.E8 K} {w : WeylGroup Tag.E8} (hy : SignConj y w)
    (hw : ∀ i j, i ≠ j → w • r i j = r (finRotate 5 i) (finRotate 5 j)) :
    ∃ du : Fin 5 → Kˣ, ∀ A : SL(5, K), y * ρ A * y⁻¹ = ρ (rotSL * conjDiagn du A * rotSL⁻¹) := by
  classical
  set σ : Equiv.Perm (Fin 5) := finRotate 5 with hσdef
  have hσne : ∀ {i j : Fin 5}, i ≠ j → σ i ≠ σ j := fun h => σ.injective.ne h
  choose! ε hε using hρ
  have hη : ∀ i j, i ≠ j → ∃ η : ℤ, (η = 1 ∨ η = -1) ∧ ∀ c : K,
      y * pinnedX Tag.E8 K (r i j) c * y⁻¹ = pinnedX Tag.E8 K (r (σ i) (σ j)) ((η : K) * c) := by
    intro i j hij
    obtain ⟨η, hη1, hηc⟩ := hy (r i j) (hr i j hij)
    exact ⟨η, hη1, fun c => by rw [hηc, hw i j hij]⟩
  choose! η hη1 hη using hη
  have hηsq : ∀ i j, i ≠ j → (η i j : K) * (η i j : K) = 1 := by
    intro i j hij
    rcases hη1 i j hij with h | h <;> rw [h] <;> simp
  have hηne : ∀ i j, i ≠ j → (η i j : K) ≠ 0 := by
    intro i j hij h
    have := hηsq i j hij
    rw [h, zero_mul] at this
    exact zero_ne_one this
  set lam : Fin 5 → Fin 5 → K :=
    fun i j => (η i j : K) * (ε i j : K) * ((ε (σ i) (σ j) : K))⁻¹ with hlam
  have hlamne : ∀ i j, i ≠ j → lam i j ≠ 0 := fun i j hij => by
    simp only [hlam]
    exact mul_ne_zero (mul_ne_zero (hηne i j hij) (ε i j).ne_zero)
      (inv_ne_zero (ε (σ i) (σ j)).ne_zero)
  have key : ∀ i j (hij : i ≠ j) (t : K),
      y * ρ (SpecialLinearGroup.transvection hij t) * y⁻¹ =
        ρ (SpecialLinearGroup.transvection (hσne hij) (lam i j * t)) := by
    intro i j hij t
    rw [hε i j hij t, hη i j hij, hε (σ i) (σ j) (hσne hij)]
    congr 1
    simp only [hlam]
    field_simp
  have hlam3 : ∀ i a j, i ≠ a → a ≠ j → i ≠ j → lam i j = lam i a * lam a j := by
    intro i a j hia haj hij
    have h1 := tv_commutator hia haj hij (1 : K) 1
    have h2 : y * ρ (SpecialLinearGroup.transvection hij (1 * 1)) * y⁻¹ =
        ⁅y * ρ (SpecialLinearGroup.transvection hia 1) * y⁻¹,
          y * ρ (SpecialLinearGroup.transvection haj 1) * y⁻¹⁆ := by
      rw [← h1, map_commutatorElement]
      simp only [commutatorElement_def]
      group
    rw [key, key, key, ← map_commutatorElement,
      tv_commutator (hσne hia) (hσne haj) (hσne hij)] at h2
    have h3 := tv_inj (hσne hij) (hρi h2)
    simp only [mul_one] at h3
    exact h3
  set d : Fin 5 → K := fun i => if i = 0 then 1 else lam i 0 with hd
  have hdlam := exact_cocycle lam hlamne hlam3
  have hdne : ∀ i, d i ≠ 0 := fun i => by
    simp only [hd]
    split_ifs with h
    · exact one_ne_zero
    · exact hlamne i 0 h
  set du : Fin 5 → Kˣ := fun i => Units.mk0 (d i) (hdne i) with hdu
  refine ⟨du, fun A => ?_⟩
  have h : (MulAut.conj y).toMonoidHom.comp ρ =
      ρ.comp ((MulAut.conj (rotSL : SL(5, K))).toMonoidHom.comp (conjDiagnHom du)) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LinearGroups.special_linear_elementary_generation (n := 5) (K := K)) ?_
    rintro _ ⟨i, j, hij, t, rfl⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      conjDiagnHom_apply]
    rw [key i j hij t, conjDiagn_transvection, rotSL_conj_tv]
    congr 2
    have h1 : lam i j * d j = d i := by
      simp only [hd]
      exact hdlam i j hij
    simp only [hdu, Units.val_mk0, Units.val_inv_eq_inv_val]
    have hdj : d j ≠ 0 := hdne j
    have h2 : lam i j = d i * (d j)⁻¹ := by
      rw [← h1]
      field_simp
    rw [h2]
    ring
  have := DFunLike.congr_fun h A
  simpa [MulAut.conj_apply, conjDiagnHom_apply] using this

end MonomialConj

section CubeDefs

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K] {ζ : K}

set_option linter.unusedSectionVars false

variable (K) in
@[expose] noncomputable def griessYT (a : Fin Tag.E8.rank → Kˣ) : ModGL Tag.E8 K :=
  griessY K * rootDiagUnit Tag.E8 a

@[expose] noncomputable def griessCubeT (hζ : IsPrimitiveRoot ζ 5) (a : Fin Tag.E8.rank → Kˣ) :
    Subgroup (adjointGroup Tag.E8 K) :=
  (Subgroup.closure ({griessZ hζ, griessX hζ, griessYT K a} : Set (ModGL Tag.E8 K))).comap
    (adjointGroup Tag.E8 K).subtype

end CubeDefs

section Data

open CFSG.RankThree.Lattice

theorem griessW_geom_data :
    ∑ k ∈ Finset.range 5, wordMat Tag.E8 griessWWord ^ k = 0 := by
  decide +kernel

end Data

section Cube

open CFSG.RankThree.E6 (chainRoot)
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.RankThree.Lattice
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b (weylAct weylAct_mul rootChar_weylAct
  eq_of_rootChar_eq)

variable {K : Type} [Field K]

set_option linter.unusedSectionVars false

theorem rootDiagUnit_comm (a b : Fin Tag.E8.rank → Kˣ) :
    rootDiagUnit Tag.E8 a * rootDiagUnit Tag.E8 b = rootDiagUnit Tag.E8 b * rootDiagUnit Tag.E8 a := by
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

theorem griessYT_mono (a : Fin Tag.E8.rank → Kˣ) : griessYT K a ∈ monomialSubgroup Tag.E8 K :=
  mul_mem griessY_mono (Subgroup.mem_sup_left (rootDiagUnit_mem_torus_E8 a))

theorem griessYT_mem (a : Fin Tag.E8.rank → Kˣ) : griessYT K a ∈ adjointGroup Tag.E8 K :=
  mul_mem griessY_mem (torusGroup_le_adjointGroup_E8' (rootDiagUnit_mem_torus_E8 a))

theorem weylQuotient_griessYT (a : Fin Tag.E8.rank → Kˣ) :
    weylQuotientHom Tag.E8 K ⟨griessYT K a, griessYT_mono a⟩ = griessW := by
  apply weylQuotientHom_eq
  have h1 := mapsRootLines_pow (griessY0_maps (K := K)) 6
  rw [griessW_pow_six] at h1
  have h2 := h1.mul (mapsRootLines_of_mem_torusGroup (rootDiagUnit_mem_torus_E8 (K := K) a))
  rw [mul_one] at h2
  exact h2

variable {ζ : K}

theorem griessYT_comm_Z (hζ : IsPrimitiveRoot ζ 5) (a : Fin Tag.E8.rank → Kˣ) :
    griessYT K a * griessZ hζ = griessZ hζ * griessYT K a := by
  rw [griessYT, mul_assoc, griessZ, rootDiagUnit_comm a, ← mul_assoc, ← griessZ,
    griessY_comm_Z hζ, mul_assoc]

theorem griessYT_comm_X (hζ : IsPrimitiveRoot ζ 5) (a : Fin Tag.E8.rank → Kˣ) :
    griessYT K a * griessX hζ = griessX hζ * griessYT K a := by
  rw [griessYT, mul_assoc, griessX, rootDiagUnit_comm a, ← mul_assoc, ← griessX,
    griessY_comm_X hζ, mul_assoc]

theorem griessY_pow_conj_rootDiagUnit (n : ℕ) (a : Fin Tag.E8.rank → Kˣ) :
    griessY K ^ n * rootDiagUnit Tag.E8 a * (griessY K ^ n)⁻¹ =
      rootDiagUnit Tag.E8 (weylAct (griessW ^ n) a) := by
  have h := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.monomial_conj_rootDiagUnit
    (⟨griessY K, griessY_mono⟩ ^ n : monomialSubgroup Tag.E8 K) a
  rw [map_pow, weylQuotient_griessY] at h
  simpa using h

theorem griessYT_pow (a : Fin Tag.E8.rank → Kˣ) : ∀ n : ℕ,
    griessYT K a ^ n = rootDiagUnit Tag.E8
      (∏ k ∈ Finset.range n, weylAct (griessW ^ (k + 1)) a) * griessY K ^ n
  | 0 => by simp [rootDiagUnit_one]
  | n + 1 => by
    rw [pow_succ, griessYT_pow a n, Finset.prod_range_succ, rootDiagUnit_mul, griessYT,
      ← griessY_pow_conj_rootDiagUnit (n + 1) a, pow_succ]
    group

theorem prod_weylAct_griessW (a : Fin Tag.E8.rank → Kˣ) :
    ∏ k ∈ Finset.range 5, weylAct (griessW ^ (k + 1)) a = 1 := by
  apply eq_of_rootChar_eq
  intro v
  have hhom : ∀ b : Fin Tag.E8.rank → Kˣ,
      rootChar b v = CFSG.LieType.SeitzGeneration.ExcHighThree.rootCharHom v b := fun _ => rfl
  rw [hhom, map_prod]
  simp only [← hhom, rootChar_weylAct]
  rw [← rootChar_sum]
  have hinv : ∀ k ∈ Finset.range 5, (griessW ^ (k + 1))⁻¹ • v = griessW ^ (5 - 1 - k) • v := by
    intro k hk
    have hk5 : k < 5 := Finset.mem_range.1 hk
    have h : (griessW ^ (k + 1))⁻¹ = griessW ^ (5 - 1 - k) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, show k + 1 + (5 - 1 - k) = 5 by omega,
        griessW_pow_five]
    rw [h]
  rw [Finset.sum_congr rfl hinv, Finset.sum_range_reflect (fun k => griessW ^ k • v) 5]
  have hsum : ∑ k ∈ Finset.range 5, griessW ^ k • v = 0 := by
    simp only [griessW_pow_smul]
    rw [← Matrix.sum_mulVec, griessW_geom_data, Matrix.zero_mulVec]
  rw [hsum, rootChar_zero]
  simp [rootChar]

theorem griessYT_pow_five (a : Fin Tag.E8.rank → Kˣ) : griessYT K a ^ 5 = 1 := by
  rw [griessYT_pow a 5, griessY_pow_five, mul_one, prod_weylAct_griessW, rootDiagUnit_one]

theorem griessT_exp_injective (hζ : IsPrimitiveRoot ζ 5) (a : Fin Tag.E8.rank → Kˣ) :
    Function.Injective fun v : Fin 5 × Fin 5 × Fin 5 =>
      griessZ hζ ^ (v.1 : ℕ) * griessX hζ ^ (v.2.1 : ℕ) * griessYT K a ^ (v.2.2 : ℕ) := by
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
  simp only at h
  have hzm : griessZ hζ ∈ monomialSubgroup Tag.E8 K := Subgroup.mem_sup_left (griessZ_torus hζ)
  have hxm : griessX hζ ∈ monomialSubgroup Tag.E8 K := Subgroup.mem_sup_left (griessX_torus hζ)
  have hwz : weylQuotientHom Tag.E8 K ⟨griessZ hζ, hzm⟩ = 1 :=
    weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup (griessZ_torus hζ))
  have hwx : weylQuotientHom Tag.E8 K ⟨griessX hζ, hxm⟩ = 1 :=
    weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup (griessX_torus hζ))
  have hel : ∀ (p q s : ℕ), (⟨griessZ hζ, hzm⟩ : monomialSubgroup Tag.E8 K) ^ p *
      ⟨griessX hζ, hxm⟩ ^ q * ⟨griessYT K a, griessYT_mono a⟩ ^ s =
      ⟨griessZ hζ ^ p * griessX hζ ^ q * griessYT K a ^ s, by
        exact mul_mem (mul_mem (pow_mem hzm _) (pow_mem hxm _)) (pow_mem (griessYT_mono a) _)⟩ := by
    intro p q s
    rfl
  have hw := congrArg (weylQuotientHom Tag.E8 K)
    (show (⟨griessZ hζ ^ (i : ℕ) * griessX hζ ^ (j : ℕ) * griessYT K a ^ (k : ℕ), by
        exact mul_mem (mul_mem (pow_mem hzm _) (pow_mem hxm _)) (pow_mem (griessYT_mono a) _)⟩ :
          monomialSubgroup Tag.E8 K) =
        ⟨griessZ hζ ^ (i' : ℕ) * griessX hζ ^ (j' : ℕ) * griessYT K a ^ (k' : ℕ), by
        exact mul_mem (mul_mem (pow_mem hzm _) (pow_mem hxm _)) (pow_mem (griessYT_mono a) _)⟩
      from Subtype.ext h)
  rw [← hel, ← hel, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow,
    map_pow, map_pow, hwz, hwx, weylQuotient_griessYT] at hw
  simp only [one_pow, one_mul] at hw
  have hk : k = k' := by
    have := (pow_inj_mod (x := griessW) (n := (k : ℕ)) (m := (k' : ℕ))).1 hw
    rw [orderOf_griessW, Nat.mod_eq_of_lt k.isLt, Nat.mod_eq_of_lt k'.isLt] at this
    exact Fin.ext this
  subst hk
  have h2 : griessZ hζ ^ (i : ℕ) * griessX hζ ^ (j : ℕ) =
      griessZ hζ ^ (i' : ℕ) * griessX hζ ^ (j' : ℕ) := mul_right_cancel h
  rw [griessZ, griessX, SeitzExcOpenRest4Griess.rootDiagUnit_pow,
    SeitzExcOpenRest4Griess.rootDiagUnit_pow, SeitzExcOpenRest4Griess.rootDiagUnit_pow,
    SeitzExcOpenRest4Griess.rootDiagUnit_pow, ← rootDiagUnit_mul, ← rootDiagUnit_mul] at h2
  have h3 := rootDiagUnit_inj h2
  have hu := griessU_prim hζ
  have h4 : griessU hζ ^ (i : ℕ) = griessU hζ ^ (i' : ℕ) := by
    have := congrFun h3 4
    simp [czVec, cxVec] at this
    exact this
  have h5 : griessU hζ ^ (j : ℕ) = griessU hζ ^ (j' : ℕ) := by
    have := congrFun h3 5
    simp [czVec, cxVec] at this
    exact this
  have hi : i = i' := by
    have := (pow_inj_mod (x := griessU hζ) (n := (i : ℕ)) (m := (i' : ℕ))).1 h4
    rw [← hu.eq_orderOf, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt i'.isLt] at this
    exact Fin.ext this
  have hj : j = j' := by
    have := (pow_inj_mod (x := griessU hζ) (n := (j : ℕ)) (m := (j' : ℕ))).1 h5
    rw [← hu.eq_orderOf, Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt j'.isLt] at this
    exact Fin.ext this
  rw [hi, hj]

variable (K) in
@[expose] noncomputable def griessYTA (a : Fin Tag.E8.rank → Kˣ) : adjointGroup Tag.E8 K :=
  ⟨griessYT K a, griessYT_mem a⟩

theorem griessCubeT_eq (hζ : IsPrimitiveRoot ζ 5) (a : Fin Tag.E8.rank → Kˣ) :
    griessCubeT hζ a = Subgroup.closure {griessZA hζ, griessXA hζ, griessYTA K a} := by
  have h : (Subgroup.closure ({griessZA hζ, griessXA hζ, griessYTA K a} :
      Set (adjointGroup Tag.E8 K))).map (adjointGroup Tag.E8 K).subtype =
      Subgroup.closure {griessZ hζ, griessX hζ, griessYT K a} := by
    rw [MonoidHom.map_closure]
    congr 1
    simp only [Set.image_insert_eq, Set.image_singleton, Subgroup.coe_subtype]
    rfl
  rw [griessCubeT, ← h,
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]

theorem griessZA_comm_YTA (hζ : IsPrimitiveRoot ζ 5) (a : Fin Tag.E8.rank → Kˣ) :
    Commute (griessZA hζ) (griessYTA K a) :=
  Subtype.ext (griessYT_comm_Z hζ a).symm

theorem griessXA_comm_YTA (hζ : IsPrimitiveRoot ζ 5) (a : Fin Tag.E8.rank → Kˣ) :
    Commute (griessXA hζ) (griessYTA K a) :=
  Subtype.ext (griessYT_comm_X hζ a).symm

theorem griessYTA_pow (a : Fin Tag.E8.rank → Kˣ) : griessYTA K a ^ 5 = 1 :=
  Subtype.ext (by
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact griessYT_pow_five a)

theorem griessTA_exp_injective (hζ : IsPrimitiveRoot ζ 5) (a : Fin Tag.E8.rank → Kˣ) :
    Function.Injective fun v : Fin 5 × Fin 5 × Fin 5 =>
      griessZA hζ ^ (v.1 : ℕ) * griessXA hζ ^ (v.2.1 : ℕ) * griessYTA K a ^ (v.2.2 : ℕ) := by
  intro v w h
  apply griessT_exp_injective (K := K) hζ a
  have h' := congrArg Subtype.val h
  simp only [Subgroup.coe_mul, SubgroupClass.coe_pow] at h'
  exact h'

theorem griessCubeT_card (hζ : IsPrimitiveRoot ζ 5) (a : Fin Tag.E8.rank → Kˣ) :
    Nat.card (griessCubeT hζ a) = 5 ^ 3 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [griessCubeT_eq]
  exact closure_triple_facts (griessZA_comm_XA hζ) (griessZA_comm_YTA hζ a)
    (griessXA_comm_YTA hζ a) (griessZA_pow hζ) (griessXA_pow hζ) (griessYTA_pow a)
    (griessTA_exp_injective hζ a)

theorem griessT_hyperplanes (hζ : IsPrimitiveRoot ζ 5) (a : Fin Tag.E8.rank → Kˣ) :
    (Subgroup.closure ({griessZA hζ, griessXA hζ} : Set (adjointGroup Tag.E8 K)) ≤
        griessCubeT hζ a ∧
      (Subgroup.closure ({griessZA hζ, griessXA hζ} : Set (adjointGroup Tag.E8 K))).relIndex
        (griessCubeT hζ a) = 5) ∧
    (Subgroup.closure ({griessZA hζ, griessYTA K a} : Set (adjointGroup Tag.E8 K)) ≤
        griessCubeT hζ a ∧
      (Subgroup.closure ({griessZA hζ, griessYTA K a} : Set (adjointGroup Tag.E8 K))).relIndex
        (griessCubeT hζ a) = 5) ∧
    (Subgroup.closure ({griessXA hζ, griessYTA K a} : Set (adjointGroup Tag.E8 K)) ≤
        griessCubeT hζ a ∧
      (Subgroup.closure ({griessXA hζ, griessYTA K a} : Set (adjointGroup Tag.E8 K))).relIndex
        (griessCubeT hζ a) = 5) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hE := griessCubeT_card hζ a
  rw [griessCubeT_eq] at hE ⊢
  obtain ⟨i1, i2, i3⟩ := pair_injective_of_triple (by norm_num : 0 < 5)
    (griessTA_exp_injective hζ a)
  have l1 : Subgroup.closure ({griessZA hζ, griessXA hζ} : Set (adjointGroup Tag.E8 K)) ≤
      Subgroup.closure {griessZA hζ, griessXA hζ, griessYTA K a} :=
    Subgroup.closure_mono (by intro t ht; rcases ht with rfl | rfl <;> simp)
  have l2 : Subgroup.closure ({griessZA hζ, griessYTA K a} : Set (adjointGroup Tag.E8 K)) ≤
      Subgroup.closure {griessZA hζ, griessXA hζ, griessYTA K a} :=
    Subgroup.closure_mono (by intro t ht; rcases ht with rfl | rfl <;> simp)
  have l3 : Subgroup.closure ({griessXA hζ, griessYTA K a} : Set (adjointGroup Tag.E8 K)) ≤
      Subgroup.closure {griessZA hζ, griessXA hζ, griessYTA K a} :=
    Subgroup.closure_mono (by intro t ht; rcases ht with rfl | rfl <;> simp)
  exact ⟨⟨l1, relIndex_of_card l1 (card_closure_pair (griessZA_comm_XA hζ) (griessZA_pow hζ)
      (griessXA_pow hζ) i1) hE (by norm_num)⟩,
    ⟨l2, relIndex_of_card l2 (card_closure_pair (griessZA_comm_YTA hζ a) (griessZA_pow hζ)
      (griessYTA_pow a) i2) hE (by norm_num)⟩,
    ⟨l3, relIndex_of_card l3 (card_closure_pair (griessXA_comm_YTA hζ a) (griessXA_pow hζ)
      (griessYTA_pow a) i3) hE (by norm_num)⟩⟩

@[expose] noncomputable def griessHmT (hζ : IsPrimitiveRoot ζ 5) (a : Fin Tag.E8.rank → Kˣ) :
    Subgroup (ModGL Tag.E8 K) :=
  (hyperClosure 5 (⊤ : Subgroup (adjointGroup Tag.E8 K)) (griessCubeT hζ a)).map
    (adjointGroup Tag.E8 K).subtype

theorem exists_monomial_conj_griessYT (v : WeylGroup Tag.E8) (a : Fin Tag.E8.rank → Kˣ)
    (hw : ∀ i j : Fin 5, i ≠ j →
      griessW • sigmaRootE8A4 v i j = sigmaRootE8A4 v (finRotate 5 i) (finRotate 5 j)) :
    ∃ du : Fin 5 → Kˣ, ∀ A : SL(5, K), griessYT K a * rhoSigmaE8A4 K v A * (griessYT K a)⁻¹ =
      rhoSigmaE8A4 K v (rotSL * conjDiagn du A * rotSL⁻¹) := by
  obtain ⟨du, hdu⟩ := exists_monomial_conj (rhoSigmaE8A4 K v) (rhoSigmaE8A4_injective v)
    (sigmaRootE8A4 v) (fun i j hij => isRoot_sigmaRootE8A4 v hij)
    (rhoSigmaE8A4_transvection v) (griessY_sign (K := K)) hw
  refine ⟨du * fun i => rootChar a (wbE8A4 v i), fun A => ?_⟩
  have ht := rhoSigmaE8A4_torus (L := K) v a A
  calc griessYT K a * rhoSigmaE8A4 K v A * (griessYT K a)⁻¹ =
        griessY K * (rootDiagUnit Tag.E8 a * rhoSigmaE8A4 K v A * (rootDiagUnit Tag.E8 a)⁻¹) *
          (griessY K)⁻¹ := by
        rw [griessYT, _root_.mul_inv_rev]
        group
    _ = griessY K * rhoSigmaE8A4 K v (conjDiagn (fun i => rootChar a (wbE8A4 v i)) A) *
          (griessY K)⁻¹ := by rw [ht]
    _ = rhoSigmaE8A4 K v (rotSL * conjDiagn (du * fun i => rootChar a (wbE8A4 v i)) A *
          rotSL⁻¹) := by rw [hdu, conjDiagn_conjDiagn]

theorem hyperGen_griessCubeT [Finite K] (hζ : IsPrimitiveRoot ζ 5) (a : Fin Tag.E8.rank → Kˣ) :
    HyperGen 5 (⊤ : Subgroup (adjointGroup Tag.E8 K)) (griessCubeT hζ a) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h5 : 5 ∣ Nat.card K - 1 := by
    have h1 : orderOf (griessU hζ) = 5 := (griessU_prim hζ).eq_orderOf.symm
    have h2 := orderOf_dvd_card (G := Kˣ) (x := griessU hζ)
    rw [h1, Fintype.card_units] at h2
    rwa [Nat.card_eq_fintype_card]
  obtain ⟨⟨hF1, hi1⟩, ⟨hF2, hi2⟩, ⟨hF3, hi3⟩⟩ := griessT_hyperplanes hζ a
  have hmem : ∀ {b c : adjointGroup Tag.E8 K},
      Subgroup.closure ({b, c} : Set (adjointGroup Tag.E8 K)) ≤ griessCubeT hζ a →
      (Subgroup.closure ({b, c} : Set (adjointGroup Tag.E8 K))).relIndex
        (griessCubeT hζ a) = 5 →
      ∀ g : ModGL Tag.E8 K, g ∈ adjointGroup Tag.E8 K → (b : ModGL Tag.E8 K) * g = g * b →
        (c : ModGL Tag.E8 K) * g = g * c → g ∈ griessHmT hζ a := by
    intro b c hle hidx g hg hb hc
    exact Subgroup.mem_map.2 ⟨⟨g, hg⟩,
      mem_hyperClosure_pair hle hidx (Subtype.ext hb) (Subtype.ext hc), rfl⟩
  have hT : ∀ t ∈ torusGroup Tag.E8 K, t ∈ griessHmT hζ a := by
    intro t ht
    obtain ⟨b, rfl⟩ :=
      CFSG.LieType.SeitzGeneration.ExcHighThree.exists_rootDiagUnit_of_mem_torusGroup ht
    refine hmem hF1 hi1 _ (torusGroup_le_adjointGroup_E8' ht) ?_ ?_
    · show griessZ hζ * rootDiagUnit Tag.E8 b = rootDiagUnit Tag.E8 b * griessZ hζ
      rw [griessZ, rootDiagUnit_comm]
    · show griessX hζ * rootDiagUnit Tag.E8 b = rootDiagUnit Tag.E8 b * griessX hζ
      rw [griessX, rootDiagUnit_comm]
  have hrhoG : ∀ (v : WeylGroup Tag.E8) (A : SL(5, K)),
      rhoSigmaE8A4 K v A ∈ adjointGroup Tag.E8 K := by
    intro v A
    have h1 : rhoSigmaE8A4 K v A ∈ (rhoSigmaE8A4 K v).range := ⟨A, rfl⟩
    rw [rhoSigmaE8A4_range] at h1
    exact (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α :
      rootSpan Tag.E8 K (sigmaSetE8A4 v) ≤ adjointGroup Tag.E8 K) h1
  have hdiag : ∀ (v : WeylGroup Tag.E8) (A : SL(5, K)),
      (∃ t : Fin 5 → K, (A : Matrix (Fin 5) (Fin 5) K) = diagonal t) →
        rhoSigmaE8A4 K v A ∈ griessHmT hζ a := by
    rintro v A ⟨t, ht⟩
    refine hT _ (rhoSigmaE8A4_diagonal v A fun i j hij => ?_)
    rw [ht]
    exact diagonal_apply_ne _ hij
  obtain ⟨duA, hduA⟩ := exists_monomial_conj_griessYT (K := K) e8VA a
    (fun i j hij => griessW_sigmaA hij)
  have hA : ∀ A : SL(5, K), rhoSigmaE8A4 K e8VA A ∈ griessHmT hζ a :=
    monomial_closure h5 hζ (rhoSigmaE8A4 K e8VA) (griessYT K a) duA hduA (griessHmT hζ a)
      (hdiag e8VA)
      (fun A hyA => hmem hF2 hi2 _ (hrhoG e8VA A) (griessZ_comm_rhoA hζ A) hyA)
  obtain ⟨duV, hduV⟩ := exists_monomial_conj_griessYT (K := K) griessV a
    (fun i j hij => griessW_sigmaV hij)
  have hV : ∀ A : SL(5, K), rhoSigmaE8A4 K griessV A ∈ griessHmT hζ a :=
    monomial_closure h5 hζ (rhoSigmaE8A4 K griessV) (griessYT K a) duV hduV (griessHmT hζ a)
      (hdiag griessV)
      (fun A hyA => hmem hF3 hi3 _ (hrhoG griessV A) (griessX_comm_rhoV hζ A) hyA)
  have hrange : ∀ v : WeylGroup Tag.E8, (∀ A, rhoSigmaE8A4 K v A ∈ griessHmT hζ a) →
      rootSpan Tag.E8 K (sigmaSetE8A4 v) ≤ griessHmT hζ a := by
    intro v hv
    rw [← rhoSigmaE8A4_range]
    rintro _ ⟨A, rfl⟩
    exact hv A
  have hroots : ∀ r ∈ e8ListA ++ griessList1, rootSubgroup Tag.E8 K r ≤ griessHmT hζ a := by
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · refine (Heis.rootSubgroup_le_rootSpan_of_mem (S := sigmaSetE8A4 e8VA) ?_).trans
        (hrange e8VA hA)
      rw [sigmaSet_e8VA]
      exact hr
    · refine (Heis.rootSubgroup_le_rootSpan_of_mem (S := sigmaSetE8A4 griessV) ?_).trans
        (hrange griessV hV)
      rw [sigmaSet_griessV]
      exact hr
  have hend := chain_le (griessHmT hζ a) griessSteps (e8ListA ++ griessList1) griessChain_ok
    hroots
  have hadj : adjointGroup Tag.E8 K ≤ griessHmT hζ a := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨i, c, hg | hg⟩
    · have h : g = pinnedX Tag.E8 K (Pi.single i 1) c := by
        rw [pinnedX_single]
        exact Units.ext hg
      rw [h]
      exact hend _ (griessChain_targets i).1 (mem_rootSubgroup.2 ⟨c, rfl⟩)
    · have h : g = pinnedX Tag.E8 K (-Pi.single i 1) c := by
        rw [pinnedX_neg_single]
        exact Units.ext hg
      rw [h]
      exact hend _ (griessChain_targets i).2 (mem_rootSubgroup.2 ⟨c, rfl⟩)
  rw [hyperGen_iff_le]
  intro g _
  obtain ⟨h, hh, he⟩ := Subgroup.mem_map.1 (hadj g.2)
  have hhg : h = g := Subtype.ext he
  rw [← hhg]
  exact hh

theorem hyperGen_conj_griessCubeT [Finite K] (hζ : IsPrimitiveRoot ζ 5)
    (a : Fin Tag.E8.rank → Kˣ) (g : adjointGroup Tag.E8 K) :
    HyperGen 5 (⊤ : Subgroup (adjointGroup Tag.E8 K))
      ((griessCubeT hζ a).map (MulAut.conj g).toMonoidHom) :=
  hyperGen_conj g (hyperGen_griessCubeT hζ a)

end Cube

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Twist

end
