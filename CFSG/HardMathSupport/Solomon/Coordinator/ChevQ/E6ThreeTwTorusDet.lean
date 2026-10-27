module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLayerNC
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.FullUni

import Mathlib.Tactic.Group
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.RankThree.PartTwo.KFacts (unitaryIsom3 mem_unitaryIsom3)
open CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd

set_option linter.unusedSectionVars false

local notation "GL₃" => Matrix.GeneralLinearGroup (Fin 3)

section Scalars

variable {p n : ℕ} {F : Type} [Field F]

theorem bar_eq_inv_of_pow_three_eq_one (hF : UnitaryFieldData p n F) (h3 : 3 ∣ p ^ n + 1)
    {l : F} (hl : l ^ 3 = 1) : hF.bar l = l⁻¹ := by
  obtain ⟨m, hm⟩ := h3
  have h1 : 1 ≤ p ^ n := Nat.one_le_pow _ _ hF.prime.pos
  obtain ⟨k, hk⟩ : ∃ k, p ^ n = 3 * k + 2 := ⟨m - 1, by omega⟩
  rw [hF.bar_apply, hk, pow_add, pow_mul, hl, one_pow, one_mul]
  exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hl)

theorem three_dvd_card_sub_one_of_unitary (hF : UnitaryFieldData p n F) (h3 : 3 ∣ p ^ n + 1) :
    3 ∣ Nat.card F - 1 := by
  have hq := hF.one_lt_pow
  have hsq : (p ^ n) ^ 2 - 1 = (p ^ n + 1) * (p ^ n - 1) := by
    zify [hq.le, Nat.one_le_pow 2 (p ^ n) (by omega)]
    ring
  rw [hF.card_eq_sq, hsq]
  exact Dvd.dvd.mul_right h3 _

theorem eq_one_of_bar_eq_of_pow_three_eq_one (hF : UnitaryFieldData p n F) (h3 : 3 ∣ p ^ n + 1)
    {l : F} (hl : l ^ 3 = 1) (hb : hF.bar l = l) : l = 1 := by
  have h0 : l ≠ 0 := by
    rintro rfl
    simp at hl
  have h2 : l * l = 1 := by
    have := bar_eq_inv_of_pow_three_eq_one hF h3 hl
    rw [hb] at this
    exact mul_eq_one_iff_eq_inv₀ h0 |>.2 this
  calc l = l ^ 3 * (l * l)⁻¹ := by field_simp
    _ = 1 := by rw [hl, h2]; simp

end Scalars

section Core

theorem fin3_all_eq_of_forall_exists_eq {α : Type*} (d : Fin 3 → α)
    (h : ∀ i, ∃ j, j ≠ i ∧ d j = d i) : d 0 = d 1 ∧ d 1 = d 2 := by
  have e0 : ∀ j : Fin 3, j ≠ 0 → j = 1 ∨ j = 2 := by decide
  have e1 : ∀ j : Fin 3, j ≠ 1 → j = 0 ∨ j = 2 := by decide
  have e2 : ∀ j : Fin 3, j ≠ 2 → j = 0 ∨ j = 1 := by decide
  obtain ⟨j0, hj0, hd0⟩ := h 0
  obtain ⟨j1, hj1, hd1⟩ := h 1
  obtain ⟨j2, hj2, hd2⟩ := h 2
  rcases e0 j0 hj0 with rfl | rfl <;> rcases e1 j1 hj1 with rfl | rfl <;>
    rcases e2 j2 hj2 with rfl | rfl <;> grind

variable {p n : ℕ} {F : Type} [Field F]

open scoped Classical in
theorem spectral_coeff_eq {l x c : F} (hl : l ^ 3 = 1) (hx : x ^ 3 = 1) (hc3 : c * 3 = 1) :
    c * (1 + l ^ 2 * x + l * (x * x)) = if x = l then 1 else 0 := by
  split_ifs with h
  · rw [h]
    calc c * (1 + l ^ 2 * l + l * (l * l)) = c * (1 + l ^ 3 + l ^ 3) := by ring
      _ = 1 := by rw [hl]; linear_combination hc3
  · have ht3 : (l ^ 2 * x) ^ 3 = 1 := by
      calc (l ^ 2 * x) ^ 3 = (l ^ 3) ^ 2 * x ^ 3 := by ring
        _ = 1 := by rw [hl, hx]; norm_num
    have ht1 : l ^ 2 * x ≠ 1 := by
      intro h1
      apply h
      calc x = l ^ 3 * x := by rw [hl, one_mul]
        _ = l * (l ^ 2 * x) := by ring
        _ = l := by rw [h1, mul_one]
    have hsum := cube_root_sq_add_eq_zeroU ht3 ht1
    have hsq : (l ^ 2 * x) ^ 2 = l * (x * x) := by
      calc (l ^ 2 * x) ^ 2 = l ^ 3 * l * (x * x) := by ring
        _ = l * (x * x) := by rw [hl, one_mul]
    have h0 : 1 + l ^ 2 * x + l * (x * x) = 0 := by
      rw [← hsq]
      linear_combination hsum
    rw [h0, mul_zero]

theorem exists_isom_commute_det_eq_of_pow_three_eq_one (hF : UnitaryFieldData p n F)
    (h3 : 3 ∣ p ^ n + 1) {S : Matrix (Fin 3) (Fin 3) F} (hS3 : S ^ 3 = 1)
    (hSu : (S.map hF.bar)ᵀ * S = 1) {β : F} (hβ : hF.bar β * β = 1) :
    ∃ Z : Matrix (Fin 3) (Fin 3) F, Z * S = S * Z ∧ Z.det = β ∧ (Z.map hF.bar)ᵀ * Z = 1 := by
  classical
  haveI := hF.finite
  obtain ⟨ω, hω⟩ := exists_isPrimitiveRoot_three (three_dvd_card_sub_one_of_unitary hF h3)
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hω1 : ω ≠ 1 := hω.ne_one (by norm_num)
  have h3F : (3 : F) ≠ 0 := three_ne_zero_of_cube_rootU hω3 hω1
  have hS3' : S * (S * S) = 1 := by rw [← pow_three]; exact hS3
  have hS3'' : S * S * S = 1 := by rw [mul_assoc]; exact hS3'
  have hS4 : S * S * (S * S) = S := by
    rw [show S * S * (S * S) = S * S * S * S by noncomm_ring, hS3'', one_mul]
  have hSS : (S.map hF.bar)ᵀ = S * S := by
    calc (S.map hF.bar)ᵀ = (S.map hF.bar)ᵀ * (S * (S * S)) := by rw [hS3', mul_one]
      _ = ((S.map hF.bar)ᵀ * S) * (S * S) := by rw [← mul_assoc]
      _ = S * S := by rw [hSu, one_mul]
  let G : GL₃ F := ⟨S, S * S, hS3', hS3''⟩
  have hG3 : G ^ 3 = 1 := Units.ext (by simpa [G] using hS3)
  have hcomm : ∀ x ∈ Subgroup.zpowers G, ∀ y ∈ Subgroup.zpowers G, x * y = y * x := by
    rintro x ⟨m, rfl⟩ y ⟨k, rfl⟩
    exact (Commute.zpow_zpow_self G m k).eq
  have hexp : ∀ x ∈ Subgroup.zpowers G, x ^ 3 = 1 := by
    rintro x ⟨m, rfl⟩
    rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, _root_.zpow_natCast,
      hG3, _root_.one_zpow]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.CTP.exists_conj_diagonal_of_exponent_prime (p := 3)
    ⟨ω, hω⟩ (Subgroup.zpowers G) hcomm hexp
  have hoff := hg G (Subgroup.mem_zpowers G)
  set Dm : Matrix (Fin 3) (Fin 3) F := ((g * G * g⁻¹ : GL₃ F) : Matrix (Fin 3) (Fin 3) F) with hDm
  set d : Fin 3 → F := fun i => Dm i i with hd
  have hDd : Dm = diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hd]
    · rw [diagonal_apply_ne _ hij]
      exact hoff i j hij
  have hgS : (g : Matrix (Fin 3) (Fin 3) F) * S = Dm * g := by
    have h : g * G = (g * G * g⁻¹) * g := by group
    have h' := congrArg Units.val h
    simpa [hDm, G] using h'
  have hDm3 : Dm ^ 3 = 1 := by
    rw [hDm, ← Units.val_pow_eq_pow_val, conj_pow, hG3, mul_one, mul_inv_cancel, Units.val_one]
  have hd3 : ∀ i, d i ^ 3 = 1 := by
    intro i
    have h := hDm3
    rw [hDd, diagonal_pow] at h
    have h' := congrFun (congrFun h i) i
    simpa using h'
  by_cases hall : d 0 = d 1 ∧ d 1 = d 2
  ·
    have hDs : Dm = d 0 • (1 : Matrix (Fin 3) (Fin 3) F) := by
      rw [hDd, Matrix.smul_one_eq_diagonal]
      congr 1
      funext i
      fin_cases i
      · rfl
      · exact hall.1.symm
      · exact (hall.1.trans hall.2).symm
    have hSs : S = d 0 • (1 : Matrix (Fin 3) (Fin 3) F) := by
      have h : S = (g⁻¹ : GL₃ F).val * ((g : Matrix (Fin 3) (Fin 3) F) * S) := by
        rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      rw [h, hgS, hDs, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, ← Units.val_mul,
        inv_mul_cancel, Units.val_one]
    refine ⟨diagonal ![β, 1, 1], ?_, ?_, ?_⟩
    · rw [hSs, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    · rw [det_diagonal, Fin.prod_univ_three]
      simp
    · rw [diagonal_map (map_zero hF.bar), diagonal_transpose, diagonal_mul_diagonal]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [diagonal_apply, hβ]
  ·
    obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin 3, ∀ j, j ≠ i₀ → d j ≠ d i₀ := by
      by_contra hcon
      push Not at hcon
      apply hall
      exact fin3_all_eq_of_forall_exists_eq d hcon
    obtain ⟨l, hl⟩ : ∃ l, l = d i₀ := ⟨_, rfl⟩
    have hl3 : l ^ 3 = 1 := hl ▸ hd3 i₀
    have hl0 : l ≠ 0 := by
      rintro rfl
      simp at hl3
    have hbl : hF.bar l = l⁻¹ := bar_eq_inv_of_pow_three_eq_one hF h3 hl3
    have hl2 : l⁻¹ = l ^ 2 :=
      (eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hl3)).symm
    obtain ⟨c, hc⟩ : ∃ c : F, c = (3 : F)⁻¹ := ⟨_, rfl⟩
    have hc3 : c * 3 = 1 := by rw [hc]; exact inv_mul_cancel₀ h3F
    have hbc : hF.bar c = c := by rw [hc, map_inv₀, map_ofNat]
    obtain ⟨E, hE⟩ : ∃ E : Matrix (Fin 3) (Fin 3) F,
        E = c • (1 + l ^ 2 • S + l • (S * S)) := ⟨_, rfl⟩
    obtain ⟨En, hEn⟩ : ∃ En : Matrix (Fin 3) (Fin 3) F,
        En = diagonal (fun i => if i = i₀ then (1 : F) else 0) := ⟨_, rfl⟩
    have hiff : ∀ i, d i = l ↔ i = i₀ := by
      intro i
      constructor
      · intro h
        by_contra hne
        exact hi₀ i hne (h.trans hl)
      · rintro rfl
        exact hl.symm
    have hDiag : c • (1 + l ^ 2 • Dm + l • (Dm * Dm)) = En := by
      rw [hEn, hDd, diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst hij
        have h := spectral_coeff_eq hl3 (hd3 i) hc3
        simp only [hiff] at h
        simpa [diagonal_apply_eq, Matrix.one_apply_eq, mul_comm, mul_assoc] using h
      · simp [diagonal_apply_ne _ hij, Matrix.one_apply_ne hij, hij]
    have hgE : (g : Matrix (Fin 3) (Fin 3) F) * E = En * g := by
      have hgSS : (g : Matrix (Fin 3) (Fin 3) F) * (S * S) = Dm * Dm * g := by
        rw [← Matrix.mul_assoc, hgS, Matrix.mul_assoc, hgS, ← Matrix.mul_assoc]
      rw [hE, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
        Matrix.mul_smul, hgS, hgSS, ← hDiag]
      simp only [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul]
    have hbl2 : hF.bar (l ^ 2) = l := by
      rw [map_pow, hbl, hl2]
      calc (l ^ 2) ^ 2 = l ^ 3 * l := by ring
        _ = l := by rw [hl3, one_mul]
    have hcancel : ∀ X Y : Matrix (Fin 3) (Fin 3) F,
        (g : Matrix (Fin 3) (Fin 3) F) * X = (g : Matrix (Fin 3) (Fin 3) F) * Y → X = Y := by
      intro X Y h
      have h1 := congrArg (fun M => ((g⁻¹ : GL₃ F) : Matrix (Fin 3) (Fin 3) F) * M) h
      simpa [← Matrix.mul_assoc, ← Units.val_mul] using h1
    have hEnEn : En * En = En := by
      rw [hEn, diagonal_mul_diagonal]
      congr 1
      funext i
      split_ifs <;> simp
    have hE2 : E * E = E := by
      apply hcancel
      rw [← Matrix.mul_assoc, hgE, Matrix.mul_assoc, hgE, ← Matrix.mul_assoc, hEnEn]
    have hSE : S * E = E * S := by
      rw [hE]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    have hEadj : (E.map hF.bar)ᵀ = E := by
      rw [hE, adjU_smul, hbc, adjU_add, adjU_add, adjU_one, adjU_smul, adjU_smul, adjU_mul, hSS,
        hS4, hbl2, hbl, hl2]
      congr 1
      abel
    have hDiagZ : (diagonal (fun i => if i = i₀ then β else 1) : Matrix (Fin 3) (Fin 3) F) =
        1 + (β - 1) • En := by
      rw [hEn]
      ext i j
      by_cases hij : i = j
      · subst hij
        by_cases hi : i = i₀ <;> simp [hi, diagonal_apply, Matrix.one_apply]
      · simp [diagonal_apply_ne _ hij, Matrix.one_apply_ne hij, hij]
    refine ⟨1 + (β - 1) • E, ?_, ?_, ?_⟩
    · rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
        Matrix.mul_smul, hSE]
    · have hZg : (g : Matrix (Fin 3) (Fin 3) F) * (1 + (β - 1) • E) =
          diagonal (fun i => if i = i₀ then β else 1) * g := by
        rw [hDiagZ, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hgE, Matrix.add_mul,
          Matrix.one_mul, Matrix.smul_mul]
      have hgdet : ((g : Matrix (Fin 3) (Fin 3) F)).det ≠ 0 :=
        ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
      have h := congrArg Matrix.det hZg
      rw [Matrix.det_mul, Matrix.det_mul, det_diagonal] at h
      have hprod : (∏ i : Fin 3, if i = i₀ then β else (1 : F)) = β := by
        simp [Finset.prod_ite_eq']
      rw [hprod] at h
      exact mul_left_cancel₀ hgdet (h.trans (mul_comm _ _))
    · have hZadj : ((1 + (β - 1) • E).map hF.bar)ᵀ = 1 + (hF.bar β - 1) • E := by
        rw [adjU_add, adjU_one, adjU_smul, hEadj, map_sub, map_one]
      rw [hZadj]
      have key : (1 + (hF.bar β - 1) • E) * (1 + (β - 1) • E) =
          1 + ((hF.bar β - 1) + (β - 1) + (hF.bar β - 1) * (β - 1)) • E := by
        simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul,
          hE2]
        module
      rw [key]
      have h0 : (hF.bar β - 1) + (β - 1) + (hF.bar β - 1) * (β - 1) = 0 := by
        linear_combination hβ
      rw [h0, zero_smul, add_zero]

end Core

section Main

variable {p n : ℕ} {F : Type} [Field F]

theorem exists_isom_commute_det_eq_of_pow_three (hF : UnitaryFieldData p n F)
    (h3 : 3 ∣ p ^ n + 1) {γ : Matrix (Fin 3) (Fin 3) F} {α : F} (hγ3 : γ ^ 3 = α • 1)
    (hγu : (γ.map hF.bar)ᵀ * γ = 1) {β : F} (hβ : hF.bar β * β = 1) :
    ∃ Z : Matrix (Fin 3) (Fin 3) F, Z * γ = γ * Z ∧ Z.det = β ∧ (Z.map hF.bar)ᵀ * Z = 1 := by
  classical
  haveI := hF.finite
  have hγdet : γ.det ≠ 0 := by
    intro h0
    have h := congrArg Matrix.det hγu
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at h
    exact zero_ne_one h
  have hdet3 : γ.det ^ 3 = α ^ 3 := by
    have h := congrArg Matrix.det hγ3
    rw [Matrix.det_pow, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at h
    exact h
  have hα0 : α ≠ 0 := by
    rintro rfl
    apply hγdet
    have h : γ.det ^ 3 = 0 := by rw [hdet3]; ring
    exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).1 h
  by_cases hcube : ∃ μ : F, μ ^ 3 = α
  · obtain ⟨μ, hμ⟩ := hcube
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      apply hα0
      rw [← hμ]
      ring
    have hdn : hF.bar γ.det * γ.det = 1 := by
      have h := congrArg Matrix.det hγu
      rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
      rwa [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
    have hαu : hF.bar α * α = 1 := by
      apply eq_one_of_bar_eq_of_pow_three_eq_one hF h3
      · calc (hF.bar α * α) ^ 3 = hF.bar (α ^ 3) * α ^ 3 := by rw [map_pow, mul_pow]
          _ = hF.bar (γ.det ^ 3) * γ.det ^ 3 := by rw [hdet3]
          _ = (hF.bar γ.det * γ.det) ^ 3 := by rw [map_pow, mul_pow]
          _ = 1 := by rw [hdn, one_pow]
      · rw [map_mul, hF.bar_bar, mul_comm]
    have hν : hF.bar μ * μ = 1 := by
      apply eq_one_of_bar_eq_of_pow_three_eq_one hF h3
      · calc (hF.bar μ * μ) ^ 3 = hF.bar (μ ^ 3) * μ ^ 3 := by rw [map_pow, mul_pow]
          _ = 1 := by rw [hμ, hαu]
      · rw [map_mul, hF.bar_bar, mul_comm]
    obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin 3) (Fin 3) F, S = μ⁻¹ • γ := ⟨_, rfl⟩
    have hS3 : S ^ 3 = 1 := by
      rw [hS, smul_pow, hγ3, smul_smul, ← hμ, inv_pow, inv_mul_cancel₀ (pow_ne_zero 3 hμ0),
        one_smul]
    have hSu : (S.map hF.bar)ᵀ * S = 1 := by
      rw [hS, adjU_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hγu, map_inv₀, ← mul_inv,
        hν, inv_one, one_smul]
    obtain ⟨Z, hZS, hZdet, hZu⟩ :=
      exists_isom_commute_det_eq_of_pow_three_eq_one hF h3 hS3 hSu hβ
    refine ⟨Z, ?_, hZdet, hZu⟩
    have hγS : γ = μ • S := by rw [hS, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
    rw [hγS, Matrix.mul_smul, Matrix.smul_mul, hZS]
  · have hα' : ∀ b : F, b ^ 3 ≠ α := fun b hb => hcube ⟨b, hb⟩
    have hdet : γ.det = α := by
      have h := det_sub_smul_one_of_pow_three_not_cube hα' hγ3 0
      simpa using h
    have hβ0 : β ≠ 0 := by
      rintro rfl
      simp at hβ
    let Gγ : GL₃ F := Matrix.GeneralLinearGroup.mkOfDetNeZero γ hγdet
    have hGγ : Gγ ∈ unitaryIsom3 hF := mem_unitaryIsom3.2 hγu
    have hβmem : Units.mk0 β hβ0 ∈ rootsOfUnity (p ^ n + 1) F := by
      rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one,
        Units.val_mk0, ← hF.norm_eq_pow, UnitaryFieldData.norm, mul_comm]
      exact hβ
    let u : rootsOfUnity (p ^ n + 1) F :=
      ⟨Matrix.GeneralLinearGroup.det Gγ, det_mem_rootsOfUnityU hF hGγ⟩
    let v : rootsOfUnity (p ^ n + 1) F := ⟨(Units.mk0 β hβ0)⁻¹, inv_mem hβmem⟩
    have hu : ¬ ∃ w : rootsOfUnity (p ^ n + 1) F, w ^ 3 = u := by
      rintro ⟨w, hw⟩
      apply hα' ((w : Fˣ) : F)
      have h := congrArg (fun x : rootsOfUnity (p ^ n + 1) F => ((x : Fˣ) : F)) hw
      simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, u,
        Matrix.GeneralLinearGroup.val_det_apply] at h
      rw [h]
      exact hdet
    obtain ⟨k, w, hw⟩ := exists_cube_mul_pow_unitary (v := v) hu
    have hw' : (w : Fˣ) ^ 3 = (Units.mk0 β hβ0)⁻¹ * Matrix.GeneralLinearGroup.det Gγ ^ k := by
      have h := congrArg Subtype.val hw
      rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow] at h
      exact h
    let Zg : GL₃ F := Gγ ^ k * Matrix.GeneralLinearGroup.scalar (Fin 3) (w : Fˣ)⁻¹
    have hZmem : Zg ∈ unitaryIsom3 hF :=
      mul_mem (pow_mem hGγ k) (scalarU_mem_unitaryIsom3 hF (inv_mem w.2))
    have hZcomm : Zg * Gγ = Gγ * Zg := by
      have h1 : Commute (Gγ ^ k) Gγ := (Commute.refl Gγ).pow_left k
      have h2 : Commute (Matrix.GeneralLinearGroup.scalar (Fin 3) (w : Fˣ)⁻¹) Gγ :=
        Matrix.GeneralLinearGroup.scalar_commute _ Gγ
      exact (h1.mul_left h2).eq
    have hZdet : Matrix.GeneralLinearGroup.det Zg = Units.mk0 β hβ0 := by
      rw [map_mul, map_pow, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, inv_pow, hw',
        _root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
    refine ⟨(Zg : Matrix (Fin 3) (Fin 3) F), ?_, ?_, mem_unitaryIsom3.1 hZmem⟩
    · have h := congrArg Units.val hZcomm
      rwa [Units.val_mul, Units.val_mul] at h
    · rw [← Matrix.GeneralLinearGroup.val_det_apply, hZdet, Units.val_mk0]

end Main

section Packaged

open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.RankThree.PartTwo.KFacts (suConj coe_suConj unitarySU_le_unitaryIsom3)

variable {p n : ℕ} {F : Type} [Field F] (hF : UnitaryFieldData p n F)

theorem exists_unitaryIsom_commute_det_eq_of_pow_three (h3 : 3 ∣ p ^ n + 1)
    {γ : unitaryIsom3 hF} {α : F}
    (hγ : ((γ : GL₃ F) : Matrix (Fin 3) (Fin 3) F) ^ 3 = α • 1)
    {β : Fˣ} (hβ : β ∈ rootsOfUnity (p ^ n + 1) F) :
    ∃ δ : unitaryIsom3 hF, (δ : GL₃ F) * γ = γ * δ ∧
      Matrix.GeneralLinearGroup.det (δ : GL₃ F) = β := by
  have hβ' : hF.bar (β : F) * (β : F) = 1 := by
    rw [mul_comm, ← UnitaryFieldData.norm, hF.norm_eq_pow, ← Units.val_pow_eq_pow_val,
      (mem_rootsOfUnity _ _).1 hβ, Units.val_one]
  obtain ⟨Z, hZc, hZd, hZu⟩ :=
    exists_isom_commute_det_eq_of_pow_three hF h3 hγ (mem_unitaryIsom3.1 γ.2) hβ'
  let Zg : GL₃ F := Matrix.GeneralLinearGroup.mkOfDetNeZero Z (by rw [hZd]; exact β.ne_zero)
  refine ⟨⟨Zg, mem_unitaryIsom3.2 hZu⟩, Units.ext hZc, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact hZd

theorem exists_suConj_mul_eq (h3 : 3 ∣ p ^ n + 1) {A B : unitaryIsom3 hF} (hAB : A * B = B * A)
    (x : unitarySU p n F 3) {α : F}
    (hx : (((B : GL₃ F) * (x : GL₃ F) : GL₃ F) : Matrix (Fin 3) (Fin 3) F) ^ 3 = α • 1) :
    ∃ y : unitarySU p n F 3, suConj hF A⁻¹ x * y = suConj hF B⁻¹ y * x := by
  let γ : unitaryIsom3 hF := B * ⟨(x : GL₃ F), unitarySU_le_unitaryIsom3 x.2⟩
  obtain ⟨δ, hδ, hdet⟩ := exists_unitaryIsom_commute_det_eq_of_pow_three hF h3 (γ := γ) hx
    (det_mem_rootsOfUnityU hF A.2)
  have hy1 : (((A⁻¹ * δ : unitaryIsom3 hF) : GL₃ F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, Subgroup.coe_mul, map_mul, Subgroup.coe_inv,
      map_inv, hdet, inv_mul_cancel, Units.val_one]
  refine ⟨⟨((A⁻¹ * δ : unitaryIsom3 hF) : GL₃ F),
    (mem_unitarySU_iff hF).2 ⟨hy1, (A⁻¹ * δ).2⟩⟩, Subtype.ext ?_⟩
  have hABg : (A : GL₃ F) * B = B * A := congrArg Subtype.val hAB
  have hBA : (B : GL₃ F)⁻¹ * (A : GL₃ F)⁻¹ * B = (A : GL₃ F)⁻¹ := by
    have hc : Commute (A : GL₃ F) (B : GL₃ F) := hABg
    rw [mul_assoc, hc.inv_left.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hδg : (δ : GL₃ F) * ((B : GL₃ F) * (x : GL₃ F)) = (B : GL₃ F) * (x : GL₃ F) * δ := hδ
  simp only [Subgroup.coe_mul, coe_suConj, Subgroup.coe_inv, inv_inv]
  calc (A : GL₃ F)⁻¹ * (x : GL₃ F) * A * ((A : GL₃ F)⁻¹ * δ)
      = (A : GL₃ F)⁻¹ * ((x : GL₃ F) * δ) := by group
    _ = (B : GL₃ F)⁻¹ * (A : GL₃ F)⁻¹ * B * ((x : GL₃ F) * δ) := by rw [hBA]
    _ = (B : GL₃ F)⁻¹ * (A : GL₃ F)⁻¹ * ((B : GL₃ F) * (x : GL₃ F) * δ) := by group
    _ = (B : GL₃ F)⁻¹ * (A : GL₃ F)⁻¹ * (δ * ((B : GL₃ F) * (x : GL₃ F))) := by rw [hδg]
    _ = (B : GL₃ F)⁻¹ * ((A : GL₃ F)⁻¹ * δ) * B * (x : GL₃ F) := by group

end Packaged

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
