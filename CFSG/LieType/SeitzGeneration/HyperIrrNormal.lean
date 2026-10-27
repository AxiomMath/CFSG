module

public import CFSG.LieType.SeitzGeneration.HyperIrrData
public import CFSG.LieType.SeitzGeneration.HyperIrrRadical

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix
open scoped commutatorElement

variable {F : Type*} [Field F] [Finite F] {n : ℕ}

theorem dvd_card_sub_one_of_isPrimitiveRoot {p : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : p ≠ 0) : p ∣ Nat.card F - 1 := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp
  have := Fintype.ofFinite F
  have h1 := FiniteField.pow_card_sub_one_eq_one ζ hζ0
  rw [Nat.card_eq_fintype_card]
  exact hζ.dvd_of_pow_eq_one _ h1

theorem exists_radical_normalized_lift {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n)
    (hpq : p ∣ Nat.card F - 1) {a r : SpecialLinearGroup (Fin n) F}
    (hap : a ^ p ∈ Subgroup.center (SpecialLinearGroup (Fin n) F))
    (hrp : r ^ p ∈ Subgroup.center (SpecialLinearGroup (Fin n) F)) (har : a * r = r * a)
    {c : F} (hc : (r : Matrix (Fin n) (Fin n) F) ^ p = c • (1 : Matrix (Fin n) (Fin n) F))
    (hnc : ∀ b : F, b ^ p ≠ c) :
    ∃ (j : ℕ) (s : F), s ≠ 0 ∧
      (((a * r ^ j) ^ p : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        (s ^ p) • (1 : Matrix (Fin n) (Fin n) F) := by
  have hab : ⁅a, r⁆ ∈ Subgroup.center (SpecialLinearGroup (Fin n) F) := by
    rw [commutatorElement_eq_one_iff_mul_comm.2 har]; exact Subgroup.one_mem _
  obtain ⟨e, f, hef, s, hs0, hes⟩ := exists_split_line hp hp2 hn hpq hap hrp hab
  rcases hef with ⟨he, -⟩ | ⟨j, he, -⟩
  · exfalso
    rw [he, Matrix.SpecialLinearGroup.coe_pow, hc] at hes
    exact hnc s (smul_one_inj hn hes).symm
  · rw [he] at hes
    exact ⟨j, s, hs0, hes⟩

omit [Finite F] in
theorem smul_quasi {X Y : Matrix (Fin n) (Fin n) F} {ζ : F} (h : X * Y = ζ • (Y * X))
    (a b : F) : (a • X) * (b • Y) = ζ • ((b • Y) * (a • X)) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, h]
  simp only [smul_smul]
  congr 1
  ring

omit [Finite F] in
theorem quasi_mul_pow {X Y R : Matrix (Fin n) (Fin n) F} {ζ : F} (hXY : X * Y = ζ • (Y * X))
    (hX : Commute X R) (hY : Commute Y R) (a b : ℕ) :
    (X * R ^ a) * (Y * R ^ b) = ζ • ((Y * R ^ b) * (X * R ^ a)) := by
  have e1 : R ^ a * Y = Y * R ^ a := (hY.pow_right a).eq.symm
  have e2 : R ^ b * X = X * R ^ b := (hX.pow_right b).eq.symm
  have e3 : R ^ a * R ^ b = R ^ b * R ^ a := (Commute.pow_pow_self R a b).eq
  calc (X * R ^ a) * (Y * R ^ b) = X * (R ^ a * Y) * R ^ b := by simp only [Matrix.mul_assoc]
    _ = X * (Y * R ^ a) * R ^ b := by rw [e1]
    _ = (X * Y) * (R ^ a * R ^ b) := by simp only [Matrix.mul_assoc]
    _ = ζ • ((Y * X) * (R ^ b * R ^ a)) := by rw [hXY, e3, Matrix.smul_mul]
    _ = ζ • (Y * (X * R ^ b) * R ^ a) := by simp only [Matrix.mul_assoc]
    _ = ζ • (Y * (R ^ b * X) * R ^ a) := by rw [e2]
    _ = ζ • ((Y * R ^ b) * (X * R ^ a)) := by simp only [Matrix.mul_assoc]

theorem exists_kron_data {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpF : (p : F) ≠ 0) (hn : 0 < n)
    {E : Subgroup (ProjectiveSpecialLinearGroup (Fin n) F)}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 3) {x y : SpecialLinearGroup (Fin n) F} (hx : toPSL x ∈ E)
    (hy : toPSL y ∈ E) (hxy : x * y ≠ y * x)
    (hirr : ∀ W : Submodule F (Fin n → F),
      (∀ z : SpecialLinearGroup (Fin n) F, toPSL z ∈ E →
        ∀ w ∈ W, (z : Matrix (Fin n) (Fin n) F).mulVec w ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ (x' y' r : SpecialLinearGroup (Fin n) F) (sx sy ζ c : F)
      (A B C : Matrix (Fin n) (Fin n) F) (u₀ : Fin n → F),
      toPSL x' ∈ E ∧ toPSL y' ∈ E ∧ toPSL r ∈ E ∧
      E ≤ Subgroup.closure ({toPSL x', toPSL y', toPSL r} :
        Set (ProjectiveSpecialLinearGroup (Fin n) F)) ∧
      (x' : Matrix (Fin n) (Fin n) F) = sx • A ∧ (y' : Matrix (Fin n) (Fin n) F) = sy • B ∧
      (r : Matrix (Fin n) (Fin n) F) = C ∧ KronData p ζ c A B C u₀ := by
  classical
  obtain ⟨ζ, r, hprim, hζ, hrE, hr1, hgen, hxr, hyr⟩ :=
    exists_radical_triple hp hn hcomm hexp hcard hx hy hxy
  have hpq : p ∣ Nat.card F - 1 := dvd_card_sub_one_of_isPrimitiveRoot hprim hp.ne_zero
  have hpowc : ∀ a : SpecialLinearGroup (Fin n) F, toPSL a ∈ E →
      a ^ p ∈ Subgroup.center (SpecialLinearGroup (Fin n) F) := fun a ha => by
    rw [mem_center_iff_toPSL_eq_one, map_pow]; exact hexp _ ha
  obtain ⟨c, hc0, hc⟩ := exists_scalar_of_mem_center hn (hpowc r hrE)
  rw [Matrix.SpecialLinearGroup.coe_pow] at hc
  have hnc := not_exists_pow_eq_of_irreducible hp hn ⟨ζ, hprim⟩ hgen hxr hyr hr1 hirr hc
  have hxrSL : x * r = r * x := Subtype.ext hxr
  have hyrSL : y * r = r * y := Subtype.ext hyr
  obtain ⟨jx, sx, hsx0, hsx⟩ :=
    exists_radical_normalized_lift hp hp2 hn hpq (hpowc x hx) (hpowc r hrE) hxrSL hc hnc
  obtain ⟨jy, sy, hsy0, hsy⟩ :=
    exists_radical_normalized_lift hp hp2 hn hpq (hpowc y hy) (hpowc r hrE) hyrSL hc hnc
  set x₁ := x * r ^ jx with hx₁
  set y₁ := y * r ^ jy with hy₁
  have hx₁E : toPSL x₁ ∈ E := by
    rw [hx₁, map_mul, map_pow]; exact E.mul_mem hx (E.pow_mem hrE jx)
  have hy₁E : toPSL y₁ ∈ E := by
    rw [hy₁, map_mul, map_pow]; exact E.mul_mem hy (E.pow_mem hrE jy)
  have hgen₁ : E ≤ Subgroup.closure ({toPSL x₁, toPSL y₁, toPSL r} :
      Set (ProjectiveSpecialLinearGroup (Fin n) F)) := by
    refine hgen.trans ((Subgroup.closure_le _).2 ?_)
    rintro z (rfl | rfl | rfl)
    · have : toPSL x = toPSL x₁ * (toPSL r ^ jx)⁻¹ := by
        rw [hx₁, map_mul, map_pow]; group
      rw [SetLike.mem_coe, this]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _))
    · have : toPSL y = toPSL y₁ * (toPSL r ^ jy)⁻¹ := by
        rw [hy₁, map_mul, map_pow]; group
      rw [SetLike.mem_coe, this]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _))
    · exact Subgroup.subset_closure (by simp)
  have hcX : Commute (x : Matrix (Fin n) (Fin n) F) (r : Matrix (Fin n) (Fin n) F) := hxr
  have hcY : Commute (y : Matrix (Fin n) (Fin n) F) (r : Matrix (Fin n) (Fin n) F) := hyr
  have hx₁mat : (x₁ : Matrix (Fin n) (Fin n) F) =
      (x : Matrix (Fin n) (Fin n) F) * (r : Matrix (Fin n) (Fin n) F) ^ jx := by
    rw [hx₁]; simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow]
  have hy₁mat : (y₁ : Matrix (Fin n) (Fin n) F) =
      (y : Matrix (Fin n) (Fin n) F) * (r : Matrix (Fin n) (Fin n) F) ^ jy := by
    rw [hy₁]; simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow]
  have hc₁X : Commute (x₁ : Matrix (Fin n) (Fin n) F) (r : Matrix (Fin n) (Fin n) F) := by
    rw [hx₁mat]; exact Commute.mul_left hcX (Commute.self_pow _ _).symm
  have hc₁Y : Commute (y₁ : Matrix (Fin n) (Fin n) F) (r : Matrix (Fin n) (Fin n) F) := by
    rw [hy₁mat]; exact Commute.mul_left hcY (Commute.self_pow _ _).symm
  have hxy₁ : (x₁ : Matrix (Fin n) (Fin n) F) * y₁ =
      ζ • ((y₁ : Matrix (Fin n) (Fin n) F) * x₁) := by
    rw [hx₁mat, hy₁mat]
    exact quasi_mul_pow hζ hcX hcY jx jy
  have hX₁p : (x₁ : Matrix (Fin n) (Fin n) F) ^ p = sx ^ p • (1 : Matrix (Fin n) (Fin n) F) := by
    rw [← Matrix.SpecialLinearGroup.coe_pow]; exact hsx
  have hY₁p : (y₁ : Matrix (Fin n) (Fin n) F) ^ p = sy ^ p • (1 : Matrix (Fin n) (Fin n) F) := by
    rw [← Matrix.SpecialLinearGroup.coe_pow]; exact hsy
  have hB₀ : (sy⁻¹ • (y₁ : Matrix (Fin n) (Fin n) F)) ^ p = 1 := by
    rw [smul_pow, hY₁p, smul_smul, inv_pow, inv_mul_cancel₀ (pow_ne_zero p hsy0), one_smul]
  obtain ⟨ξ, v, hξ, hv0, hB₀v⟩ := exists_eigenvector_of_pow_eq_one hp.pos ⟨ζ, hprim⟩ hn hB₀
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hξ
    exact zero_ne_one hξ
  have hxA : (x₁ : Matrix (Fin n) (Fin n) F) =
      sx • (sx⁻¹ • (x₁ : Matrix (Fin n) (Fin n) F)) := by
    rw [smul_smul, mul_inv_cancel₀ hsx0, one_smul]
  have hyB : (y₁ : Matrix (Fin n) (Fin n) F) =
      (sy * ξ) • (ξ⁻¹ • (sy⁻¹ • (y₁ : Matrix (Fin n) (Fin n) F))) := by
    rw [smul_smul, smul_smul, show sy * ξ * ξ⁻¹ * sy⁻¹ = 1 by field_simp, one_smul]
  refine ⟨x₁, y₁, r, sx, sy * ξ, ζ, c, sx⁻¹ • (x₁ : Matrix (Fin n) (Fin n) F),
    ξ⁻¹ • (sy⁻¹ • (y₁ : Matrix (Fin n) (Fin n) F)), (r : Matrix (Fin n) (Fin n) F), v,
    hx₁E, hy₁E, hrE, hgen₁, hxA, hyB, rfl, ?_⟩
  refine ⟨hp, hp2, hpF, hprim, hnc, ?_, ?_, hc, ?_, ?_, ?_, hv0, ?_, ?_⟩
  · rw [smul_pow, hX₁p, smul_smul, inv_pow, inv_mul_cancel₀ (pow_ne_zero p hsx0), one_smul]
  · rw [smul_pow, hB₀, inv_pow, hξ, inv_one, one_smul]
  · rw [smul_smul]
    exact smul_quasi hxy₁ _ _
  · rw [Matrix.smul_mul, Matrix.mul_smul]
    congr 1
  · rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul]
    congr 2
  · rw [Matrix.smul_mulVec, hB₀v, smul_smul, inv_mul_cancel₀ hξ0, one_smul]
  · intro W hAW hBW hCW
    apply hirr W
    refine stable_of_gens3 hgen₁ ?_ ?_ ?_
    · intro w hw
      have h1 := W.smul_mem sx (hAW w hw)
      rw [hxA, Matrix.smul_mulVec]
      exact h1
    · intro w hw
      have h1 := W.smul_mem (sy * ξ) (hBW w hw)
      rw [hyB, Matrix.smul_mulVec]
      exact h1
    · intro w hw
      exact hCW w hw

end CFSG.LieType.SeitzGeneration
