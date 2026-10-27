module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUnitaryInner
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFieldFrame

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitary
  CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut map_bar_comm
  primeFormUnitary mem_primeFormUnitary)
open CFSG.LieType.Chevalley (fixSubfield mem_fixSubfield)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

variable {p f : ℕ} {F : Type} [Field F]

theorem dvd_add_one_of_dvd_pow_three_add_one {x : ℕ} (h : 3 ∣ x ^ 3 + 1) : 3 ∣ x + 1 := by
  have h1 := Nat.pow_mod x 3 3
  rcases (by omega : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2) with h2 | h2 | h2 <;>
    simp [h2] at h1 <;> omega

theorem exists_fixed_cube_root [Finite F] (T : FrobData F) (y : GL (Fin 3) F)
    (hy : ∀ i j, T.τ ((y : Matrix (Fin 3) (Fin 3) F) i j) = (y : Matrix (Fin 3) (Fin 3) F) i j)
    {c : Fˣ} (hc : (c : F) ^ 3 = (y : Matrix (Fin 3) (Fin 3) F).det) {c' : F}
    (hy3 : (y : Matrix (Fin 3) (Fin 3) F) ^ 3 = c' • (1 : Matrix (Fin 3) (Fin 3) F))
    (hlift : (y : Matrix (Fin 3) (Fin 3) F) ^ 3 = (c : F) ^ 3 • (1 : Matrix (Fin 3) (Fin 3) F) →
      T.τ (c : F) = c) :
    ∃ ε : F, T.τ ε = ε ∧ ε ^ 3 = c' ∧ ε ≠ 0 := by
  set Y : Matrix (Fin 3) (Fin 3) F := (y : Matrix (Fin 3) (Fin 3) F) with hY
  have hyk : ∀ i j, Y i j ∈ fixSub T.τ := fun i j => mem_fixSub.2 (hy i j)
  have hfY : (T.τ : F →+* F).mapMatrix Y = Y := by
    ext i j
    exact hy i j
  have hc'fix : T.τ c' = c' := by
    have h1 : (T.τ : F →+* F).mapMatrix (Y ^ 3) = Y ^ 3 := by rw [map_pow, hfY]
    rw [hy3] at h1
    have h2 := congrFun (congrFun h1 0) 0
    simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using h2
  have hdet0 : Y.det ≠ 0 := by
    simpa [Matrix.GeneralLinearGroup.det] using (Matrix.GeneralLinearGroup.det y).ne_zero
  have hc'0 : c' ≠ 0 := by
    rintro rfl
    have h1 := congrArg Matrix.det hy3
    rw [zero_smul, Matrix.det_pow] at h1
    simp at h1
    exact hdet0 h1
  obtain ⟨ε, hε, hε3⟩ : ∃ ε ∈ fixSub T.τ, ε ^ 3 = c' := by
    rcases exists_cube_root_or_det_eq_of_subfield (fixSub T.τ) Y hyk (mem_fixSub.2 hc'fix) hy3
      with h | h
    · exact h
    · have hY3 : Y ^ 3 = (c : F) ^ 3 • (1 : Matrix (Fin 3) (Fin 3) F) := by rw [hy3, hc, h]
      exact ⟨c, mem_fixSub.2 (hlift hY3), by rw [hc, h]⟩
  refine ⟨ε, mem_fixSub.1 hε, hε3, ?_⟩
  rintro rfl
  apply hc'0
  rw [← hε3]
  norm_num

theorem isometry_scalar_mul (h : UnitaryFieldData p f F) {d : Fˣ} (hd : h.norm (d : F) = 1)
    (y : unitaryIsom3 h) :
    GeneralLinearGroup.scalar (Fin 3) d * (y : GL (Fin 3) F) ∈ unitaryIsom3 h :=
  mul_mem (scalar_mem_unitaryIsom3 h hd) y.2

theorem isometry_of_subfieldGL (h : UnitaryFieldData p f F) {e : ℕ} {k : Subfield F}
    (h₀ : UnitaryFieldData p e k) (hbar : ∀ c : k, (h₀.bar c : F) = h.bar c)
    {g₀ : GL (Fin 3) k} (hg : subfieldGL k 3 g₀ ∈ unitaryIsom3 h) :
    ((g₀ : Matrix (Fin 3) (Fin 3) k).map h₀.bar)ᵀ * (g₀ : Matrix (Fin 3) (Fin 3) k) = 1 := by
  have h1 := mem_unitaryIsom3.1 hg
  rw [coe_subfieldGL, map_subtype_map_bar h h₀ hbar 3, ← transpose_map, ← Matrix.map_mul] at h1
  refine Matrix.map_injective (f := (k.subtype : k → F)) Subtype.val_injective ?_
  change (((g₀ : Matrix (Fin 3) (Fin 3) k).map h₀.bar)ᵀ * g₀).map k.subtype =
    (1 : Matrix (Fin 3) (Fin 3) k).map k.subtype
  rw [h1, Matrix.map_one _ (map_zero _) (map_one _)]

theorem subfieldGL_mem_unitaryIsom3 (h : UnitaryFieldData p f F) {e : ℕ} {k : Subfield F}
    (h₀ : UnitaryFieldData p e k) (hbar : ∀ c : k, (h₀.bar c : F) = h.bar c)
    {g₀ : GL (Fin 3) k}
    (hg : ((g₀ : Matrix (Fin 3) (Fin 3) k).map h₀.bar)ᵀ * (g₀ : Matrix (Fin 3) (Fin 3) k) = 1) :
    subfieldGL k 3 g₀ ∈ unitaryIsom3 h := by
  rw [mem_unitaryIsom3, coe_subfieldGL, map_subtype_map_bar h h₀ hbar 3, ← transpose_map,
    ← Matrix.map_mul, hg, Matrix.map_one _ (map_zero _) (map_one _)]

theorem exists_fixed_unitary_frame [Finite F] (h : UnitaryFieldData p f F) (T : FrobData F)
    (hτ : orderOf T.τ = 3) (h3 : 3 ∣ p ^ f + 1) (y : unitaryIsom3 h)
    (hy : ∀ i j, T.τ (((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j) =
      ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j)
    {c : Fˣ} (hc : (c : F) ^ 3 = ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det) {c' : F}
    (hy3 : ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 =
      c' • (1 : Matrix (Fin 3) (Fin 3) F))
    (hlift : ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 =
      (c : F) ^ 3 • (1 : Matrix (Fin 3) (Fin 3) F) → T.τ (c : F) = c) :
    ∃ (P : unitaryIsom3 h) (u : Fin 3 → F),
      (∀ i j, T.τ (((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j) =
        ((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j) ∧
      ((((P : GL (Fin 3) F)⁻¹ : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) *
        ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          ((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal u := by
  classical
  set Y : Matrix (Fin 3) (Fin 3) F := ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hY
  obtain ⟨ε, hετ, hε3, hε0⟩ := exists_fixed_cube_root T (y : GL (Fin 3) F) hy hc hy3 hlift
  have hc'0 : c' ≠ 0 := hε3 ▸ pow_ne_zero 3 hε0
  have hNc' : h.norm c' = 1 := by
    have h1 := mem_unitaryIsom3.1 (pow_mem y.2 3)
    rw [Units.val_pow_eq_pow_val, hy3] at h1
    have h2 := congrFun (congrFun h1 0) 0
    simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply,
      Matrix.map_apply] at h2
    rw [UnitaryFieldData.norm, mul_comm]
    exact h2
  have hNε : h.norm ε = 1 := by
    have := norm_eq_one_of_pow_three h h3 (Units.mk0 ε hε0) (by simpa [hε3] using hNc')
    simpa using this
  have hNε' : h.norm ((((Units.mk0 ε hε0)⁻¹ : Fˣ)) : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, norm_inv_eq h, hNε, inv_one]
  set g : GL (Fin 3) F :=
    GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ε hε0)⁻¹ * (y : GL (Fin 3) F) with hg
  have hgU : g ∈ unitaryIsom3 h := isometry_scalar_mul h hNε' y
  have hgval : (g : Matrix (Fin 3) (Fin 3) F) = ε⁻¹ • Y := by
    rw [hg, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
  have hgfix : glAut T.τ g = g := by
    apply Units.ext
    rw [coe_glAut, hgval]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, hετ, hy i j]
  have hg3 : g ^ 3 = 1 := by
    have hM : (y : GL (Fin 3) F) ^ 3 = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c' hc'0) := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hy3, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.smul_one_eq_diagonal]
      rfl
    exact scalar_inv_mul_pow_three hM (u := Units.mk0 ε hε0) (Units.ext (by simp [hε3]))
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hτ3 : orderOf T.τ = 3 := hτ
  have h₀ := fixSubfield_unitaryFieldData h hp3 (by norm_num) hτ3
  have hbar := fixSubfield_unitaryFieldData_bar h hp3 (by norm_num) hτ3
  obtain ⟨f₀, hf₀⟩ := (dvd_and_card_fixSubfield_unitary h hp3 (by norm_num) hτ3).1
  have hq₀ : 3 ∣ p ^ (f / 3) + 1 := by
    apply dvd_add_one_of_dvd_pow_three_add_one
    rw [← pow_mul, Nat.div_mul_cancel ⟨f₀, hf₀⟩]
    exact h3
  obtain ⟨g₀, hg₀⟩ := exists_subfieldGL_eq_of_fixed (σ := T.τ) (n := 3) hgfix
  have hg₀U := isometry_of_subfieldGL h h₀ hbar (by rw [hg₀]; exact hgU)
  have hg₀3 : g₀ ^ 3 = 1 :=
    subfieldGL_injective (fixSubfield T.τ) 3 (by rw [map_pow, hg₀, hg3, map_one])
  let Y₀ : primeFormUnitary h₀ (idGram (fixSubfield T.τ) 3) :=
    ⟨g₀, by
      rw [mem_primeFormUnitary]
      simp only [idGram, Units.val_one, Matrix.mul_one]
      exact hg₀U⟩
  have hY₀3 : Y₀ ^ 3 = 1 := Subtype.ext hg₀3
  obtain ⟨P₀, hP₀⟩ := exists_unitary_conj_diag h₀ hp3 hq₀ (Subgroup.zpowers Y₀)
    (fun x hx z hz => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      exact ((Commute.refl Y₀).zpow_zpow m n).eq)
    (fun x hx => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
        _root_.zpow_natCast, hY₀3, _root_.one_zpow])
  have hP₀U : (((P₀ : GL (Fin 3) (fixSubfield T.τ)) : Matrix (Fin 3) (Fin 3) (fixSubfield T.τ)).map
      h₀.bar)ᵀ * ((P₀ : GL (Fin 3) (fixSubfield T.τ)) : Matrix (Fin 3) (Fin 3)
        (fixSubfield T.τ)) = 1 := by
    have := P₀.2
    rw [mem_primeFormUnitary] at this
    simpa [idGram] using this
  have hPU := subfieldGL_mem_unitaryIsom3 h h₀ hbar hP₀U
  set GP₀ : GL (Fin 3) (fixSubfield T.τ) := (P₀ : GL (Fin 3) (fixSubfield T.τ)) with hGP₀
  have hdiag : (((GP₀⁻¹ * g₀ * GP₀ : GL (Fin 3) (fixSubfield T.τ))) :
      Matrix (Fin 3) (Fin 3) (fixSubfield T.τ)).IsDiag := by
    have := hP₀ Y₀ (Subgroup.mem_zpowers Y₀)
    simpa using this
  set D₀ : Matrix (Fin 3) (Fin 3) (fixSubfield T.τ) :=
    (((GP₀⁻¹ * g₀ * GP₀ : GL (Fin 3) (fixSubfield T.τ))) :
      Matrix (Fin 3) (Fin 3) (fixSubfield T.τ)) with hD₀
  refine ⟨⟨subfieldGL (fixSubfield T.τ) 3 GP₀, hPU⟩, fun i => ε * ((D₀ i i : fixSubfield T.τ) : F),
    ?_, ?_⟩
  · intro i j
    exact (((GP₀ : GL (Fin 3) (fixSubfield T.τ)) : Matrix (Fin 3) (Fin 3) (fixSubfield T.τ))
      i j).2
  · set Pg := subfieldGL (fixSubfield T.τ) 3 with hPg
    have hD : ((Pg GP₀)⁻¹ * g * Pg GP₀ : GL (Fin 3) F) = Pg (GP₀⁻¹ * g₀ * GP₀) := by
      rw [map_mul, map_mul, map_inv, ← hg₀]
    have hmat : (((Pg GP₀)⁻¹ * g * Pg GP₀ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        Matrix.diagonal (fun i => ((D₀ i i : fixSubfield T.τ) : F)) := by
      rw [hD, hPg, coe_subfieldGL]
      ext i j
      by_cases hij : i = j
      · subst hij
        rw [Matrix.map_apply, Matrix.diagonal_apply_eq]
        rfl
      · have h0 : (((GP₀⁻¹ * g₀ * GP₀ : GL (Fin 3) (fixSubfield T.τ))) :
            Matrix (Fin 3) (Fin 3) (fixSubfield T.τ)) i j = 0 := hdiag hij
        rw [Matrix.diagonal_apply_ne _ hij, Matrix.map_apply, h0]
        rfl
    have hYg : Y = ε • (g : Matrix (Fin 3) (Fin 3) F) := by
      rw [hgval, smul_inv_smul₀ hε0]
    change ((((Pg GP₀)⁻¹ : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) * Y *
      ((Pg GP₀ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = _
    rw [hYg, Matrix.mul_smul, Matrix.smul_mul]
    simp only [Units.val_mul] at hmat
    rw [hmat]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField
