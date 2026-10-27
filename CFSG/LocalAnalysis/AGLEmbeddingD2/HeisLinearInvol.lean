module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareLinear
public import CFSG.Timmesfeld.ARS.LinearLevis

public section

namespace CFSG.AGLEmbeddingD2.HeisLinear

open CFSG.LieType.Universal.SpecialLinear CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbeddingD2.ParabLevi CFSG.AGLEmbeddingD2.SquareLinear CFSG.Timmesfeld

section Tv

variable {m : ℕ} {F : Type} [Field F]

theorem tv_castSucc_succ_mem_rankOne (i : Fin m) (c : F) :
    tv i.castSucc i.succ c ∈ rankOne (rootDatum m F).rootGroup i := by
  rw [rankOne_eq_range_blockHom]
  refine ⟨sl2Upper c, ?_⟩
  rw [blockHom_upper, CFSG.Timmesfeld.ARS.Linear.x_sroot]

theorem tv_succ_castSucc_mem_rankOne (i : Fin m) (c : F) :
    tv i.succ i.castSucc c ∈ rankOne (rootDatum m F).rootGroup i := by
  rw [rankOne_eq_range_blockHom]
  refine ⟨sl2Lower c, ?_⟩
  rw [blockHom_lower, CFSG.Timmesfeld.ARS.Linear.x_neg_sroot]

end Tv

section SL4

variable {F : Type*} [Field F]

theorem map_tv {n : ℕ} {R S : Type*} [Field R] [Field S] (φ : R →+* S) (i j : Fin n) (c : R) :
    Matrix.SpecialLinearGroup.map φ (tv i j c) = tv i j (φ c) := by
  by_cases h : i = j
  · subst h
    simp [tv]
  · rw [tv_of_ne h, tv_of_ne h]
    refine Subtype.ext ?_
    simp [Matrix.SpecialLinearGroup.transvection_coe]

@[expose] noncomputable def involX : Matrix.SpecialLinearGroup (Fin 4) F :=
  tv 0 1 1 * tv 2 3 1 * tv 2 1 1

@[expose] noncomputable def involY : Matrix.SpecialLinearGroup (Fin 4) F :=
  tv 1 2 1 * tv 1 0 1 * tv 3 2 1

theorem map_involX {R S : Type*} [Field R] [Field S] (φ : R →+* S) :
    Matrix.SpecialLinearGroup.map φ (involX : Matrix.SpecialLinearGroup (Fin 4) R) = involX := by
  simp only [involX, map_mul, map_tv, map_one]

theorem map_involY {R S : Type*} [Field R] [Field S] (φ : R →+* S) :
    Matrix.SpecialLinearGroup.map φ (involY : Matrix.SpecialLinearGroup (Fin 4) R) = involY := by
  simp only [involY, map_mul, map_tv, map_one]

theorem involX_sq [CharP F 2] : (involX : Matrix.SpecialLinearGroup (Fin 4) F) ^ 2 = 1 := by
  have h : (involX : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ^ 2 = 1 := by decide
  have := congrArg (Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_refl 2) F)) h
  rwa [map_pow, map_involX, map_one] at this

theorem involY_sq [CharP F 2] : (involY : Matrix.SpecialLinearGroup (Fin 4) F) ^ 2 = 1 := by
  have h : (involY : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ^ 2 = 1 := by decide
  have := congrArg (Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_refl 2) F)) h
  rwa [map_pow, map_involY, map_one] at this

theorem involXY_pow_five [CharP F 2] :
    ((involX : Matrix.SpecialLinearGroup (Fin 4) F) * involY) ^ 5 = 1 := by
  have h : ((involX : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) * involY) ^ 5 = 1 := by decide
  have := congrArg (Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_refl 2) F)) h
  rwa [map_pow, map_mul, map_involX, map_involY, map_one] at this

theorem involXY_ne_one [CharP F 2] :
    (involX : Matrix.SpecialLinearGroup (Fin 4) F) * involY ≠ 1 := by
  have h : (involX : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) * involY ≠ 1 := by decide
  intro h'
  apply h
  have hinj : Function.Injective (Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_refl 2) F) :
      Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) → Matrix.SpecialLinearGroup (Fin 4) F) := by
    intro A B hAB
    refine Subtype.ext (Matrix.map_injective (ZMod.castHom (dvd_refl 2) F).injective ?_)
    simpa using congrArg Subtype.val hAB
  apply hinj
  rw [map_mul, map_involX, map_involY, map_one]
  exact h'

end SL4

section Levi4

variable {m : ℕ} {F : Type} [Field F]

@[expose] def offsetEmb (a : ℕ) (ha : a + 3 ≤ m) : Fin 4 ↪ Fin (m + 1) where
  toFun t := ⟨a + t.val, by omega⟩
  inj' s t h := Fin.ext (by simpa using congrArg Fin.val h)

@[simp] theorem offsetEmb_val (a : ℕ) (ha : a + 3 ≤ m) (t : Fin 4) :
    (offsetEmb a ha t).val = a + t.val := rfl

theorem tv_offset_mem_leviM {a : ℕ} (ha : a + 3 ≤ m) {t : ℕ} (ht : t < 3) {p q : Fin 4}
    (hpq : (p.val = t ∧ q.val = t + 1) ∨ (p.val = t + 1 ∧ q.val = t)) (c : F) :
    tv (offsetEmb a ha p) (offsetEmb a ha q) c ∈
      leviM (rootDatum m F) {k : Fin m | a ≤ k.val ∧ k.val < a + 3} := by
  have hi : (⟨a + t, by omega⟩ : Fin m) ∈ {k : Fin m | a ≤ k.val ∧ k.val < a + 3} := by
    show a ≤ a + t ∧ a + t < a + 3
    omega
  refine rankOne_le_leviM hi ?_
  rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · have e1 : offsetEmb a ha p = (⟨a + t, by omega⟩ : Fin m).castSucc :=
      Fin.ext (by simp [hp])
    have e2 : offsetEmb a ha q = (⟨a + t, by omega⟩ : Fin m).succ :=
      Fin.ext (by simp only [offsetEmb_val, Fin.val_succ, hq]; omega)
    rw [e1, e2]
    exact tv_castSucc_succ_mem_rankOne _ c
  · have e1 : offsetEmb a ha p = (⟨a + t, by omega⟩ : Fin m).succ :=
      Fin.ext (by simp only [offsetEmb_val, Fin.val_succ, hp]; omega)
    have e2 : offsetEmb a ha q = (⟨a + t, by omega⟩ : Fin m).castSucc :=
      Fin.ext (by simp [hq])
    rw [e1, e2]
    exact tv_succ_castSucc_mem_rankOne _ c

theorem exists_involutions_five [CharP F 2] {a : ℕ} (ha : a + 3 ≤ m) :
    ∃ x y : Matrix.SpecialLinearGroup (Fin (m + 1)) F,
      x ∈ leviM (rootDatum m F) {k : Fin m | a ≤ k.val ∧ k.val < a + 3} ∧
      y ∈ leviM (rootDatum m F) {k : Fin m | a ≤ k.val ∧ k.val < a + 3} ∧
      x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ (x * y) ^ 5 = 1 ∧ x * y ≠ 1 := by
  set e := offsetEmb a ha
  have hX : CFSG.Timmesfeld.ARS.Linear.blockHom F e involX =
      tv (e 0) (e 1) 1 * tv (e 2) (e 3) 1 * tv (e 2) (e 1) 1 := by
    simp only [involX, map_mul,
      CFSG.Timmesfeld.ARS.Linear.blockHom_tv _ _ (by decide : (0 : Fin 4) ≠ 1),
      CFSG.Timmesfeld.ARS.Linear.blockHom_tv _ _ (by decide : (2 : Fin 4) ≠ 3),
      CFSG.Timmesfeld.ARS.Linear.blockHom_tv _ _ (by decide : (2 : Fin 4) ≠ 1)]
  have hY : CFSG.Timmesfeld.ARS.Linear.blockHom F e involY =
      tv (e 1) (e 2) 1 * tv (e 1) (e 0) 1 * tv (e 3) (e 2) 1 := by
    simp only [involY, map_mul,
      CFSG.Timmesfeld.ARS.Linear.blockHom_tv _ _ (by decide : (1 : Fin 4) ≠ 2),
      CFSG.Timmesfeld.ARS.Linear.blockHom_tv _ _ (by decide : (1 : Fin 4) ≠ 0),
      CFSG.Timmesfeld.ARS.Linear.blockHom_tv _ _ (by decide : (3 : Fin 4) ≠ 2)]
  refine ⟨CFSG.Timmesfeld.ARS.Linear.blockHom F e involX,
    CFSG.Timmesfeld.ARS.Linear.blockHom F e involY, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hX]
    exact mul_mem (mul_mem (tv_offset_mem_leviM ha (t := 0) (by norm_num) (by simp) 1)
      (tv_offset_mem_leviM ha (t := 2) (by norm_num) (by simp) 1))
      (tv_offset_mem_leviM ha (t := 1) (by norm_num) (by simp) 1)
  · rw [hY]
    exact mul_mem (mul_mem (tv_offset_mem_leviM ha (t := 1) (by norm_num) (by simp) 1)
      (tv_offset_mem_leviM ha (t := 0) (by norm_num) (by simp) 1))
      (tv_offset_mem_leviM ha (t := 2) (by norm_num) (by simp) 1)
  · rw [← map_pow, involX_sq, map_one]
  · rw [← map_pow, involY_sq, map_one]
  · rw [← map_mul, ← map_pow, involXY_pow_five, map_one]
  · rw [← map_mul]
    intro h
    exact involXY_ne_one
      (CFSG.Timmesfeld.ARS.Linear.blockHom_injective F e (h.trans (map_one _).symm))

end Levi4

end CFSG.AGLEmbeddingD2.HeisLinear
