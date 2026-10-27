module

public import CFSG.Quasithin.SteinbergBSLinearThreeRoot
public import CFSG.GH74.Generic.BProg.B2.GenLocL3Pair
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankBoundField
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X7a
  CFSG.ComponentClassification CFSG.Quasithin.SteinbergBS
open CFSG.GH74.Generic.BProg.B2.GenLocL3Pair (rt FullPair top_of_roots fullPair_trans)
open scoped MatrixGroups

section Roots

variable {F : Type} [Field F]

@[expose] noncomputable def rtHom (i j : Fin 3) (h : i ≠ j) :
    Multiplicative F →* projectiveSL 3 F where
  toFun s := rt i j h s.toAdd
  map_one' := by
    rw [rt, toAdd_one, SpecialLinearGroup.transvection_coeff_zero, map_one]
  map_mul' a b := by
    rw [rt, rt, rt, toAdd_mul, SpecialLinearGroup.transvection_add, map_mul]

theorem transvection_mem_unitriangular {i j : Fin 3} (h : i < j) (s : F) :
    SpecialLinearGroup.transvection h.ne s ∈ unitriangular 3 F := by
  rw [mem_unitriangular, SpecialLinearGroup.transvection_coe]
  refine ⟨fun k l hkl => ?_, fun k => ?_⟩
  · rw [Matrix.add_apply, one_apply_ne (ne_of_lt hkl).symm, zero_add, single_apply_of_ne]
    rintro ⟨rfl, rfl⟩
    exact absurd (h.trans hkl) (lt_irrefl _)
  · rw [Matrix.add_apply, one_apply_eq, single_apply_of_ne, add_zero]
    rintro ⟨rfl, rfl⟩
    exact lt_irrefl _ h

theorem rtHom_range_le_projUnitriangular {i j : Fin 3} (h : i < j) :
    (rtHom (F := F) i j h.ne).range ≤ projUnitriangular 3 F := by
  rintro _ ⟨s, rfl⟩
  exact ⟨_, transvection_mem_unitriangular h s.toAdd, rfl⟩

theorem card_range_rtHom {i j : Fin 3} (h : i < j) :
    Nat.card (rtHom (F := F) i j h.ne).range = Nat.card F := by
  have hinj : Function.Injective (rtHom (F := F) i j h.ne) := by
    intro a b hab
    have h1 := proj_injOn_unitriangular (transvection_mem_unitriangular h a.toAdd)
      (transvection_mem_unitriangular h b.toAdd) hab
    have h2 := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F) i j) h1
    simp only [SpecialLinearGroup.transvection_coe, Matrix.add_apply, one_apply_ne h.ne,
      single_apply_same, zero_add] at h2
    exact Multiplicative.toAdd.injective h2
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_congr Multiplicative.toAdd]

theorem isElemTwo_range_rtHom [CharP F 2] (i j : Fin 3) (h : i ≠ j) :
    IsElemTwo (rtHom (F := F) i j h).range := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨a, rfl⟩
    rw [← map_mul, ← map_one (rtHom i j h)]
    congr 1
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one, CharTwo.add_self_eq_zero]

theorem commute_transvection {i j k l : Fin 3} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) (s r : F) :
    Commute (SpecialLinearGroup.transvection hij s) (SpecialLinearGroup.transvection hkl r) := by
  have hm : (1 + single i j s : Matrix (Fin 3) (Fin 3) F) * (1 + single k l r) =
      (1 + single k l r) * (1 + single i j s) := by
    simp only [add_mul, mul_add, one_mul, mul_one, single_mul_single_of_ne _ _ _ _ hjk,
      single_mul_single_of_ne _ _ _ _ hli, add_zero]
    abel
  apply Subtype.ext
  simp [SpecialLinearGroup.transvection_coe, hm]

theorem commute_rt_one_zero_rt_one_two (s r : F) :
    Commute (rt (K := F) 1 0 (by decide) s) (rt 1 2 (by decide) r) :=
  (commute_transvection _ _ (by decide) (by decide) s r).map (proj 3 F)

theorem commute_rt_two_one_rt_zero_one (s r : F) :
    Commute (rt (K := F) 2 1 (by decide) s) (rt 0 1 (by decide) r) :=
  (commute_transvection _ _ (by decide) (by decide) s r).map (proj 3 F)

theorem rt_mem_projUnitriangular {i j : Fin 3} (h : i < j) (s : F) :
    rt i j h.ne s ∈ projUnitriangular 3 F :=
  rtHom_range_le_projUnitriangular h ⟨Multiplicative.ofAdd s, rfl⟩

theorem eq_top_of_projUnitriangular_le {H : Subgroup (projectiveSL 3 F)}
    (hU : projUnitriangular 3 F ≤ H) (h10 : ∀ s : F, rt 1 0 (by decide) s ∈ H)
    (h21 : ∀ s : F, rt 2 1 (by decide) s ∈ H) : H = ⊤ := by
  have h01 : FullPair H 0 1 (by decide) :=
    ⟨fun s => hU (rt_mem_projUnitriangular (by decide) s), h10⟩
  have h12 : FullPair H 1 2 (by decide) :=
    ⟨fun s => hU (rt_mem_projUnitriangular (by decide) s), h21⟩
  have h02 : FullPair H 0 2 (by decide) := fullPair_trans (by decide) h01 h12
  refine top_of_roots fun i j hij s => ?_
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact h01.1 s | exact h01.2 s | exact h12.1 s | exact h12.2 s | exact h02.1 s
    | exact h02.2 s

end Roots

section Center

variable {F : Type} [Field F]

theorem semilinear_apply_center {A : GL (Fin 3) F}
    (hA : ∀ i j : Fin 3, j < i → (A : Matrix (Fin 3) (Fin 3) F) i j = 0) (σ : F ≃+* F) (y : F) :
    (conjAut 3 F A * fieldAut 3 F σ) (proj 3 F (up3 0 y 0)) =
      proj 3 F (up3 0 ((A : Matrix (Fin 3) (Fin 3) F) 0 0 *
        ((A : Matrix (Fin 3) (Fin 3) F) 2 2)⁻¹ * σ y) 0) := by
  have h22 : (A : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 := diag_ne_zero_of_upperTriangular hA 2
  rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  set c := (A : Matrix (Fin 3) (Fin 3) F) 0 0 * ((A : Matrix (Fin 3) (Fin 3) F) 2 2)⁻¹ * σ y
  have hc22 :
      c * (A : Matrix (Fin 3) (Fin 3) F) 2 2 = (A : Matrix (Fin 3) (Fin 3) F) 0 0 * σ y := by
    simp only [c]
    field_simp
  have hAi : (A : Matrix (Fin 3) (Fin 3) F) * ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have key : (A : Matrix (Fin 3) (Fin 3) F) *
      (SpecialLinearGroup.map σ.toRingHom (up3 0 y 0) : Matrix (Fin 3) (Fin 3) F) =
      (up3 0 c 0 : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) := by
    rw [SpecialLinearGroup.map_apply_coe, up3_coe, up3_coe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upMat, Matrix.mul_apply, Fin.sum_univ_three, RingHom.mapMatrix_apply,
        hA 1 0 (by decide), hA 2 0 (by decide), hA 2 1 (by decide)]
    first | linear_combination hc22 | linear_combination -hc22
  rw [key, Matrix.mul_assoc, hAi, Matrix.mul_one]

theorem exists_center_formula [Finite F] [CharP F 2] {α : MulAut (projectiveSL 3 F)}
    (hα : (projUnitriangular 3 F).map α.toMonoidHom = projUnitriangular 3 F) :
    ∃ (c : F) (σ : F ≃+* F), ∀ y : F,
      α (proj 3 F (up3 0 y 0)) = proj 3 F (up3 0 (c * σ y) 0) := by
  by_cases hs : α ∈ semilinearAutGroup 3 F
  · obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.mp hs
    exact ⟨_, σ, semilinear_apply_center (upperTriangular_of_semilinear_normalizes hα) σ⟩
  · obtain ⟨A, σ, hA, rfl⟩ := exists_eq_semilinear_mul_gammaZero hα hs
    refine ⟨(A : Matrix (Fin 3) (Fin 3) F) 0 0 * ((A : Matrix (Fin 3) (Fin 3) F) 2 2)⁻¹, σ,
      fun y => ?_⟩
    rw [MulAut.mul_apply, gammaZero_apply, zero_mul, add_zero]
    exact semilinear_apply_center hA σ y

theorem center_trichotomy [Finite F] [CharP F 2] {α β : MulAut (projectiveSL 3 F)}
    (hα : (projUnitriangular 3 F).map α.toMonoidHom = projUnitriangular 3 F)
    (hβ : (projUnitriangular 3 F).map β.toMonoidHom = projUnitriangular 3 F)
    (hα2 : ∀ y : F, α (α (proj 3 F (up3 0 y 0))) = proj 3 F (up3 0 y 0))
    (hβ2 : ∀ y : F, β (β (proj 3 F (up3 0 y 0))) = proj 3 F (up3 0 y 0))
    (hαβ : ∀ y : F, α (β (α (β (proj 3 F (up3 0 y 0))))) = proj 3 F (up3 0 y 0)) :
    (∀ y : F, α (proj 3 F (up3 0 y 0)) = proj 3 F (up3 0 y 0)) ∨
      (∀ y : F, β (proj 3 F (up3 0 y 0)) = proj 3 F (up3 0 y 0)) ∨
      ∀ y : F, α (proj 3 F (up3 0 y 0)) = β (proj 3 F (up3 0 y 0)) := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨c, σ, hc⟩ := exists_center_formula hα
  obtain ⟨d, τ, hd⟩ := exists_center_formula hβ
  have inj : ∀ {a b : F}, proj 3 F (up3 0 a 0) = proj 3 F (up3 0 b 0) → a = b :=
    fun h => (proj_up3_inj h).2.1
  have e1 : ∀ y, c * σ (c * σ y) = y := fun y => inj (by rw [← hα2 y, hc, hc])
  have e2 : ∀ y, d * τ (d * τ y) = y := fun y => inj (by rw [← hβ2 y, hd, hd])
  have e3 : ∀ y, c * σ (d * τ (c * σ (d * τ y))) = y := fun y =>
    inj (by rw [← hαβ y, hd, hc, hd, hc])
  have invol : ∀ {c : F} {σ : F ≃+* F}, (∀ y, c * σ (c * σ y) = y) →
      c * σ c = 1 ∧ σ * σ = 1 := by
    intro c σ e
    have h1 : c * σ c = 1 := by simpa using e 1
    refine ⟨h1, RingEquiv.ext fun y => ?_⟩
    have := e y
    rw [map_mul, ← mul_assoc, h1, one_mul] at this
    exact this
  have sq_one : ∀ {a : F}, a * a = 1 → a = 1 := by
    intro a ha
    rcases mul_self_eq_one_iff.mp ha with h | h
    · exact h
    · rw [h, CharTwo.neg_eq]
  obtain ⟨hc1, hσ2⟩ := invol e1
  obtain ⟨hd1, hτ2⟩ := invol e2
  have hσσ : ∀ y, σ (σ y) = y := fun y => by
    simpa using congrArg (fun ρ : F ≃+* F => ρ y) hσ2
  by_cases hσ : σ = 1
  · subst hσ
    have : c = 1 := sq_one (by simpa using hc1)
    left
    intro y
    rw [hc, this, one_mul]
    rfl
  by_cases hτ : τ = 1
  · subst hτ
    have : d = 1 := sq_one (by simpa using hd1)
    right; left
    intro y
    rw [hd, this, one_mul]
    rfl
  have hστ : σ = τ := CFSG.ProperTwoGeneratedCore.Lemma37.ringEquiv_eq_of_involution hσ hσ2 hτ hτ2
  subst hστ
  right; right
  have hcd : c * σ d = 1 := by
    have h := e3 1
    simp only [map_mul, map_one, mul_one, hσσ] at h
    exact sq_one (by linear_combination h)
  have hcd' : c = d := by
    have hc0 : c ≠ 0 := left_ne_zero_of_mul_eq_one hc1
    have : σ c = σ d := mul_left_cancel₀ hc0 (hc1.trans hcd.symm)
    exact σ.injective this
  intro y
  rw [hc, hd, hcd']
