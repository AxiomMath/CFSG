module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRBase

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR.E2

open CFSG Subgroup CFSG.LieType.Chevalley

theorem not_isPGroup_of_odd_commute {G : Type*} [Group G] {t c : G} (hc : c * t = t * c)
    {m : ℕ} (hm : Odd m) (hcm : c ^ m = 1) (h1 : c ≠ 1) :
    ¬ IsPGroup 2 ↥(centralizer ({t} : Set G)) := by
  refine not_isPGroup_of_pow
    (g := (⟨c, mem_centralizer_singleton_iff.mpr hc⟩ : ↥(centralizer ({t} : Set G)))) hm ?_ ?_
  · apply Subtype.ext
    change c ^ m = 1
    exact hcm
  · intro h
    exact h1 (congrArg Subtype.val h)

theorem not_isPGroup_of_mem_closure_odd {G : Type*} [Group G] {t x : G}
    (hx : x ∈ closure {c : G | c * t = t * c ∧ Odd (orderOf c)}) (hx1 : x ≠ 1) :
    ¬ IsPGroup 2 ↥(centralizer ({t} : Set G)) := by
  intro hP
  apply hx1
  have hle : closure {c : G | c * t = t * c ∧ Odd (orderOf c)} ≤ ⊥ := by
    rw [closure_le]
    rintro c ⟨hct, hodd⟩
    rw [SetLike.mem_coe, mem_bot]
    by_contra hc1
    exact not_isPGroup_of_odd_commute hct hodd (pow_orderOf_eq_one c) hc1 hP
  exact mem_bot.mp (hle hx)

theorem uSL_mul_vSL_pow_three {F : Type*} [Field F] [CharP F 2] :
    ((uSL 1 : SL2 F) * vSL 1) ^ 3 = 1 := by
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_one]
  change (!![1, 1; 0, 1] * !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h2]

theorem uSL_mul_vSL_ne_one {F : Type*} [Field F] [CharP F 2] :
    ((uSL 1 : SL2 F) * vSL 1) ≠ 1 := by
  intro h
  have h00 := congrArg (fun g : SL2 F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  change (!![1, 1; 0, 1] * !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) 0 0 =
    (1 : Matrix (Fin 2) (Fin 2) F) 0 0 at h00
  simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero] at h00

theorem not_isPGroup_of_sl2 {G : Type*} [Group G] {F : Type*} [Field F] [CharP F 2]
    (ρ : SL2 F →* G) (hρ : Function.Injective ρ) {t : G} (hρt : ∀ s, ρ s * t = t * ρ s) :
    ¬ IsPGroup 2 ↥(centralizer ({t} : Set G)) := by
  refine not_isPGroup_of_odd_commute (hρt (uSL 1 * vSL 1)) (m := 3) ⟨1, rfl⟩ ?_ ?_
  · rw [← map_pow, uSL_mul_vSL_pow_three, map_one]
  · intro h
    exact uSL_mul_vSL_ne_one (hρ (h.trans (map_one ρ).symm))

theorem not_isPGroup_of_mulEquiv {Y G : Type*} [Group Y] [Group G] (e : Y ≃* G) (c : Y)
    (h : ¬ IsPGroup 2 ↥(centralizer ({e c} : Set G))) :
    ¬ IsPGroup 2 ↥(centralizer ({c} : Set Y)) := by
  intro hP
  apply h
  have hmem : ∀ y : ↥(centralizer ({e c} : Set G)),
      e.symm (y : G) ∈ centralizer ({c} : Set Y) := by
    intro y
    have hy : (y : G) * e c = e c * y := mem_centralizer_singleton_iff.mp y.2
    rw [mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy
  refine hP.of_injective ((e.symm.toMonoidHom.comp
    (centralizer ({e c} : Set G)).subtype).codRestrict _ hmem) ?_
  intro y z hyz
  have h' : e.symm (y : G) = e.symm z := congrArg Subtype.val hyz
  exact Subtype.ext (e.symm.injective h')

end CFSG.ComponentClassification.HarrisLit.L33.SR.E2
