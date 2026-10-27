module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Eight2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

namespace TwA5Eight

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
open CFSG.LocalAnalysis.ComponentInitial

variable {F : Type} [Field F] (h : UnitaryFieldData 2 3 F)

theorem mem_rootsOfUnity_three_val {a : rootsOfUnity 3 F} : ((a : Fˣ) : F) ^ 3 = 1 := by
  have := (mem_rootsOfUnity (M := F) 3 (a : Fˣ)).mp a.2
  simpa using congrArg (fun u : Fˣ => (u : F)) this

theorem twA5Entries_scalar (a : Fˣ) (haF : (a : F) ^ 3 = 1) :
    twA5Entries (F := F) a 1 1 1 = fun _ => (a : F) := by
  funext i
  fin_cases i <;> simp [twA5Entries]
  · have h5 : (a : F) ^ 5 = (a : F) ^ 2 := by
      rw [show (5 : ℕ) = 2 + 3 by norm_num, pow_add, haF, mul_one]
    rw [h5, show (a : F) ^ 2 = (a : F) * (a : F) by ring]
    exact inv_eq_of_mul_eq_one_right (by
      calc (a : F) * (a : F) * (a : F) = (a : F) ^ 3 := by ring
        _ = 1 := haF)

theorem twA5ScalarParam_mem (a : rootsOfUnity 3 F) :
    (a : Fˣ) ^ 9 = 1 ∧ (1 : Fˣ) ^ 3 = 1 ∧ (1 : Fˣ) ^ 3 = 1 ∧ (1 : Fˣ) ^ 3 = 1 := by
  refine ⟨?_, by simp, by simp, by simp⟩
  have ha : (a : Fˣ) ^ 3 = 1 := (mem_rootsOfUnity (M := F) 3 (a : Fˣ)).mp a.2
  rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, ha, one_pow]

noncomputable abbrev twA5ScalarParam (a : rootsOfUnity 3 F) : twA5Param (F := F) :=
  ⟨(a, 1, 1, 1), (mem_twA5Param).2 (twA5ScalarParam_mem (F := F) a)⟩

@[simp] theorem twA5ScalarParam_val (a : rootsOfUnity 3 F) :
    (twA5ScalarParam (F := F) a : Fˣ × Fˣ × Fˣ × Fˣ) = ((a : Fˣ), 1, 1, 1) := rfl

theorem twA5Hom_apply (x : twA5Param (F := F)) :
    twA5Hom h x =
      twA5Diag h x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2
        (norm_eq_one_of_pow_nine h (coe_pow_eq_one (mem_twA5Param.mp x.2).1))
        (norm_eq_one_of_pow_three h (coe_pow_eq_one (mem_twA5Param.mp x.2).2.1))
        (norm_eq_one_of_pow_three h (coe_pow_eq_one (mem_twA5Param.mp x.2).2.2.1))
        (norm_eq_one_of_pow_three h (coe_pow_eq_one (mem_twA5Param.mp x.2).2.2.2)) := rfl

theorem twA5Hom_scalarParam_mem (a : rootsOfUnity 3 F) :
    twA5Hom h (twA5ScalarParam (F := F) a) ∈ unitaryScalars h 6 := by
  rw [mem_unitaryScalars]
  refine ⟨(a : Fˣ), ?_, ?_, ?_⟩
  · apply norm_eq_one_of_pow_three h
    simpa using mem_rootsOfUnity_three_val (F := F) (a := a)
  · have ha : (a : Fˣ) ^ 3 = 1 := (mem_rootsOfUnity (M := F) 3 (a : Fˣ)).mp a.2
    rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, ha, one_pow]
  · rw [twA5Hom_apply]
    unfold twA5Diag
    change ((diagSU h (twA5Entries (F := F) (a : Fˣ) 1 1 1) _ _ : unitarySU 2 3 F 6) :
      GL (Fin 6) F) = Matrix.GeneralLinearGroup.scalar (Fin 6) (a : Fˣ)
    apply Units.ext
    rw [coe_diagSU,
      twA5Entries_scalar (F := F) (a := (a : Fˣ)) (mem_rootsOfUnity_three_val (F := F))]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply, Matrix.scalar_apply]

theorem twA5ScalarParam_injective : Function.Injective (twA5ScalarParam (F := F)) := by
  intro a b hab
  have h := congrArg (fun x : twA5Param (F := F) => (x : Fˣ × Fˣ × Fˣ × Fˣ).1) hab
  simpa [twA5ScalarParam] using h

theorem card_unitaryScalars_six : Nat.card (unitaryScalars h 6) = 3 := by
  rw [card_unitaryScalars h (by norm_num)]
  norm_num

theorem card_ker_twA5Proj (hcard : Nat.card F = 64) :
    Nat.card ((unitaryProj h 6).ker.comap (twA5Hom h)) = 3 := by
  letI : Finite F := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let φ : twA5Param (F := F) →* unitaryPSU h 6 := (unitaryProj h 6).comp (twA5Hom h)
  have hker : φ.ker = (unitaryProj h 6).ker.comap (twA5Hom h) := rfl
  rw [← hker]
  apply le_antisymm
  · have hmem : ∀ x : φ.ker, twA5Hom h x.1 ∈ unitaryScalars h 6 := by
      intro x
      have hx : (unitaryProj h 6) (twA5Hom h x.1) = 1 := by
        have := x.2
        change φ x.1 = 1 at this
        simpa [φ] using this
      have hy : twA5Hom h x.1 ∈ (unitaryProj h 6).ker := MonoidHom.mem_ker.mpr hx
      rwa [ker_unitaryProj] at hy
    let g : φ.ker → unitaryScalars h 6 := fun x => ⟨twA5Hom h x.1, hmem x⟩
    have hinj : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      apply twA5Hom_injective h
      have hval := congrArg (fun z : unitaryScalars h 6 => (z : unitarySU 2 3 F 6)) hxy
      simpa [g] using hval
    have hle := Nat.card_le_card_of_injective g hinj
    rwa [card_unitaryScalars_six h] at hle
  · let g : rootsOfUnity 3 F → φ.ker := fun a =>
      ⟨twA5ScalarParam (F := F) a, by
        change φ (twA5ScalarParam (F := F) a) = 1
        exact MonoidHom.mem_ker.mpr (by
          change (unitaryProj h 6) (twA5Hom h (twA5ScalarParam (F := F) a)) = 1
          exact MonoidHom.mem_ker.mp (by
            rw [ker_unitaryProj]
            exact twA5Hom_scalarParam_mem h a))⟩
    have hinj : Function.Injective g := by
      intro a b hab
      apply twA5ScalarParam_injective
      have h := congrArg (fun x : φ.ker => (x.1 : twA5Param (F := F))) hab
      simpa [g] using h
    have h3 : Nat.card (rootsOfUnity 3 F) = 3 := by
      apply CFSG.LinearGroups.card_rootsOfUnity_of_dvd
      rw [hcard]
      norm_num
    have hle := Nat.card_le_card_of_injective g hinj
    rwa [h3] at hle

theorem card_twA5Bar (hcard : Nat.card F = 64) :
    Nat.card ((twA5Hom h).range.map (unitaryProj h 6)) = 81 := by
  let φ : twA5Param (F := F) →* unitaryPSU h 6 := (unitaryProj h 6).comp (twA5Hom h)
  have hcard' := Subgroup.card_eq_card_quotient_mul_card_subgroup (φ.ker)
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at hcard'
  have hker : Nat.card φ.ker = 3 := card_ker_twA5Proj h hcard
  have hparam : Nat.card (twA5Param (F := F)) = 243 := card_twA5Param (F := F) hcard
  rw [hker, hparam] at hcard'
  have hrange : φ.range = (twA5Hom h).range.map (unitaryProj h 6) := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_map]
  rw [hrange] at hcard'
  omega

theorem twA5Param_pow_three (x : twA5Param (F := F)) :
    ∃ a : rootsOfUnity 3 F, x ^ 3 = twA5ScalarParam (F := F) a := by
  let a : rootsOfUnity 3 F := ⟨x.1.1 ^ 3, by
    rw [mem_rootsOfUnity]
    have hx := (mem_twA5Param.mp x.2).1
    rw [show (x.1.1 ^ 3) ^ 3 = x.1.1 ^ 9 by
      rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul], hx]⟩
  have h2F : (x.1.2.1 : F) * x.1.2.1 * x.1.2.1 = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) (mem_twA5Param.mp x.2).2.1
    simpa [pow_succ, pow_two, mul_assoc] using this
  have h3F : (x.1.2.2.1 : F) * x.1.2.2.1 * x.1.2.2.1 = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) (mem_twA5Param.mp x.2).2.2.1
    simpa [pow_succ, pow_two, mul_assoc] using this
  have h4F : (x.1.2.2.2 : F) * x.1.2.2.2 * x.1.2.2.2 = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) (mem_twA5Param.mp x.2).2.2.2
    simpa [pow_succ, pow_two, mul_assoc] using this
  have h2F' : (x.1.2.1 : F) * (x.1.2.1 * x.1.2.1) = 1 := by
    rw [← mul_assoc]; exact h2F
  have h3F' : (x.1.2.2.1 : F) * (x.1.2.2.1 * x.1.2.2.1) = 1 := by
    rw [← mul_assoc]; exact h3F
  have h4F' : (x.1.2.2.2 : F) * (x.1.2.2.2 * x.1.2.2.2) = 1 := by
    rw [← mul_assoc]; exact h4F
  refine ⟨a, ?_⟩
  apply Subtype.ext
  ext <;> simp [twA5ScalarParam, a, h2F', h3F', h4F', pow_succ, pow_two, mul_assoc]

theorem twA5Hom_pow_three_mem (x : twA5Param (F := F)) :
    (twA5Hom h x) ^ 3 ∈ unitaryScalars h 6 := by
  obtain ⟨a, ha⟩ := twA5Param_pow_three (F := F) x
  rw [← map_pow, ha]
  exact twA5Hom_scalarParam_mem h a

theorem twA5Bar_isElemAbelian (hcard : Nat.card F = 64) :
    IsElemAbelian 3 ((twA5Hom h).range.map (unitaryProj h 6)) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨a, ha, hx⟩ := Subgroup.mem_map.1 x.2
    obtain ⟨b, hb, hy⟩ := Subgroup.mem_map.1 y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hx, ← hy]
    obtain ⟨p, hp⟩ := MonoidHom.mem_range.1 ha
    obtain ⟨q, hq⟩ := MonoidHom.mem_range.1 hb
    rw [← hp, ← hq]
    calc
      (unitaryProj h 6) (twA5Hom h p) * (unitaryProj h 6) (twA5Hom h q)
          = (unitaryProj h 6) (twA5Hom h (p * q)) := by rw [map_mul, map_mul]
      _ = (unitaryProj h 6) (twA5Hom h (q * p)) := by rw [mul_comm p q]
      _ = (unitaryProj h 6) (twA5Hom h q) * (unitaryProj h 6) (twA5Hom h p) := by
        rw [map_mul, map_mul]
  · intro x hx
    obtain ⟨a, ha, hx⟩ := Subgroup.mem_map.1 hx
    rw [← hx]
    obtain ⟨p, hp⟩ := MonoidHom.mem_range.1 ha
    rw [← hp]
    change ((unitaryProj h 6) (twA5Hom h p)) ^ 3 = 1
    rw [← map_pow]
    have hmem : (twA5Hom h p) ^ 3 ∈ (unitaryProj h 6).ker := by
      rw [ker_unitaryProj]
      exact twA5Hom_pow_three_mem h p
    exact MonoidHom.mem_ker.mp hmem

end TwA5Eight

end CFSG.LocalAnalysis.GLTheoremA.Y10F
