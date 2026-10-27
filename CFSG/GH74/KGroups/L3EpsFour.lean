module

public import CFSG.GH74.KGroups.L3EpsSylow

public section

namespace CFSG.GH74.KGroups.L3Eps

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

section Abstract

variable {X Y : Type*} [Group X] [Group Y]

theorem four_of_d8 {Ĝ : Type*} [Group Ĝ] [Finite Y] (π : Ĝ →* Y) {S : Subgroup Y} (hS : IsPGroup 2 S)
    (hmax : ∀ T : Subgroup Y, IsPGroup 2 T → S ≤ T → T ≤ S) {e r : Ĝ} (he : e ^ 4 = 1) (hr : r ^ 2 = 1)
    (hre : r * e * r⁻¹ = e⁻¹) (hinj : ∀ a b : Ĝ, a ^ 4 = 1 → b ^ 4 = 1 → π a = π b → a = b)
    (h1 : e * e ≠ 1) (h2 : r ≠ 1) (h3 : e * e ≠ r) :
    ∃ a ∈ S, ∃ b ∈ S, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  have hD : IsPGroup 2 (Subgroup.closure {e, r}) := isPGroup_closure_dihedral he hr hre
  obtain ⟨x, hx⟩ := exists_conj_le_of_isPGroup hS hmax (hD.map π)
  have hee : e * e ∈ Subgroup.closure {e, r} :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert _ _))
  have hrD : r ∈ Subgroup.closure {e, r} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have he4 : (e * e) * (e * e) = 1 := by
    have : e ^ 4 = (e * e) * (e * e) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    rw [← this]
    exact he
  have hr2 : r * r = 1 := by rw [← pow_two]; exact hr
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have hcomm : (e * e) * r = r * (e * e) := by
    have h4 : r * (e * e) * r⁻¹ = (e * e)⁻¹ := by
      calc r * (e * e) * r⁻¹ = (r * e * r⁻¹) * (r * e * r⁻¹) := by group
        _ = e⁻¹ * e⁻¹ := by rw [hre]
        _ = (e * e)⁻¹ := by group
    have h5 : (e * e)⁻¹ = e * e := inv_eq_of_mul_eq_one_right he4
    rw [h5] at h4
    calc (e * e) * r = (r * (e * e) * r⁻¹) * r := by rw [h4]
      _ = r * (e * e) := by group
  have hee4 : (e * e) ^ 4 = 1 := by
    have : (e * e) ^ 4 = ((e * e) * (e * e)) * ((e * e) * (e * e)) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    rw [this, he4, one_mul]
  have hr4 : r ^ 4 = 1 := by
    have : r ^ 4 = (r * r) * (r * r) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    rw [this, hr2, one_mul]
  have hconj1 : ∀ y : Y, x⁻¹ * y * x = 1 → y = 1 := fun y h => by
    calc y = x * (x⁻¹ * y * x) * x⁻¹ := by group
      _ = 1 := by rw [h]; group
  refine ⟨x⁻¹ * π (e * e) * x, hx _ ⟨e * e, hee, rfl⟩, x⁻¹ * π r * x, hx _ ⟨r, hrD, rfl⟩, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · calc x⁻¹ * π (e * e) * x * (x⁻¹ * π (e * e) * x) = x⁻¹ * π ((e * e) * (e * e)) * x := by
          simp only [map_mul]; group
      _ = 1 := by rw [he4]; simp
  · calc x⁻¹ * π r * x * (x⁻¹ * π r * x) = x⁻¹ * π (r * r) * x := by simp only [map_mul]; group
      _ = 1 := by rw [hr2]; simp
  · calc x⁻¹ * π (e * e) * x * (x⁻¹ * π r * x) = x⁻¹ * π ((e * e) * r) * x := by
          simp only [map_mul]; group
      _ = x⁻¹ * π (r * (e * e)) * x := by rw [hcomm]
      _ = x⁻¹ * π r * x * (x⁻¹ * π (e * e) * x) := by simp only [map_mul]; group
  · intro h
    apply h1
    exact hinj _ _ hee4 (by simp) (by rw [hconj1 _ h, map_one])
  · intro h
    apply h2
    exact hinj _ _ hr4 (by simp) (by rw [hconj1 _ h, map_one])
  · intro h
    apply h3
    refine hinj _ _ hee4 hr4 ?_
    have := congrArg (fun y : Y => x * y * x⁻¹) h
    simpa [mul_assoc] using this

end Abstract

section Transport

variable {X Y : Type*} [Group X] [Group Y]

theorem four_of_mulEquiv (e : X ≃* Y)
    (hY : ∀ S' : Subgroup Y, IsPGroup 2 S' →
      (∀ T : Subgroup Y, IsPGroup 2 T → S' ≤ T → T ≤ S') →
      ∃ a ∈ S', ∃ b ∈ S', a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b)
    {S : Subgroup X} (hS : IsPGroup 2 S) (hmax : ∀ T : Subgroup X, IsPGroup 2 T → S ≤ T → T ≤ S) :
    ∃ a ∈ S, ∃ b ∈ S, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  obtain ⟨hS', hmax'⟩ := isMaxPGroup_map e hS hmax
  obtain ⟨a', ha', b', hb', h1, h2, h3, h4, h5, h6⟩ := hY _ hS' hmax'
  obtain ⟨a, ha, rfl⟩ := ha'
  obtain ⟨b, hb, rfl⟩ := hb'
  have hinj : ∀ u v : X, e u = e v → u = v := fun u v h => e.injective h
  refine ⟨a, ha, b, hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hinj _ _ (by simpa using h1)
  · exact hinj _ _ (by simpa using h2)
  · exact hinj _ _ (by simpa using h3)
  · intro h
    exact h4 (by simp [h])
  · intro h
    exact h5 (by simp [h])
  · intro h
    exact h6 (by simp [h])

end Transport

section Lin

variable {K : Type} [Field K] [Finite K]

theorem lin_four (hK2 : ringChar K ≠ 2) {S : Subgroup (projectiveSL 3 K)} (hS : IsPGroup 2 S)
    (hmax : ∀ T : Subgroup (projectiveSL 3 K), IsPGroup 2 T → S ≤ T → T ≤ S) :
    ∃ a ∈ S, ∃ b ∈ S, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  refine four_of_d8 (proj 3 K) hS hmax (e := eSL) (r := rSL) eSL_pow_four rSL_sq rSL_eSL
    (fun a b ha hb hab => eq_of_proj_eq (j := 2) (by simpa using ha) (by simpa using hb) hab)
    ?_ ?_ ?_
  · intro h
    have := congrArg (fun g : SL(3, K) => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_eSL, eMat, Matrix.mul_apply, Fin.sum_univ_succ] at this
    exact h2 (by linear_combination (-1 : K) * this)
  · intro h
    have := congrArg (fun g : SL(3, K) => (g : Matrix (Fin 3) (Fin 3) K) 1 1) h
    simp [coe_rSL, rMat] at this
    exact h2 (by linear_combination (-1 : K) * this)
  · intro h
    have := congrArg (fun g : SL(3, K) => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_eSL, coe_rSL, eMat, rMat, Matrix.mul_apply, Fin.sum_univ_succ] at this
    exact h2 (by linear_combination (-1 : K) * this)

end Lin

section Uni

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

local notation "𝟙" => ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

theorem uni_four (hp2 : p ≠ 2) {S : Subgroup (primeFormP h 𝟙)} (hS : IsPGroup 2 S)
    (hmax : ∀ T : Subgroup (primeFormP h 𝟙), IsPGroup 2 T → S ≤ T → T ≤ S) :
    ∃ a ∈ S, ∃ b ∈ S, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  have : Finite K := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have h2 : (2 : K) ≠ 0 := by
    intro h2
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h2
    have := (CharP.cast_eq_zero_iff K p 2).1 this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this)
  refine four_of_d8 (QuotientGroup.mk' (normOneScalars h (gramSU h 𝟙) 3)) hS hmax (e := eU h)
    (r := rU h) (eU_pow_four h) (rU_sq h) (rU_eU h)
    (fun a b ha hb hab => eq_of_mk_eq_u h (j := 2) (by simpa using ha) (by simpa using hb) hab)
    ?_ ?_ ?_
  · intro hh
    have := congrArg (fun g : gramSU h 𝟙 => (((g : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 0 0) hh
    simp [eU, coe_eSL, eMat, Matrix.mul_apply, Fin.sum_univ_succ] at this
    exact h2 (by linear_combination (-1 : K) * this)
  · intro hh
    have := congrArg (fun g : gramSU h 𝟙 => (((g : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 1 1) hh
    simp [rU, coe_rSL, rMat] at this
    exact h2 (by linear_combination (-1 : K) * this)
  · intro hh
    have := congrArg (fun g : gramSU h 𝟙 => (((g : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 0 0) hh
    simp [eU, rU, coe_eSL, coe_rSL, Matrix.mul_apply, Fin.sum_univ_succ, eMat, rMat] at this
    exact h2 (by linear_combination (-1 : K) * this)

end Uni

theorem l3eps_sylow_four {X : Type} [Group X] [Finite X] {t : StatedLieTag} {p f : ℕ}
    (ht : t = .PSL ∨ t = .PSU) (hp2 : p ≠ 2) (hX : StatedClassicalModel X t 3 p f)
    {S : Subgroup X} (hS : IsPGroup 2 S) (hmax : ∀ T : Subgroup X, IsPGroup 2 T → S ≤ T → T ≤ S) :
    ∃ a ∈ S, ∃ b ∈ S, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  rcases ht with rfl | rfl
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_projectiveSL_equiv hX
    exact four_of_mulEquiv e (fun S' hS' hmax' =>
      lin_four (ringChar_ne_two_of_card hX.1.1 hp2 hF) hS' hmax') hS hmax
  · obtain ⟨K, _, hU, ⟨e⟩⟩ := exists_primeFormP_equiv hX
    exact four_of_mulEquiv e (fun S' hS' hmax' => uni_four hU hp2 hS' hmax') hS hmax

end CFSG.GH74.KGroups.L3Eps
