module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFourModules

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

open scoped MatrixGroups LinearAlgebra.Projectivization
open CFSG.GorensteinWalter Projectivization

section Borel

variable {F : Type*} [Field F]

@[expose] def borelSubgroup (F : Type*) [Field F] : Subgroup SL(2, F) :=
  MulAction.stabilizer SL(2, F) (psl2ProjectiveInfinity F)

theorem mem_borelSubgroup_iff (g : SL(2, F)) :
    g ∈ borelSubgroup F ↔ ∃ (a : Fˣ) (b : F),
      (g : Matrix (Fin 2) (Fin 2) F) = !![(a : F), b; 0, ((a⁻¹ : Fˣ) : F)] := by
  rw [borelSubgroup, sl2_mem_stabilizer_infinity_iff]
  constructor
  · intro h10
    have ha := borel_a_ne_zero g h10
    have hdet : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
      have h := g.property
      rw [Matrix.det_fin_two, h10] at h
      simpa using h
    refine ⟨Units.mk0 _ ha, (g : Matrix (Fin 2) (Fin 2) F) 0 1, ?_⟩
    ext i j
    have h11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = ((g : Matrix (Fin 2) (Fin 2) F) 0 0)⁻¹ :=
      eq_inv_of_mul_eq_one_right hdet
    fin_cases i <;> fin_cases j <;> simp [h10, h11]
  · rintro ⟨a, b, h⟩
    show (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
    rw [h]
    simp

theorem borel_mul_uElt (g : SL(2, F)) (hg : g ∈ borelSubgroup F) (t : F) :
    g * uElt t = uElt (((g : Matrix (Fin 2) (Fin 2) F) 0 0) ^ 2 * t) * g := by
  have h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := (sl2_mem_stabilizer_infinity_iff g).mp hg
  have hdet : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have h := g.property
    rw [Matrix.det_fin_two, h10] at h
    simpa using h
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j
  · simp [uElt, Matrix.mul_apply, Fin.sum_univ_two, h10]
  · simp [uElt, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-(t * (g : Matrix (Fin 2) (Fin 2) F) 0 0)) * hdet
  · simp [uElt, Matrix.mul_apply, Fin.sum_univ_two, h10]
  · simp [uElt, Matrix.mul_apply, Fin.sum_univ_two, h10]

theorem upperRootGroup_le_borel : upperRootGroup F ≤ borelSubgroup F := by
  intro u hu
  obtain ⟨t, rfl⟩ := (mem_upperRootGroup_iff u).mp hu
  rw [borelSubgroup, MulAction.mem_stabilizer_iff]
  exact uElt_smul_infinity t

theorem normalizer_upperRootGroup :
    Subgroup.normalizer (upperRootGroup F : Set SL(2, F)) = borelSubgroup F := by
  ext g
  constructor
  · intro hg
    have hfix : ∀ u ∈ upperRootGroup F,
        u • (g • psl2ProjectiveInfinity F) = g • psl2ProjectiveInfinity F := by
      intro u hu
      have hu' : g⁻¹ * u * g⁻¹⁻¹ ∈ upperRootGroup F :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) u).mp hu
      have h1 : (g⁻¹ * u * g⁻¹⁻¹) • psl2ProjectiveInfinity F = psl2ProjectiveInfinity F :=
        (rootGroup_fixed_iff (psl2ProjectiveInfinity F)).mpr rfl _ hu'
      calc u • g • psl2ProjectiveInfinity F
          = g • ((g⁻¹ * u * g⁻¹⁻¹) • psl2ProjectiveInfinity F) := by
            simp only [smul_smul, inv_inv, mul_inv_cancel_left, mul_assoc]
        _ = g • psl2ProjectiveInfinity F := by rw [h1]
    exact MulAction.mem_stabilizer_iff.mpr ((rootGroup_fixed_iff (g • psl2ProjectiveInfinity F)).mp hfix)
  · intro hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨t, rfl⟩ := (mem_upperRootGroup_iff h).mp hh
      rw [mem_upperRootGroup_iff]
      exact ⟨_, by rw [borel_mul_uElt g hg t, mul_inv_cancel_right]⟩
    · intro hh
      obtain ⟨t, ht⟩ := (mem_upperRootGroup_iff _).mp hh
      have hginv : g⁻¹ ∈ borelSubgroup F := Subgroup.inv_mem _ hg
      rw [mem_upperRootGroup_iff]
      refine ⟨((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * t, ?_⟩
      calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
        _ = g⁻¹ * uElt t * g := by rw [ht]
        _ = _ := by rw [borel_mul_uElt g⁻¹ hginv t, inv_mul_cancel_right]

end Borel

section Counting

open scoped Pointwise

variable {F : Type*} [Field F] [Fintype F]

theorem natCard_projectiveLine : Nat.card (ℙ F (Fin 2 → F)) = Fintype.card F + 1 := by
  classical
  have : Fintype (ℙ F (Fin 2 → F)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact card_projectiveLine

instance : Nontrivial (ℙ F (Fin 2 → F)) :=
  ⟨⟨psl2ProjectiveInfinity F, psl2ProjectiveZero F, infinity_ne_zero⟩⟩

theorem index_stabilizer_projective (M : ℙ F (Fin 2 → F)) :
    (MulAction.stabilizer SL(2, F) M).index = Fintype.card F + 1 := by
  rw [MulAction.index_stabilizer_of_transitive, natCard_projectiveLine]

omit [Fintype F] in
theorem isCoatom_stabilizer_projective (M : ℙ F (Fin 2 → F)) :
    IsCoatom (MulAction.stabilizer SL(2, F) M) :=
  MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := SL(2, F))
    (X := ℙ F (Fin 2 → F)) M

theorem natCard_borel : Nat.card (borelSubgroup F) = Fintype.card F * (Fintype.card F - 1) := by
  have h := (borelSubgroup F).card_mul_index
  have hidx : (borelSubgroup F).index = Fintype.card F + 1 :=
    index_stabilizer_projective (psl2ProjectiveInfinity F)
  rw [hidx, CFSG.GorensteinWalter.sl2_card_formula, Nat.card_eq_fintype_card (α := F)] at h
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card F = m + 2 := by
    have := Fintype.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial F)
    exact ⟨Fintype.card F - 2, by omega⟩
  rw [hm] at h ⊢
  have h1 : (m + 2) ^ 2 - 1 = (m + 1) * (m + 3) :=
    Nat.sub_eq_of_eq_add (by ring)
  rw [h1] at h
  have h2 : m + 2 - 1 = m + 1 := by omega
  rw [h2]
  apply Nat.eq_of_mul_eq_mul_right (show 0 < m + 2 + 1 by omega)
  rw [h]
  ring

theorem natCard_upperRootGroup : Nat.card (upperRootGroup F) = Fintype.card F := by
  rw [upperRootGroup,
    CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.upperUnipotent_card,
    Nat.card_eq_fintype_card]

theorem factorization_card_sl2_prime {p n : ℕ} [hp : Fact p.Prime] (hn : 1 ≤ n)
    (hF : Fintype.card F = p ^ n) : (Nat.card SL(2, F)).factorization p = n := by
  have h1 := CFSG.GorensteinWalter.sl2_card_formula F
  rw [Nat.card_eq_fintype_card (α := F), hF] at h1
  rw [h1]
  have hodd : ¬ p ∣ ((p ^ n) ^ 2 - 1) := by
    intro h
    have h2 : p ∣ (p ^ n) ^ 2 := dvd_pow (dvd_pow_self p (by omega)) (by norm_num)
    have h3 : 1 ≤ (p ^ n) ^ 2 := Nat.one_le_pow 2 (p ^ n) (pow_pos hp.out.pos n)
    have h4 : p ∣ 1 := by
      have := Nat.dvd_sub h2 h
      rwa [Nat.sub_sub_self h3] at this
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp h4)
  have hne : (p ^ n) ^ 2 - 1 ≠ 0 := fun h => hodd (by rw [h]; exact dvd_zero p)
  rw [Nat.factorization_mul (by have := hp.out.pos; positivity) hne, Finsupp.add_apply,
    Nat.Prime.factorization_pow hp.out, Nat.factorization_eq_zero_of_not_dvd hodd]
  simp

theorem upperRootGroup_isSylow {p : ℕ} [Fact p.Prime] [CharP F p] :
    ∃ P : Sylow p SL(2, F), (P : Subgroup SL(2, F)) = upperRootGroup F := by
  obtain ⟨n, -, hF⟩ := FiniteField.card F p
  refine ⟨Sylow.ofCard (upperRootGroup F) ?_, rfl⟩
  rw [natCard_upperRootGroup, hF, factorization_card_sl2_prime n.pos hF]

omit [Fintype F] in
theorem borel_not_normal : ¬ (borelSubgroup F).Normal := by
  intro hnorm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, F) (psl2ProjectiveInfinity F)
    (psl2ProjectiveZero F)
  have hfix : ∀ u ∈ upperRootGroup F, u • psl2ProjectiveZero F = psl2ProjectiveZero F := by
    intro u hu
    have hu' : g⁻¹ * u * g⁻¹⁻¹ ∈ borelSubgroup F :=
      hnorm.conj_mem u (upperRootGroup_le_borel hu) g⁻¹
    have h1 : (g⁻¹ * u * g⁻¹⁻¹) • psl2ProjectiveInfinity F = psl2ProjectiveInfinity F :=
      MulAction.mem_stabilizer_iff.mp hu'
    calc u • psl2ProjectiveZero F = u • g • psl2ProjectiveInfinity F := by rw [hg]
      _ = g • ((g⁻¹ * u * g⁻¹⁻¹) • psl2ProjectiveInfinity F) := by
          simp only [smul_smul, inv_inv, mul_inv_cancel_left, mul_assoc]
      _ = g • psl2ProjectiveInfinity F := by rw [h1]
      _ = psl2ProjectiveZero F := hg
  exact infinity_ne_zero ((rootGroup_fixed_iff (psl2ProjectiveZero F)).mp hfix).symm

omit [Fintype F] in
theorem normalizer_stabilizer_projective (M : ℙ F (Fin 2 → F)) :
    Subgroup.normalizer (MulAction.stabilizer SL(2, F) M : Set SL(2, F)) =
      MulAction.stabilizer SL(2, F) M := by
  have hc := isCoatom_stabilizer_projective (F := F) M
  rcases hc.le_iff.mp Subgroup.le_normalizer with h | h
  · exfalso
    have hnorm : (MulAction.stabilizer SL(2, F) M).Normal := Subgroup.normalizer_eq_top_iff.mp h
    obtain ⟨h0, hh0⟩ := MulAction.exists_smul_eq SL(2, F) M (psl2ProjectiveInfinity F)
    have hB : borelSubgroup F = MulAction.stabilizer SL(2, F) M := by
      rw [borelSubgroup, ← hh0, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
      have hmem : h0 ∈ Subgroup.normalizer (MulAction.stabilizer SL(2, F) M : Set SL(2, F)) := by
        rw [h]; exact Subgroup.mem_top h0
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hmem
    exact borel_not_normal (hB ▸ hnorm)
  · exact h

theorem sylow_conj_description {p : ℕ} [Fact p.Prime] [CharP F p] (P : Sylow p SL(2, F)) :
    ∃ g : SL(2, F), ∀ x, x ∈ (P : Subgroup SL(2, F)) ↔ g⁻¹ * x * g ∈ upperRootGroup F := by
  obtain ⟨P₀, hP₀⟩ := upperRootGroup_isSylow (F := F) (p := p)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, F) P₀ P
  refine ⟨g, fun x => ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hP₀]
  rfl

theorem sl2_defining_characteristic_Sylow_normalizer_maximal_Borel {p : ℕ} [Fact p.Prime]
    [CharP F p] :
    Nat.card SL(2, F) = Fintype.card F * (Fintype.card F ^ 2 - 1) ∧
    (∃ P : Sylow p SL(2, F), (P : Subgroup SL(2, F)) = upperRootGroup F) ∧
    Subgroup.normalizer (upperRootGroup F : Set SL(2, F)) = borelSubgroup F ∧
    Nat.card (borelSubgroup F) = Fintype.card F * (Fintype.card F - 1) ∧
    IsCoatom (borelSubgroup F) ∧
    Subgroup.normalizer (borelSubgroup F : Set SL(2, F)) = borelSubgroup F ∧
    (borelSubgroup F).index = Fintype.card F + 1 ∧
    ∀ P : Sylow p SL(2, F), ∃ g : SL(2, F),
      (∀ x, x ∈ (P : Subgroup SL(2, F)) ↔ g⁻¹ * x * g ∈ upperRootGroup F) ∧
      (∀ x, x ∈ Subgroup.normalizer ((P : Subgroup SL(2, F)) : Set SL(2, F)) ↔ g⁻¹ * x * g ∈ borelSubgroup F) ∧
      IsCoatom (Subgroup.normalizer ((P : Subgroup SL(2, F)) : Set SL(2, F))) ∧
      Subgroup.normalizer ((Subgroup.normalizer ((P : Subgroup SL(2, F)) : Set SL(2, F)) :
        Subgroup SL(2, F)) : Set SL(2, F)) =
        Subgroup.normalizer ((P : Subgroup SL(2, F)) : Set SL(2, F)) ∧
      (Subgroup.normalizer ((P : Subgroup SL(2, F)) : Set SL(2, F))).index = Fintype.card F + 1 := by
  classical
  refine ⟨?_, upperRootGroup_isSylow, normalizer_upperRootGroup, natCard_borel,
    isCoatom_stabilizer_projective _, normalizer_stabilizer_projective _,
    index_stabilizer_projective _, ?_⟩
  · rw [CFSG.GorensteinWalter.sl2_card_formula, Nat.card_eq_fintype_card (α := F)]
  · intro P
    obtain ⟨g, hg⟩ := sylow_conj_description (p := p) P
    have hN : ∀ x, x ∈ Subgroup.normalizer ((P : Subgroup SL(2, F)) : Set SL(2, F)) ↔
        g⁻¹ * x * g ∈ borelSubgroup F := by
      intro x
      rw [← normalizer_upperRootGroup, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
      constructor
      · intro hx z
        have h1 := hx (g * z * g⁻¹)
        rw [hg, hg] at h1
        have e1 : g⁻¹ * (g * z * g⁻¹) * g = z := by group
        have e2 : g⁻¹ * (x * (g * z * g⁻¹) * x⁻¹) * g = (g⁻¹ * x * g) * z * (g⁻¹ * x * g)⁻¹ := by
          group
        rw [e1, e2] at h1
        exact h1
      · intro hx h
        rw [hg, hg]
        have h1 := hx (g⁻¹ * h * g)
        have e2 : (g⁻¹ * x * g) * (g⁻¹ * h * g) * (g⁻¹ * x * g)⁻¹ = g⁻¹ * (x * h * x⁻¹) * g := by
          group
        rw [e2] at h1
        exact h1
    have hstab : Subgroup.normalizer ((P : Subgroup SL(2, F)) : Set SL(2, F)) =
        MulAction.stabilizer SL(2, F) (g • psl2ProjectiveInfinity F) := by
      ext x
      rw [hN, borelSubgroup, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
        mul_smul, mul_smul, inv_smul_eq_iff]
    refine ⟨g, hg, hN, ?_, ?_, ?_⟩
    · rw [hstab]
      exact isCoatom_stabilizer_projective _
    · rw [hstab]
      exact normalizer_stabilizer_projective _
    · rw [hstab]
      exact index_stabilizer_projective _

end Counting

end CFSG.QuasithinUnique.Setup.SL2Modules
