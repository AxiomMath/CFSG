module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.Sp
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits CFSG.Open
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.SpCell

variable {F : Type} [Field F]

@[expose] def j1Mat (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks (A : Matrix (Fin 2) (Fin 2) F) 0 0
    (((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))ᵀ

theorem j1Mat_one : j1Mat (1 : Matrix.SpecialLinearGroup (Fin 2) F) = 1 := by
  simp [j1Mat, Matrix.fromBlocks_one]

theorem j1Mat_mul (A B : Matrix.SpecialLinearGroup (Fin 2) F) :
    j1Mat (A * B) = j1Mat A * j1Mat B := by
  simp [j1Mat, Matrix.fromBlocks_multiply, _root_.mul_inv_rev, Matrix.transpose_mul]

@[expose] def j1 : Matrix.SpecialLinearGroup (Fin 2) F →* GL (Fin 2 ⊕ Fin 2) F :=
  MonoidHom.toHomUnits
    { toFun := j1Mat
      map_one' := j1Mat_one
      map_mul' := j1Mat_mul }

theorem coe_j1 (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((j1 A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = j1Mat A := rfl

@[expose] def tauPerm : Equiv.Perm (Fin 2 ⊕ Fin 2) := Equiv.swap (Sum.inl 1) (Sum.inr 1)

theorem tauPerm_symm : (tauPerm : Equiv.Perm (Fin 2 ⊕ Fin 2)).symm = tauPerm :=
  Equiv.symm_swap _ _

theorem tauPerm_tauPerm (x : Fin 2 ⊕ Fin 2) : tauPerm (tauPerm x) = x := Equiv.swap_apply_self _ _ _

@[expose] def tauConj : GL (Fin 2 ⊕ Fin 2) F ≃* GL (Fin 2 ⊕ Fin 2) F :=
  Units.mapEquiv (Matrix.reindexAlgEquiv F F tauPerm).toMulEquiv

theorem coe_tauConj (A : GL (Fin 2 ⊕ Fin 2) F) :
    ((tauConj A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).submatrix tauPerm.symm tauPerm.symm := rfl

@[expose] def j2 : Matrix.SpecialLinearGroup (Fin 2) F →* GL (Fin 2 ⊕ Fin 2) F :=
  tauConj.toMonoidHom.comp j1

theorem coe_j2 (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((j2 A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      (j1Mat A).submatrix tauPerm.symm tauPerm.symm := rfl

theorem quadPlus_eq_dotProduct (v : Fin 2 ⊕ Fin 2 → F) :
    StatedQuadPlus 2 F v = (v ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inr) := rfl

theorem j1_preserves (A : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 ⊕ Fin 2 → F) :
    StatedQuadPlus 2 F (j1Mat A *ᵥ v) = StatedQuadPlus 2 F v := by
  rw [quadPlus_eq_dotProduct, quadPlus_eq_dotProduct]
  simp only [j1Mat, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  have h : ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (A : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec, h,
    Matrix.one_mulVec]

theorem quadPlus_comp_tauPerm (v : Fin 2 ⊕ Fin 2 → F) :
    StatedQuadPlus 2 F (v ∘ tauPerm) = StatedQuadPlus 2 F v := by
  simp [StatedQuadPlus, Fin.sum_univ_two, tauPerm, Equiv.swap_apply_of_ne_of_ne, mul_comm]

theorem j2_preserves (A : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 ⊕ Fin 2 → F) :
    StatedQuadPlus 2 F (((j2 A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
      *ᵥ v) = StatedQuadPlus 2 F v := by
  have h : ((j2 A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v =
      (j1Mat A *ᵥ (v ∘ tauPerm)) ∘ tauPerm := by
    rw [coe_j2]
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Function.comp_apply]
    rw [tauPerm_symm, ← Equiv.sum_comp tauPerm]
    simp only [tauPerm_tauPerm]
  rw [h, quadPlus_comp_tauPerm, j1_preserves]
  exact quadPlus_comp_tauPerm v

theorem j1_mem_orthGroup (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    j1 A ∈ orthGroup (StatedQuadPlus 2 F) :=
  Subgroup.subset_closure fun v => j1_preserves A v

theorem j2_mem_orthGroup (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    j2 A ∈ orthGroup (StatedQuadPlus 2 F) :=
  Subgroup.subset_closure fun v => j2_preserves A v

theorem j1Mat_entries (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    j1Mat A = Matrix.fromBlocks !![A 0 0, A 0 1; A 1 0, A 1 1] 0 0
      !![A 1 1, -A 1 0; -A 0 1, A 0 0] := by
  rw [j1Mat, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, ← Matrix.eta_fin_two]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem j1_j2_commute (A B : Matrix.SpecialLinearGroup (Fin 2) F) :
    Commute (j1 A) (j2 B) := by
  have hA := A.2
  have hB := B.2
  rw [Matrix.det_fin_two] at hA hB
  refine Units.ext ?_
  show j1Mat A * ((j1Mat B).submatrix tauPerm.symm tauPerm.symm) =
    ((j1Mat B).submatrix tauPerm.symm tauPerm.symm) * j1Mat A
  rw [j1Mat_entries, j1Mat_entries]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, tauPerm,
      Equiv.swap_apply_of_ne_of_ne]
  all_goals ring

theorem j1_injective : Function.Injective (j1 (F := F)) := by
  intro A B h
  have h' : j1Mat A = j1Mat B := congrArg Units.val h
  rw [j1Mat_entries, j1Mat_entries] at h'
  have e := fun i j => congrFun (congrFun h' (Sum.inl i)) (Sum.inl j)
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j
  · simpa using e 0 0
  · simpa using e 0 1
  · simpa using e 1 0
  · simpa using e 1 1

theorem j2_injective : Function.Injective (j2 (F := F)) := by
  intro A B h
  exact j1_injective (tauConj.injective h)

theorem eq_one_of_j1_eq_j2 [CharP F 2] {A B : Matrix.SpecialLinearGroup (Fin 2) F}
    (h : j1 A = j2 B) : A = 1 ∧ B = 1 := by
  have h' : j1Mat A = (j1Mat B).submatrix tauPerm.symm tauPerm.symm := congrArg Units.val h
  rw [j1Mat_entries, j1Mat_entries] at h'
  have e := fun i j => congrFun (congrFun h' i) j
  have e1 := e (Sum.inl 0) (Sum.inl 1)
  have e2 := e (Sum.inl 1) (Sum.inl 0)
  have e3 := e (Sum.inl 0) (Sum.inl 0)
  have e4 := e (Sum.inl 1) (Sum.inl 1)
  have e5 := e (Sum.inl 0) (Sum.inr 1)
  have e6 := e (Sum.inr 1) (Sum.inl 0)
  simp [tauPerm, Equiv.swap_apply_of_ne_of_ne] at e1 e2 e3 e4 e5 e6
  have hA := A.2
  have hB := B.2
  rw [Matrix.det_fin_two] at hA hB
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have e5' := e5.symm
  have e6' := e6.symm
  have hA0 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have hsq : ((A : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) ^ 2 = 0 := by
      linear_combination hA + (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (e3 - e4) +
        (A : Matrix (Fin 2) (Fin 2) F) 1 0 * e1 + (1 - (A : Matrix (Fin 2) (Fin 2) F) 0 0) * h2
    have := pow_eq_zero_iff (two_ne_zero) |>.1 hsq
    linear_combination this
  have hB0 : (B : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by rw [← e3]; exact hA0
  have hA1 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by rw [e4]; exact hB0
  have hB1 : (B : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    linear_combination hB - (B : Matrix (Fin 2) (Fin 2) F) 1 1 * hB0 -
      (B : Matrix (Fin 2) (Fin 2) F) 1 0 * e5
  constructor
  · refine Subtype.ext (Matrix.ext fun i j => ?_)
    fin_cases i <;> fin_cases j
    · simpa using hA0
    · simpa using e1
    · simpa using e2
    · simpa using hA1
  · refine Subtype.ext (Matrix.ext fun i j => ?_)
    fin_cases i <;> fin_cases j
    · simpa using hB0
    · simpa using e5'
    · simpa using e6'
    · simpa using hB1

theorem card_orthGroup_quadPlus_two [Finite F] :
    Nat.card ↥(orthGroup (StatedQuadPlus 2 F)) = 2 * Nat.card F ^ 2 * (Nat.card F ^ 2 - 1) ^ 2 := by
  have hQ : ⇑(CFSG.LieType.Universal.Spin.quadPlus 2 F) = StatedQuadPlus 2 F :=
    funext fun v => CFSG.LieType.Universal.Spin.quadPlus_apply 2 F v
  have hcomap := CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap
    (ι := Fin 2 ⊕ Fin 2) hQ
  have e : ↥(orthGroup (StatedQuadPlus 2 F)) ≃*
      ↥(TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadPlus 2 F)) :=
    ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2) F).subgroupMap
      (orthGroup (StatedQuadPlus 2 F))).trans (MulEquiv.subgroupCongr (by
        show Subgroup.map _ (Subgroup.closure _) = _
        rw [hcomap]
        exact Subgroup.map_comap_eq_self_of_surjective
          (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2) F).surjective _))
  rw [Nat.card_congr e.toEquiv]
  have h := (CFSG.ClassicalInvolution.card_singular_and_orthogonalGroup_quadPlus (K := F) 1).2
  have hq : 1 ≤ Nat.card F := Nat.one_le_iff_ne_zero.mpr Finite.card_pos.ne'
  have hq2 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ hq
  simp only [Finset.Icc_self, Finset.prod_singleton] at h
  zify [hq2]
  convert h using 1
  ring

theorem eq_one_of_pow_eq_one_of_not_dvd [Finite F] [CharP F 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card F ^ 2 - 1) {y : GL (Fin 2 ⊕ Fin 2) F}
    (hy : y ∈ orthGroup (StatedQuadPlus 2 F)) (hyp : y ^ p = 1) : y = 1 := by
  set y' : ↥(orthGroup (StatedQuadPlus 2 F)) := ⟨y, hy⟩ with hy'
  have h1 : y' ^ p = 1 := Subtype.ext hyp
  have hdvd : orderOf y' ∣ p := orderOf_dvd_of_pow_eq_one h1
  rcases (Nat.dvd_prime hp).1 hdvd with h | h
  · have : y' = 1 := orderOf_eq_one_iff.1 h
    exact congrArg Subtype.val this
  · exfalso
    have hO : p ∣ Nat.card ↥(orthGroup (StatedQuadPlus 2 F)) := h ▸ orderOf_dvd_natCard y'
    rw [card_orthGroup_quadPlus_two] at hO
    have hnq : ¬ p ∣ Nat.card F := by
      intro hq
      have := Fintype.ofFinite F
      obtain ⟨n, -, hn⟩ := FiniteField.card F 2
      have hq' : p ∣ 2 ^ (n : ℕ) := by
        have : Nat.card F = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
        rwa [this] at hq
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hq'))
    rcases (Nat.Prime.dvd_mul hp).1 hO with h3 | h3
    · rcases (Nat.Prime.dvd_mul hp).1 h3 with h4 | h4
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h4)
      · exact hnq (hp.dvd_of_dvd_pow h4)
    · exact hpq (hp.dvd_of_dvd_pow h3)

@[expose] def jProd : (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F) →*
    GL (Fin 2 ⊕ Fin 2) F :=
  MonoidHom.noncommCoprod j1 j2 fun a b => j1_j2_commute a b

theorem jProd_apply (a b : Matrix.SpecialLinearGroup (Fin 2) F) :
    jProd (a, b) = j1 a * j2 b := by
  simp [jProd, MonoidHom.noncommCoprod_apply]

theorem jProd_injective [CharP F 2] : Function.Injective (jProd (F := F)) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b⟩ h
  rw [jProd_apply] at h
  have h' : j1 a = j2 b⁻¹ := by
    rw [map_inv]; exact eq_inv_of_mul_eq_one_left h
  obtain ⟨ha, hb⟩ := eq_one_of_j1_eq_j2 h'
  rw [ha]
  exact Prod.ext rfl (inv_eq_one.1 hb)

theorem jProd_mem_orthGroup (x : Matrix.SpecialLinearGroup (Fin 2) F ×
    Matrix.SpecialLinearGroup (Fin 2) F) : jProd x ∈ orthGroup (StatedQuadPlus 2 F) := by
  obtain ⟨a, b⟩ := x
  rw [jProd_apply]
  exact mul_mem (j1_mem_orthGroup a) (j2_mem_orthGroup b)

theorem card_jProd_range [Finite F] [CharP F 2] :
    Nat.card ↥(jProd (F := F)).range = Nat.card F ^ 2 * (Nat.card F ^ 2 - 1) ^ 2 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective jProd_injective).toEquiv, Nat.card_prod,
    card_SL2_eq]
  ring

theorem relIndex_jProd_range [Finite F] [CharP F 2] :
    (jProd (F := F)).range.relIndex (orthGroup (StatedQuadPlus 2 F)) = 2 := by
  have hle : (jProd (F := F)).range ≤ orthGroup (StatedQuadPlus 2 F) := by
    rintro _ ⟨x, rfl⟩; exact jProd_mem_orthGroup x
  have h := Subgroup.relIndex_mul_card (H := (jProd (F := F)).range)
    (K := orthGroup (StatedQuadPlus 2 F))
  rw [inf_of_le_left hle, card_jProd_range, card_orthGroup_quadPlus_two] at h
  have hq : 1 ≤ Nat.card F := Nat.one_le_iff_ne_zero.mpr Finite.card_pos.ne'
  have hpos : 0 < Nat.card F ^ 2 * (Nat.card F ^ 2 - 1) ^ 2 := by
    have h2 : 2 ≤ Nat.card F := by
      have := Finite.one_lt_card (α := F)
      omega
    have h3 : 0 < Nat.card F ^ 2 - 1 := by
      have : 4 ≤ Nat.card F ^ 2 := by nlinarith
      omega
    positivity
  have : (jProd (F := F)).range.relIndex (orthGroup (StatedQuadPlus 2 F)) *
      (Nat.card F ^ 2 * (Nat.card F ^ 2 - 1) ^ 2) = 2 * (Nat.card F ^ 2 * (Nat.card F ^ 2 - 1) ^ 2) := by
    rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem map_mem_statedOmega_of_perfect [Finite F] (h4 : 4 ≤ Nat.card F)
    (φ : Matrix.SpecialLinearGroup (Fin 2) F →* GL (Fin 2 ⊕ Fin 2) F)
    (hφ : ∀ A, φ A ∈ orthGroup (StatedQuadPlus 2 F)) (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    φ A ∈ StatedOmega (StatedQuadPlus 2 F) := by
  have hperf : commutator (Matrix.SpecialLinearGroup (Fin 2) F) = ⊤ :=
    Group.isPerfect_def.1 (LieType.HighestRoot.isQuasisimple_SL2_of_four_le h4).1
  have hA : A ∈ ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)),
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))⁆ := by
    rw [← commutator_def, hperf]; trivial
  have hle : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).map φ ≤
      orthGroup (StatedQuadPlus 2 F) := by
    rintro _ ⟨x, -, rfl⟩; exact hφ x
  have := Subgroup.commutator_mono hle hle
  rw [← Subgroup.map_commutator] at this
  exact this ⟨A, hA, rfl⟩

theorem j1_mem_omega [Finite F] (h4 : 4 ≤ Nat.card F) (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    j1 A ∈ StatedOmega (StatedQuadPlus 2 F) :=
  map_mem_statedOmega_of_perfect h4 j1 j1_mem_orthGroup A

theorem j2_mem_omega [Finite F] (h4 : 4 ≤ Nat.card F) (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    j2 A ∈ StatedOmega (StatedQuadPlus 2 F) :=
  map_mem_statedOmega_of_perfect h4 j2 j2_mem_orthGroup A

@[expose] def j1Om [Finite F] (h4 : 4 ≤ Nat.card F) :
    Matrix.SpecialLinearGroup (Fin 2) F →* ↥(StatedOmega (StatedQuadPlus 2 F)) :=
  j1.codRestrict _ (j1_mem_omega h4)

@[expose] def j2Om [Finite F] (h4 : 4 ≤ Nat.card F) :
    Matrix.SpecialLinearGroup (Fin 2) F →* ↥(StatedOmega (StatedQuadPlus 2 F)) :=
  j2.codRestrict _ (j2_mem_omega h4)

theorem j1Om_injective [Finite F] (h4 : 4 ≤ Nat.card F) : Function.Injective (j1Om h4) :=
  fun _ _ h => j1_injective (congrArg Subtype.val h)

theorem j2Om_injective [Finite F] (h4 : 4 ≤ Nat.card F) : Function.Injective (j2Om h4) :=
  fun _ _ h => j2_injective (congrArg Subtype.val h)

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell
