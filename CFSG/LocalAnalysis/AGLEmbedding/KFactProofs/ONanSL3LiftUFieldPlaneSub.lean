module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {p f f₀ : ℕ} {K : Type} [Field K]

section Subfield

variable {K₀ : Subfield K}

theorem bar_coe_subfield (h : UnitaryFieldData p f K) (hf : f = 3 * f₀)
    (h₀ : UnitaryFieldData p f₀ K₀) (x : K₀) : h.bar (x : K) = ((h₀.bar x : K₀) : K) := by
  have hx : x ^ (p ^ (2 * f₀)) = x := by
    have := h₀.finite
    have := Fintype.ofFinite K₀
    rw [← h₀.card, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  rw [h.bar_apply, h₀.bar_apply, ← SubmonoidClass.coe_pow]
  congr 1
  rw [show p ^ f = p ^ (2 * f₀) * p ^ f₀ by rw [← pow_add, hf]; congr 1; omega, pow_mul, hx]

theorem coe_map_subfield {n : ℕ} (A : GL (Fin n) K₀) :
    ((Matrix.GeneralLinearGroup.map K₀.subtype A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (A : Matrix (Fin n) (Fin n) K₀).map K₀.subtype := by
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply]

theorem map_subfield_mem_unitarySU (h : UnitaryFieldData p f K) (hf : f = 3 * f₀)
    (h₀ : UnitaryFieldData p f₀ K₀) {n : ℕ} {A : GL (Fin n) K₀} (hA : A ∈ unitarySU p f₀ K₀ n) :
    Matrix.GeneralLinearGroup.map K₀.subtype A ∈ unitarySU p f K n := by
  rw [mem_unitarySU_iff h₀] at hA
  rw [mem_unitarySU_iff h, coe_map_subfield]
  refine ⟨?_, ?_⟩
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hA.1, map_one]
  · have h1 : ((A : Matrix (Fin n) (Fin n) K₀).map K₀.subtype).map h.bar =
        ((A : Matrix (Fin n) (Fin n) K₀).map h₀.bar).map K₀.subtype := by
      ext i j
      simp [bar_coe_subfield h hf h₀]
    rw [h1, ← Matrix.transpose_map, ← Matrix.map_mul, hA.2,
      Matrix.map_one _ (map_zero _) (map_one _)]

@[expose] noncomputable def suOfSubfield (h : UnitaryFieldData p f K) (hf : f = 3 * f₀)
    (h₀ : UnitaryFieldData p f₀ K₀) (n : ℕ) : unitarySU p f₀ K₀ n →* unitarySU p f K n :=
  ((Matrix.GeneralLinearGroup.map K₀.subtype).comp (unitarySU p f₀ K₀ n).subtype).codRestrict _
    fun A => map_subfield_mem_unitarySU h hf h₀ A.2

theorem coe_suOfSubfield (h : UnitaryFieldData p f K) (hf : f = 3 * f₀)
    (h₀ : UnitaryFieldData p f₀ K₀) {n : ℕ} (A : unitarySU p f₀ K₀ n) :
    ((suOfSubfield h hf h₀ n A : unitarySU p f K n) : GL (Fin n) K) =
      Matrix.GeneralLinearGroup.map K₀.subtype (A : GL (Fin n) K₀) :=
  rfl

theorem suOfSubfield_injective (h : UnitaryFieldData p f K) (hf : f = 3 * f₀)
    (h₀ : UnitaryFieldData p f₀ K₀) (n : ℕ) : Function.Injective (suOfSubfield h hf h₀ n) := by
  intro A B hAB
  have hAB' := congrArg
    (fun g : unitarySU p f K n => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hAB
  refine Subtype.ext (Units.ext ?_)
  ext i j
  have := congrFun (congrFun hAB' i) j
  simpa [coe_suOfSubfield, Matrix.GeneralLinearGroup.map_apply] using this

theorem entries_suOfSubfield (h : UnitaryFieldData p f K) (hf : f = 3 * f₀)
    (h₀ : UnitaryFieldData p f₀ K₀) {n : ℕ} (A : unitarySU p f₀ K₀ n) (i j : Fin n) :
    ((suOfSubfield h hf h₀ n A : unitarySU p f K n) : GL (Fin n) K) i j ∈ K₀ := by
  rw [coe_suOfSubfield, Matrix.GeneralLinearGroup.map_apply]
  exact ((A : GL (Fin n) K₀) i j).2

theorem not_isSolvable_of_subfield (h : UnitaryFieldData p f K) (hf : f = 3 * f₀)
    (hq₀ : 4 ≤ p ^ f₀) (hK₀ : Nat.card K₀ = p ^ (2 * f₀))
    (H₂ : Subgroup (unitarySU p f K 2))
    (hK : ∀ g : unitarySU p f K 2,
      (∀ i j, ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j ∈ K₀) → g ∈ H₂) :
    ¬ Group.IsSolvable H₂ := by
  intro hs
  have hf₀ : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with rfl | hpos
    · simp at hq₀
    · exact hpos
  have h₀' : UnitaryFieldData p f₀ K₀ := ⟨h.prime, hf₀, hK₀⟩
  have : Finite K₀ := h₀'.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K₀ p := h₀'.charP
  have hperf : Group.IsPerfect (unitarySU p f₀ K₀ 2) :=
    CFSG.RankThree.SubgroupLists.isPerfect_statedSU_two h₀'.card_eq_sq hq₀
  have hnt : Nontrivial (unitarySU p f₀ K₀ 2) := by
    rw [← Finite.one_lt_card_iff_nontrivial,
      CFSG.RankThree.SubgroupLists.card_statedSU_two h₀'.card_eq_sq]
    have h16 : 16 ≤ (p ^ f₀) ^ 2 := by nlinarith
    have := Nat.mul_le_mul hq₀ (show 15 ≤ (p ^ f₀) ^ 2 - 1 by omega)
    omega
  let ι : unitarySU p f₀ K₀ 2 →* H₂ :=
    (suOfSubfield h hf h₀' 2).codRestrict H₂ fun A => hK _ (entries_suOfSubfield h hf h₀' A)
  have hinj : Function.Injective ι := fun A B hAB =>
    suOfSubfield_injective h hf h₀' 2 (congrArg Subtype.val hAB)
  have : Group.IsSolvable (unitarySU p f₀ K₀ 2) := Group.isSolvable_of_isSolvable_injective hinj
  exact Group.IsPerfect.not_isSolvable (unitarySU p f₀ K₀ 2) this

end Subfield

section Diag

@[expose] noncomputable def diagInvTwo (a : Kˣ) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![(a : K), ((a⁻¹ : Kˣ) : K)])
    (by simp [Matrix.det_diagonal, Fin.prod_univ_two])

theorem coe_diagInvTwo (a : Kˣ) :
    ((diagInvTwo a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal ![(a : K), ((a⁻¹ : Kˣ) : K)] :=
  rfl

theorem isDiag_diagInvTwo (a : Kˣ) :
    ((diagInvTwo a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).IsDiag := by
  rw [coe_diagInvTwo]
  exact Matrix.isDiag_diagonal _

@[expose] noncomputable def diagInvTwoHom : Kˣ →* GL (Fin 2) K where
  toFun := diagInvTwo
  map_one' := by
    refine Units.ext ?_
    rw [coe_diagInvTwo, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    refine Units.ext ?_
    rw [Units.val_mul, coe_diagInvTwo, coe_diagInvTwo, coe_diagInvTwo, Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp [mul_comm]

theorem diagInvTwoHom_injective : Function.Injective (diagInvTwoHom : Kˣ →* GL (Fin 2) K) := by
  intro a b hab
  have := congrFun (congrFun (congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K))
    hab) 0) 0
  exact Units.ext (by simpa [diagInvTwoHom, coe_diagInvTwo] using this)

theorem orderOf_diagInvTwo (a : Kˣ) : orderOf (diagInvTwo a) = orderOf a :=
  orderOf_injective diagInvTwoHom diagInvTwoHom_injective a

theorem diagInvTwo_mem_unitarySU (h : UnitaryFieldData p f K) {a : Kˣ} (ha : a ^ (p ^ f + 1) = 1) :
    diagInvTwo a ∈ unitarySU p f K 2 := by
  have hbar : ∀ u : Kˣ, u ^ (p ^ f + 1) = 1 → h.bar (u : K) * (u : K) = 1 := fun u hu => by
    rw [h.bar_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, hu, Units.val_one]
  rw [mem_unitarySU_iff h, coe_diagInvTwo]
  refine ⟨by simp [Matrix.det_diagonal, Fin.prod_univ_two], ?_⟩
  rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i
  · exact hbar a ha
  · exact hbar a⁻¹ (by rw [inv_pow, ha, inv_one])

end Diag

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField
