module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU62Model

public section

namespace CFSG.AGLEmbedding.U62O10Cent

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62

section Gram

variable {p f : ℕ} {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def gramU (h : UnitaryFieldData p f K) (G : Matrix ι ι K) : Subgroup (GL ι K) where
  carrier := {g | ((g : Matrix ι ι K).map h.bar)ᵀ * G * g = G}
  mul_mem' {g g'} hg hg' := by
    change (((g * g' : GL ι K) : Matrix ι ι K).map h.bar)ᵀ * G * ((g * g' : GL ι K) :
      Matrix ι ι K) = G
    rw [Units.val_mul, conjTranspose_mul_mul]
    rw [hg]
    exact hg'
  one_mem' := by
    change (((1 : GL ι K) : Matrix ι ι K).map h.bar)ᵀ * G * ((1 : GL ι K) : Matrix ι ι K) = G
    simp
  inv_mem' {g} hg := by
    have hgg : (g : Matrix ι ι K) * ((g⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h1 := conjTranspose_mul_mul h G (g : Matrix ι ι K) ((g⁻¹ : GL ι K) : Matrix ι ι K)
    change ((g : Matrix ι ι K).map h.bar)ᵀ * G * (g : Matrix ι ι K) = G at hg
    rw [hg, hgg] at h1
    simp only [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one,
      Matrix.one_mul, Matrix.mul_one] at h1
    exact h1.symm

theorem mem_gramU {h : UnitaryFieldData p f K} {G : Matrix ι ι K} {g : GL ι K} :
    g ∈ gramU h G ↔ ((g : Matrix ι ι K).map h.bar)ᵀ * G * (g : Matrix ι ι K) = G :=
  Iff.rfl

theorem toLin_mem_sesqUnitaryGroup_iff (h : UnitaryFieldData p f K) (G : Matrix ι ι K)
    (g : GL ι K) :
    Matrix.GeneralLinearGroup.toLin g ∈ sesqUnitaryGroup (gramForm h G) ↔ g ∈ gramU h G := by
  rw [mem_sesqUnitaryGroup, mem_gramU, ← gramForm_isometry_iff]
  simp only [Matrix.GeneralLinearGroup.coe_toLin, ← Matrix.toLin'_apply', Matrix.toLin'_apply]

theorem card_gramU (h : UnitaryFieldData p f K) (G : Matrix ι ι K) :
    Nat.card (gramU h G) = Nat.card (sesqUnitaryGroup (gramForm h G)) :=
  Nat.card_congr ((Matrix.GeneralLinearGroup.toLin.toEquiv.subtypeEquiv fun g =>
    (toLin_mem_sesqUnitaryGroup_iff h G g).symm))

end Gram

theorem card_gramU_one {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (hι : Fintype.card ι = n)
    (hn : n ≤ 3) :
    Nat.card (gramU uData (1 : Matrix ι ι F4)) = (![1, 3, 18, 648] : Fin 4 → ℕ) ⟨n, by omega⟩ := by
  rw [card_gramU]
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hι
    have : Subsingleton (LinearMap.GeneralLinearGroup F4 (ι → F4)) :=
      ⟨fun a b => Units.ext (LinearMap.ext fun v => funext fun i => isEmptyElim i)⟩
    have : Subsingleton (sesqUnitaryGroup (gramForm uData (1 : Matrix ι ι F4))) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    rw [Nat.card_unique]
    rfl
  · have hdim : Module.finrank F4 (ι → F4) = n := by
      rw [Module.finrank_fintype_fun_eq_card, hι]
    have hsymm : (gramForm uData (1 : Matrix ι ι F4)).IsSymm :=
      gramForm_isSymm uData (by simp)
    have hsep : (gramForm uData (1 : Matrix ι ι F4)).SeparatingLeft :=
      gramForm_separatingLeft uData (by simp)
    have key := (unitary_full_group_order uData hsymm hsep hdim hpos).1
    interval_cases n
    · have h1 : (Nat.card (sesqUnitaryGroup (gramForm uData (1 : Matrix ι ι F4))) : ℤ) = 3 := by
        rw [key]; decide
      exact_mod_cast h1
    · have h1 : (Nat.card (sesqUnitaryGroup (gramForm uData (1 : Matrix ι ι F4))) : ℤ) = 18 := by
        rw [key]; decide
      exact_mod_cast h1
    · have h1 : (Nat.card (sesqUnitaryGroup (gramForm uData (1 : Matrix ι ι F4))) : ℤ) = 648 := by
        rw [key]; decide
      exact_mod_cast h1

end CFSG.AGLEmbedding.U62O10Cent
