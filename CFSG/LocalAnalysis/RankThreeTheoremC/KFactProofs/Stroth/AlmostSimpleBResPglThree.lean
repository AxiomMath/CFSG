module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResIndepPair
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix Matrix.ProjGenLinGroup CFSG.RankThree.PartTwo.Sec4

section

variable {F : Type} [Field F]

@[expose] noncomputable def diagGL3 : (Fin 3 → Fˣ) →* GL (Fin 3) F :=
  (Units.map (Matrix.diagonalRingHom (Fin 3) F).toMonoidHom).comp
    (MulEquiv.piUnits (M := fun _ : Fin 3 => F)).symm.toMonoidHom

theorem coe_diagGL3 (w : Fin 3 → Fˣ) :
    ((diagGL3 w : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal (fun i => (w i : F)) := rfl

@[expose] noncomputable def pglDiag3 : (Fin 3 → Fˣ) →* Matrix.ProjGenLinGroup (Fin 3) F := mk.comp diagGL3

theorem diagGL3_mem_center {w : Fin 3 → Fˣ} (h : diagGL3 w ∈ Subgroup.center (GL (Fin 3) F)) :
    w 0 = w 1 ∧ w 1 = w 2 := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨a, ha⟩ := h
  have h' := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) ha
  have e0 := congrFun (congrFun h' 0) 0
  have e1 := congrFun (congrFun h' 1) 1
  have e2 := congrFun (congrFun h' 2) 2
  simp [coe_diagGL3, Matrix.diagonal_apply_eq] at e0 e1 e2
  exact ⟨Units.ext (e0.symm.trans e1), Units.ext (e1.symm.trans e2)⟩

theorem hasIndepPair_pglDiag3 {u : Fˣ} (hu : orderOf u = 3) :
    ∃ w₁ w₂ : Fin 3 → Fˣ, Commute (pglDiag3 (F := F) w₁) (pglDiag3 w₂) ∧
      pglDiag3 (F := F) w₁ ^ 3 = 1 ∧ pglDiag3 (F := F) w₂ ^ 3 = 1 ∧
      (∀ i j : ℤ, pglDiag3 (F := F) w₁ ^ i * pglDiag3 w₂ ^ j = 1 → (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j) ∧
      (∀ i, w₁ i ∈ Subgroup.zpowers u ∧ w₂ i ∈ Subgroup.zpowers u) := by
  let w₁ : Fin 3 → Fˣ := ![1, 1, u]
  let w₂ : Fin 3 → Fˣ := ![1, u, 1]
  have hu3 : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hw₁ : ∀ i, w₁ i ∈ Subgroup.zpowers u := fun i => by
    fin_cases i <;> simp [w₁, Subgroup.one_mem, Subgroup.mem_zpowers]
  have hw₂ : ∀ i, w₂ i ∈ Subgroup.zpowers u := fun i => by
    fin_cases i <;> simp [w₂, Subgroup.one_mem, Subgroup.mem_zpowers]
  refine ⟨w₁, w₂, (Commute.all w₁ w₂).map pglDiag3, ?_, ?_, ?_, fun i => ⟨hw₁ i, hw₂ i⟩⟩
  · rw [← map_pow]
    have : w₁ ^ 3 = 1 := by
      funext i
      fin_cases i <;> simp [w₁, hu3]
    rw [this, map_one]
  · rw [← map_pow]
    have : w₂ ^ 3 = 1 := by
      funext i
      fin_cases i <;> simp [w₂, hu3]
    rw [this, map_one]
  · intro i j hij
    rw [← map_zpow, ← map_zpow, ← map_mul] at hij
    have hij' : diagGL3 (w₁ ^ i * w₂ ^ j) ∈ Subgroup.center (GL (Fin 3) F) := by
      rw [← mk_eq_one]
      exact hij
    have hc := diagGL3_mem_center hij'
    have e0 : (w₁ ^ i * w₂ ^ j) 0 = 1 := by simp [w₁, w₂]
    have e1 : (w₁ ^ i * w₂ ^ j) 1 = u ^ j := by simp [w₁, w₂]
    have e2 : (w₁ ^ i * w₂ ^ j) 2 = u ^ i := by simp [w₁, w₂]
    have hj : u ^ j = 1 := by rw [← e1, ← hc.1, e0]
    have hi : u ^ i = 1 := by rw [← e2, ← hc.2, ← hc.1, e0]
    refine ⟨?_, ?_⟩
    · have := (orderOf_dvd_iff_zpow_eq_one (x := u) (i := i)).2 hi
      rw [hu] at this
      exact_mod_cast this
    · have := (orderOf_dvd_iff_zpow_eq_one (x := u) (i := j)).2 hj
      rw [hu] at this
      exact_mod_cast this

theorem exists_unit_orderOf_three [Finite F] (h : 3 ∣ Nat.card F - 1) :
    ∃ u : Fˣ, orderOf u = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h' : 3 ∣ Nat.card Fˣ := by rw [Nat.card_units]; exact h
  exact exists_prime_orderOf_dvd_card' 3 h'

theorem hasIndepPair_of_diag_mem {u : Fˣ} (hu : orderOf u = 3)
    {S : Subgroup (Matrix.ProjGenLinGroup (Fin 3) F)}
    (hS : ∀ w : Fin 3 → Fˣ, (∀ i, w i ∈ Subgroup.zpowers u) → pglDiag3 w ∈ S) :
    HasIndepPair 3 ↥S := by
  obtain ⟨w₁, w₂, hc, h1, h2, hi, hw⟩ := hasIndepPair_pglDiag3 (F := F) hu
  have m₁ : pglDiag3 w₁ ∈ S := hS w₁ fun i => (hw i).1
  have m₂ : pglDiag3 w₂ ∈ S := hS w₂ fun i => (hw i).2
  refine ⟨⟨pglDiag3 w₁, m₁⟩, ⟨pglDiag3 w₂, m₂⟩, Subtype.ext hc, Subtype.ext ?_, Subtype.ext ?_,
    fun i j hij => hi i j ?_⟩
  · simpa using h1
  · simpa using h2
  · simpa using congrArg Subtype.val hij

theorem hasIndepPair_pgl_three [Finite F] (h : 3 ∣ Nat.card F - 1) :
    HasIndepPair 3 (Matrix.ProjGenLinGroup (Fin 3) F) := by
  obtain ⟨u, hu⟩ := exists_unit_orderOf_three h
  have := hasIndepPair_of_diag_mem (F := F) hu (S := ⊤) (fun w _ => Subgroup.mem_top _)
  exact HasIndepPair.of_mulEquiv Subgroup.topEquiv this

theorem diagGL3_mem_glPi_false {q : ℕ} (hq : 1 ≤ q) {w : Fin 3 → Fˣ}
    (hw : ∀ i, w i ^ (q + 1) = 1) : diagGL3 w ∈ glPi false 3 q F := by
  refine Subgroup.subset_closure ?_
  change (((diagGL3 w : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map (· ^ q))ᵀ *
    ((diagGL3 w : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1
  rw [coe_diagGL3, Matrix.diagonal_map (by simp [zero_pow (by omega : q ≠ 0)]),
    Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  have := congrArg (fun x : Fˣ => (x : F)) (hw i)
  simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
  rw [pow_succ] at this
  exact this

theorem hasIndepPair_projImage_glPi_false {q : ℕ} (hq : 1 ≤ q) [Finite F]
    (hF : Nat.card F = q ^ 2) (h3 : 3 ∣ q + 1) :
    HasIndepPair 3 ↥(CFSG.PGLModel.projImage (glPi false 3 q F)) := by
  have hd : 3 ∣ Nat.card F - 1 := by
    rw [hF]
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    have h2 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      zify [hq, h1]
      ring
    rw [h2]
    exact Dvd.dvd.mul_left h3 _
  obtain ⟨u, hu⟩ := exists_unit_orderOf_three hd
  have hu1 : u ^ (q + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hu]; exact h3)
  refine hasIndepPair_of_diag_mem hu fun w hw => ?_
  refine ⟨diagGL3 w, diagGL3_mem_glPi_false hq (fun i => ?_), rfl⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hw i)
  rw [← hk, ← zpow_natCast (u ^ k) (q + 1), ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
    zpow_natCast, hu1, _root_.one_zpow]

end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
