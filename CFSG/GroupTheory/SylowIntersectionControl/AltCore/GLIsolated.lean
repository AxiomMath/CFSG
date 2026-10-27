module

public import CFSG.GroupTheory.SylowIntersectionControl.IsolatedEmbedded
import CFSG.RankThree.PartOne.CTP.StrongPGlue

public section

namespace CFSG.GroupTheory.AltCore

open Subgroup CFSG.RankThree.PartOne.StrongP

section Transvections

variable {e : ℕ}

private def tv {i j : Fin e} (h : i ≠ j) : GL (Fin e) (ZMod 2) :=
  Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection h 1)

private theorem coe_tv {i j : Fin e} (h : i ≠ j) :
    ((tv h : GL (Fin e) (ZMod 2)) : Matrix (Fin e) (Fin e) (ZMod 2)) =
      1 + Matrix.single i j 1 := rfl

private theorem tv_sq {i j : Fin e} (h : i ≠ j) : tv h ^ 2 = 1 := by
  unfold tv
  rw [← map_pow, sq, ← Matrix.SpecialLinearGroup.transvection_add h 1 1,
    show (1 + 1 : ZMod 2) = 0 from by decide, Matrix.SpecialLinearGroup.transvection_coeff_zero,
    map_one]

private theorem tv_ne_one {i j : Fin e} (h : i ≠ j) : tv h ≠ 1 := by
  intro h1
  have := congrArg (fun g : GL (Fin e) (ZMod 2) => (g : Matrix (Fin e) (Fin e) (ZMod 2)) i j) h1
  simp [coe_tv, h] at this

private theorem tv_commute {i j k l : Fin e} (h : i ≠ j) (h' : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) : Commute (tv h) (tv h') := by
  refine Units.ext ?_
  simp only [Units.val_mul, coe_tv, add_mul, mul_add, one_mul, mul_one,
    Matrix.single_mul_single_of_ne _ _ _ _ hjk, Matrix.single_mul_single_of_ne _ _ _ _ hli]
  abel

private def tvSet (e : ℕ) : Set (GL (Fin e) (ZMod 2)) :=
  {g | ∃ (i j : Fin e) (h : i ≠ j), g = tv h}

private def InClosure (N : Matrix (Fin e) (Fin e) (ZMod 2)) : Prop :=
  ∃ x ∈ Subgroup.closure (tvSet e), (x : Matrix (Fin e) (Fin e) (ZMod 2)) = N

private theorem inClosure_diagonal (D : Fin e → ZMod 2) (hD : (Matrix.diagonal D).det ≠ 0) :
    InClosure (Matrix.diagonal D) := by
  have hD1 : D = fun _ => 1 := by
    funext i
    have hi : D i ≠ 0 := Finset.prod_ne_zero_iff.mp (by simpa [Matrix.det_diagonal] using hD) i
      (Finset.mem_univ i)
    revert hi
    generalize D i = x
    revert x
    decide
  exact ⟨1, one_mem _, by simp [hD1]⟩

private theorem inClosure_transvection (t : Matrix.TransvectionStruct (Fin e) (ZMod 2)) :
    InClosure t.toMatrix := by
  have hc : t.c = 0 ∨ t.c = 1 := by
    generalize t.c = x
    revert x
    decide
  rcases hc with hc | hc
  · exact ⟨1, one_mem _, by simp [Matrix.TransvectionStruct.toMatrix, hc]⟩
  · refine ⟨tv t.hij, subset_closure ⟨_, _, t.hij, rfl⟩, ?_⟩
    simp [Matrix.TransvectionStruct.toMatrix, Matrix.transvection, coe_tv, hc]

private theorem inClosure_mul {A B : Matrix (Fin e) (Fin e) (ZMod 2)} (hA : InClosure A)
    (hB : InClosure B) : InClosure (A * B) := by
  obtain ⟨x, hx, rfl⟩ := hA
  obtain ⟨y, hy, rfl⟩ := hB
  exact ⟨x * y, mul_mem hx hy, Units.val_mul x y⟩

private theorem closure_tvSet : Subgroup.closure (tvSet e) = ⊤ := by
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨x, hx, hxg⟩ := Matrix.diagonal_transvection_induction_of_det_ne_zero InClosure
    (g : Matrix (Fin e) (Fin e) (ZMod 2)) (Matrix.GeneralLinearGroup.det_ne_zero g)
    (fun D hD => inClosure_diagonal D hD) inClosure_transvection
    (fun A B _ _ hA hB => inClosure_mul hA hB)
  rwa [← Units.ext hxg]

private theorem tv_mem_of_forall_commute {Q : Subgroup (GL (Fin e) (ZMod 2))} (he : 3 ≤ e)
    (hQ : ∀ t ∈ Q, t ≠ 1 → t ^ 2 = 1 → ∀ s, Commute t s → s ∈ Q) {i j : Fin e}
    (hij : i ≠ j) (hQij : tv hij ∈ Q) {k l : Fin e} (hkl : k ≠ l) : tv hkl ∈ Q := by
  obtain ⟨m, hmi, hmk⟩ := Fin.exists_ne_and_ne_of_two_lt i k (by omega)
  have step : ∀ {a b c d : Fin e} (h₁ : a ≠ b) (h₂ : c ≠ d), b ≠ c → d ≠ a → tv h₁ ∈ Q →
      tv h₂ ∈ Q := fun h₁ h₂ hbc hda h =>
    hQ _ h (tv_ne_one h₁) (tv_sq h₁) _ (tv_commute h₁ h₂ hbc hda)
  have h₁ : tv (hmi.symm : i ≠ m) ∈ Q := step hij hmi.symm hij.symm hmi hQij
  have h₂ : tv (hmk.symm : k ≠ m) ∈ Q := step hmi.symm hmk.symm hmk hmi h₁
  exact step hmk.symm hkl hmk hkl.symm h₂

end Transvections

theorem not_isPIsolatedOver_GL_two {e : ℕ} (he : 3 ≤ e) :
    ¬ IsPIsolatedOver 2 (⊤ : Subgroup (GL (Fin e) (ZMod 2))) ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  obtain ⟨M, hM⟩ := isPIsolatedOver_top_bot_iff.mp h
  have h01 : (⟨0, by omega⟩ : Fin e) ≠ ⟨1, by omega⟩ := fun h => by simpa using congrArg Fin.val h
  obtain ⟨S, hS⟩ :=
    (isPGroup_zpowers_of_pow_eq_one (p := 2) (x := tv h01) (tv_sq h01)).exists_le_sylow
  obtain ⟨g, hg⟩ := hM.exists_conj_ge (P := S)
    ⟨le_top, S.isPGroup', by rw [relIndex_top_right]; exact S.not_dvd_index⟩
  have hM' := hM.conj g
  have hQ : ∀ t ∈ conjSub g M, t ≠ 1 → t ^ 2 = 1 → ∀ s, Commute t s → s ∈ conjSub g M :=
    fun t ht ht1 ht2 s hts =>
      hM'.centralizer_le ht1 ht2 ht (mem_centralizer_singleton_iff.mpr hts.eq.symm)
  refine hM'.1 (eq_top_iff.mpr ?_)
  rw [← closure_tvSet, closure_le]
  rintro _ ⟨i, j, hij, rfl⟩
  exact tv_mem_of_forall_commute he hQ h01 (hg (hS (mem_zpowers _))) hij

end CFSG.GroupTheory.AltCore
