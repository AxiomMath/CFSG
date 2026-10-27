module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.Transv

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

theorem gen_perp_cases : ∀ h : V3, h ⬝ᵥ (![1, 0, 0] + ![0, 1, 0]) = 0 →
    h = 0 ∨ h = ![1, 1, 0] ∨ h = ![0, 0, 1] ∨ h = ![1, 1, 1] := by
  decide +kernel

theorem gen_tv_swap : tvMat (![1, 0, 0] + ![0, 1, 0]) ![1, 1, 0] =
    tvMat ![1, 0, 0] ![0, 1, 0] * tvMat ![0, 1, 0] ![1, 0, 0] * tvMat ![1, 0, 0] ![0, 1, 0] := by
  decide +kernel

theorem gen_tv_vert : tvMat (![1, 0, 0] + ![0, 1, 0]) ![0, 0, 1] =
    tvMat ![1, 0, 0] ![0, 0, 1] * tvMat ![0, 1, 0] ![0, 0, 1] := by
  decide +kernel

theorem gen_tv_all : tvMat (![1, 0, 0] + ![0, 1, 0]) ![1, 1, 1] =
    tvMat (![1, 0, 0] + ![0, 1, 0]) ![1, 1, 0] * tvMat (![1, 0, 0] + ![0, 1, 0]) ![0, 0, 1] := by
  decide +kernel

theorem gen_Spt_add_le_std :
    Spt (![1, 0, 0] + ![0, 1, 0]) ≤ Spt ![1, 0, 0] ⊔ Spt ![0, 1, 0] := by
  intro g hg
  obtain ⟨h, hh, rfl⟩ := mem_Spt_iff.1 hg
  have hA : tvGL ![1, 0, 0] ![0, 1, 0] (by decide +kernel) ∈ Spt ![1, 0, 0] ⊔ Spt ![0, 1, 0] :=
    mem_sup_left (tv_tvGL_mem_Spt _ _ _)
  have hB : tvGL ![0, 1, 0] ![1, 0, 0] (by decide +kernel) ∈ Spt ![1, 0, 0] ⊔ Spt ![0, 1, 0] :=
    mem_sup_right (tv_tvGL_mem_Spt _ _ _)
  have hC : tvGL ![1, 0, 0] ![0, 0, 1] (by decide +kernel) ∈ Spt ![1, 0, 0] ⊔ Spt ![0, 1, 0] :=
    mem_sup_left (tv_tvGL_mem_Spt _ _ _)
  have hD : tvGL ![0, 1, 0] ![0, 0, 1] (by decide +kernel) ∈ Spt ![1, 0, 0] ⊔ Spt ![0, 1, 0] :=
    mem_sup_right (tv_tvGL_mem_Spt _ _ _)
  have hswap : tvGL (![1, 0, 0] + ![0, 1, 0]) ![1, 1, 0] (by decide +kernel) ∈
      Spt ![1, 0, 0] ⊔ Spt ![0, 1, 0] := by
    have : tvGL (![1, 0, 0] + ![0, 1, 0]) ![1, 1, 0] (by decide +kernel) =
        tvGL ![1, 0, 0] ![0, 1, 0] (by decide +kernel) *
          tvGL ![0, 1, 0] ![1, 0, 0] (by decide +kernel) *
            tvGL ![1, 0, 0] ![0, 1, 0] (by decide +kernel) := Units.ext gen_tv_swap
    rw [this]
    exact mul_mem (mul_mem hA hB) hA
  have hvert : tvGL (![1, 0, 0] + ![0, 1, 0]) ![0, 0, 1] (by decide +kernel) ∈
      Spt ![1, 0, 0] ⊔ Spt ![0, 1, 0] := by
    have : tvGL (![1, 0, 0] + ![0, 1, 0]) ![0, 0, 1] (by decide +kernel) =
        tvGL ![1, 0, 0] ![0, 0, 1] (by decide +kernel) *
          tvGL ![0, 1, 0] ![0, 0, 1] (by decide +kernel) := Units.ext gen_tv_vert
    rw [this]
    exact mul_mem hC hD
  rcases gen_perp_cases h hh with rfl | rfl | rfl | rfl
  · rw [(tvGL_eq_one_iff _ _ hh).2 (Or.inr rfl)]
    exact one_mem _
  · exact hswap
  · exact hvert
  · have : tvGL (![1, 0, 0] + ![0, 1, 0]) ![1, 1, 1] hh =
        tvGL (![1, 0, 0] + ![0, 1, 0]) ![1, 1, 0] (by decide +kernel) *
          tvGL (![1, 0, 0] + ![0, 1, 0]) ![0, 0, 1] (by decide +kernel) := Units.ext gen_tv_all
    rw [this]
    exact mul_mem hswap hvert

theorem Spt_add_le {p q : V3} (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p ≠ q) :
    Spt (p + q) ≤ Spt p ⊔ Spt q := by
  obtain ⟨g, h1, h2⟩ := tv_exists_pair_basis hp hq hpq
  have e1 : Spt p = (Spt ![1, 0, 0]).map (MulAut.conj g).toMonoidHom := by
    rw [Spt_conj, h1]
  have e2 : Spt q = (Spt ![0, 1, 0]).map (MulAut.conj g).toMonoidHom := by
    rw [Spt_conj, h2]
  have e3 : Spt (p + q) = (Spt (![1, 0, 0] + ![0, 1, 0])).map (MulAut.conj g).toMonoidHom := by
    rw [Spt_conj, act_add, h1, h2]
  rw [e1, e2, e3, ← Subgroup.map_sup]
  exact Subgroup.map_mono gen_Spt_add_le_std

theorem gen_det_three : ∀ p q r : V3, p ≠ 0 ∧ q ≠ 0 ∧ r ≠ 0 ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
    r ≠ p + q → (tv_colMat p q r).det = 1 := by
  decide +kernel

theorem gen_colMat_e2 : ∀ p q r : V3, (tv_colMat p q r).mulVec ![0, 0, 1] = r := by
  decide +kernel

theorem gen_exists_basis {p q r : V3} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) (h : r ≠ p + q) :
    ∃ g : GL32, act g ![1, 0, 0] = p ∧ act g ![0, 1, 0] = q ∧ act g ![0, 0, 1] = r := by
  have hd := gen_det_three p q r ⟨hp, hq, hr, hpq, hpr, hqr, h⟩
  exact ⟨Matrix.SpecialLinearGroup.toGL ⟨tv_colMat p q r, hd⟩, tv_colMat_e0 p q r,
    tv_colMat_e1 p q r, gen_colMat_e2 p q r⟩

theorem gen_single_cases : ∀ i : Fin 3, (Pi.single i 1 : V3) = ![1, 0, 0] ∨
    (Pi.single i 1 : V3) = ![0, 1, 0] ∨ (Pi.single i 1 : V3) = ![0, 0, 1] := by
  decide +kernel

theorem gen_single_perp :
    ∀ i j : Fin 3, i ≠ j → (Pi.single j 1 : V3) ⬝ᵥ (Pi.single i 1 : V3) = 0 := by
  decide +kernel

theorem gen_join_top : Spt ![1, 0, 0] ⊔ Spt ![0, 1, 0] ⊔ Spt ![0, 0, 1] = ⊤ := by
  set H : Subgroup GL32 := Spt ![1, 0, 0] ⊔ Spt ![0, 1, 0] ⊔ Spt ![0, 0, 1] with hH
  have hS : ∀ i : Fin 3, Spt (Pi.single i 1 : V3) ≤ H := by
    intro i
    rcases gen_single_cases i with h | h | h <;> rw [h]
    · exact le_trans le_sup_left le_sup_left
    · exact le_trans le_sup_right le_sup_left
    · exact le_sup_right
  have htv : ∀ (i j : Fin 3) (hij : i ≠ j) (a : ZMod 2),
      Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij a) ∈ H := by
    intro i j hij a
    rcases tv_zmod_two a with rfl | rfl
    · rw [Matrix.SpecialLinearGroup.transvection_coeff_zero, map_one]
      exact one_mem _
    · have hu := gen_single_perp i j hij
      have : Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij 1) =
          tvGL (Pi.single i 1) (Pi.single j 1) hu := by
        apply Units.ext
        show (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) + Matrix.single i j 1 = tvMat _ _
        rw [Matrix.single_eq_single_vecMulVec_single]
        rfl
      rw [this]
      exact hS i (tv_tvGL_mem_Spt _ _ hu)
  have key : ∀ M : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      Matrix.SpecialLinearGroup.toGL M ∈ H := by
    intro M
    refine Matrix.SpecialLinearGroup.diagonal_transvection_induction'
      (fun M => Matrix.SpecialLinearGroup.toGL M ∈ H) M ?_ htv ?_
    · intro i j hij c hc
      rcases tv_zmod_two c with h0 | h1
      · exact absurd h0 hc
      · subst h1
        have : Matrix.SpecialLinearGroup.diag2n hij (1 : ZMod 2) hc = 1 := by
          ext a b
          simp [Matrix.SpecialLinearGroup.diag2n_coe]
        show Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.diag2n hij 1 hc) ∈ H
        rw [this, map_one]
        exact one_mem _
    · intro A B hA hB
      show Matrix.SpecialLinearGroup.toGL (A * B) ∈ H
      rw [map_mul]
      exact mul_mem hA hB
  rw [eq_top_iff]
  intro g _
  have hdet : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
    have hu : IsUnit (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    rcases tv_zmod_two ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det) with h | h
    · rw [h] at hu
      exact absurd hu not_isUnit_zero
    · exact h
  have h2 : g = Matrix.SpecialLinearGroup.toGL ⟨(g : Matrix (Fin 3) (Fin 3) (ZMod 2)), hdet⟩ :=
    Units.ext rfl
  rw [h2]
  exact key _

theorem Spt_sup_three {p q r : V3} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) (h : r ≠ p + q) : Spt p ⊔ Spt q ⊔ Spt r = ⊤ := by
  obtain ⟨g, h1, h2, h3⟩ := gen_exists_basis hp hq hr hpq hpr hqr h
  have e1 : Spt p = (Spt ![1, 0, 0]).map (MulAut.conj g).toMonoidHom := by
    rw [Spt_conj, h1]
  have e2 : Spt q = (Spt ![0, 1, 0]).map (MulAut.conj g).toMonoidHom := by
    rw [Spt_conj, h2]
  have e3 : Spt r = (Spt ![0, 0, 1]).map (MulAut.conj g).toMonoidHom := by
    rw [Spt_conj, h3]
  rw [e1, e2, e3, ← Subgroup.map_sup, ← Subgroup.map_sup, gen_join_top]
  exact Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813
