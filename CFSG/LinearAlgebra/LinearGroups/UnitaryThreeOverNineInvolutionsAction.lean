module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutionsCentralizer

public section

namespace CFSG.LinearGroups.UnitaryThreeOverNine

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F] {h : UnitaryFieldData 3 1 F} {hF : Nat.card F = 9}

theorem lineAct_eq_self_iff (g : StatedSU 3 3 F) (L : NonisoLine F) :
    lineAct hF g L = L ↔ g ∈ Subgroup.centralizer {(tauLine h hF L : StatedSU 3 3 F)} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hgL
    have := tauLine_lineAct h hF g L
    rw [hgL, eq_mul_inv_iff_mul_eq] at this
    exact this.symm
  · intro hc
    apply tauLine_injective (h := h) (hF := hF)
    apply Subtype.ext
    rw [tauLine_lineAct, hc, mul_inv_cancel_right]

theorem exists_lineAct_eq (hF : Nat.card F = 9) {L₀ : NonisoLine F}
    (hL₀ : L₀.1 = F ∙ ![1, 0, 0]) (L : NonisoLine F) : ∃ g, lineAct hF g L₀ = L := by
  have h := unitaryFieldData_of_card hF
  have : Finite (NonisoLine F) :=
    Nat.finite_of_card_ne_zero (by rw [card_nonisoLine hF]; norm_num)
  let _ : MulAction (StatedSU 3 3 F) (NonisoLine F) :=
    { smul := lineAct hF, one_smul := lineAct_one hF, mul_smul := lineAct_mul hF }
  have hstab : MulAction.stabilizer (StatedSU 3 3 F) L₀ =
      Subgroup.centralizer {(tauLine h hF L₀ : StatedSU 3 3 F)} := by
    ext g
    rw [MulAction.mem_stabilizer_iff]
    exact lineAct_eq_self_iff g L₀
  have hidx := MulAction.index_stabilizer (StatedSU 3 3 F) L₀
  have hmul := (MulAction.stabilizer (StatedSU 3 3 F) L₀).index_mul_card
  rw [hstab] at hidx hmul
  rw [card_centralizer_tauLine hL₀, card_statedSU hF] at hmul
  have horb : MulAction.orbit (StatedSU 3 3 F) L₀ = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
    rw [Set.ncard_univ, card_nonisoLine hF, ← hidx]
    omega
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (horb ▸ Set.mem_univ L)
  exact ⟨g, hg⟩

theorem lineAct_transitive (hF : Nat.card F = 9) (L L' : NonisoLine F) :
    ∃ g, lineAct hF g L = L' := by
  have h := unitaryFieldData_of_card hF
  have hv : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) ![1, 0, 0] ![1, 0, 0] ≠ 0 := by
    rw [gramForm_e0_left]
    exact one_ne_zero
  obtain ⟨g, rfl⟩ := exists_lineAct_eq hF (L₀ := lineOf _ hv) rfl L
  obtain ⟨g', rfl⟩ := exists_lineAct_eq hF (L₀ := lineOf _ hv) rfl L'
  refine ⟨g' * g⁻¹, ?_⟩
  rw [← lineAct_mul, mul_assoc, inv_mul_cancel, mul_one]

theorem isConj_of_orderOf_eq_two (hF : Nat.card F = 9) {a b : StatedSU 3 3 F}
    (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b := by
  have h := unitaryFieldData_of_card hF
  obtain ⟨L, hL⟩ := tauLine_surjective (h := h) (hF := hF) ⟨a, ha⟩
  obtain ⟨M, hM⟩ := tauLine_surjective (h := h) (hF := hF) ⟨b, hb⟩
  obtain ⟨g, hg⟩ := lineAct_transitive hF L M
  have := tauLine_lineAct h hF g L
  rw [hg, hM, hL] at this
  exact isConj_iff.mpr ⟨g, this.symm⟩

theorem exists_mulVec_eq_smul (g : StatedSU 3 3 F) {v : Fin 3 → F}
    (hv : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v ≠ 0)
    (hg : (lineAct hF g (lineOf v hv)).1 = (lineOf v hv).1) :
    ∃ c : F, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = c • v := by
  have hmem : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈
      (lineAct hF g (lineOf v hv)).1 := by
    rw [lineAct_val]
    exact ⟨v, Submodule.mem_span_singleton_self v, Matrix.toLin'_apply _ _⟩
  rw [hg] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨c, hc.symm⟩

theorem eq_one_of_lineAct_eq (hF : Nat.card F = 9) (g : StatedSU 3 3 F)
    (hg : ∀ L : NonisoLine F, (lineAct hF g L).1 = L.1) : g = 1 := by
  have h := unitaryFieldData_of_card hF
  have h2 := two_ne_zero' h
  set G := ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hG
  have hn : ∀ v : Fin 3 → F, ∑ j, v j ^ 3 * v j ≠ 0 → ∃ c : F, G *ᵥ v = c • v := fun v hv =>
    exists_mulVec_eq_smul (h := h) g ((gramForm_self_ne_zero_iff v).mpr hv) (hg _)
  have hn2 : (1 : F) + 1 ≠ 0 := by rw [one_add_one_eq_two]; exact h2
  obtain ⟨a, ha⟩ := hn ![1, 0, 0] (by simp [Fin.sum_univ_three])
  obtain ⟨b, hb⟩ := hn ![0, 1, 0] (by simp [Fin.sum_univ_three])
  obtain ⟨c, hc⟩ := hn ![0, 0, 1] (by simp [Fin.sum_univ_three])
  obtain ⟨d, hd⟩ := hn ![1, 1, 0] (by simpa [Fin.sum_univ_three] using hn2)
  obtain ⟨d', hd'⟩ := hn ![1, 0, 1] (by simpa [Fin.sum_univ_three] using hn2)
  have e1 : (![1, 1, 0] : Fin 3 → F) = ![1, 0, 0] + ![0, 1, 0] := by
    funext k
    fin_cases k <;> simp
  have e2 : (![1, 0, 1] : Fin 3 → F) = ![1, 0, 0] + ![0, 0, 1] := by
    funext k
    fin_cases k <;> simp
  rw [e1, Matrix.mulVec_add, ha, hb] at hd
  rw [e2, Matrix.mulVec_add, ha, hc] at hd'
  have had : a = d := by simpa using congrFun hd 0
  have hbd : b = d := by simpa using congrFun hd 1
  have had' : a = d' := by simpa using congrFun hd' 0
  have hcd : c = d' := by simpa using congrFun hd' 2
  have hGa : G = a • 1 := by
    refine Matrix.ext_iff_mulVec.mpr fun y => ?_
    have hy : y = y 0 • ![1, 0, 0] + y 1 • ![0, 1, 0] + y 2 • ![0, 0, 1] := by
      funext k
      fin_cases k <;> simp
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, hy, Matrix.mulVec_add, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, ha, hb, hc, hbd, hcd, ← had,
      ← had']
    module
  have hgSU : (g : GL (Fin 3) F) ∈ gramSU h 1 := by
    rw [← statedSU_eq_gramSU hF h]
    exact g.2
  have hdet := (mem_gramSU_iff_isometry.mp hgSU).2
  rw [← hG, hGa, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at hdet
  have hnorm := isometry_of_mem hF h g ![1, 0, 0] ![1, 0, 0]
  rw [← hG, ha, gramForm_smul_smul, gramForm_e0_left] at hnorm
  have hnorm' : a * a ^ 3 = 1 := by
    rw [UnitaryFieldData.norm, bar_eq_cube h] at hnorm
    simpa using hnorm
  have ha1 : a = 1 := by
    calc a = a * a ^ 3 := by rw [hdet, mul_one]
      _ = 1 := hnorm'
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_one, Units.val_one, ← hG, hGa, ha1, one_smul]

end CFSG.LinearGroups.UnitaryThreeOverNine
