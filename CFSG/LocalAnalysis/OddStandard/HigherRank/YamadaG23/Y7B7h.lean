module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7g

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_X0_decomp (c : Ctx7 G L) (hb : B5Std c) :
    ∀ a ∈ y7bX0 c.s, ∃ n ∈ f3X0 c.s, ∃ m ∈ M3 c.s, a = n * m := by
  intro a ha
  have haX : a ∈ y7bX c.s := y7b_X0_le_X c ha
  have hta : ⁅c.s.t, a⁆ ∈ M3 c.s := ha.2.2 c.s.t (y7b_t_mem_W c hb)
  have hat : ⁅a, c.s.t⁆ ∈ M3 c.s := by
    have h : ⁅a, c.s.t⁆ = (⁅c.s.t, a⁆)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h]
    exact (M3 c.s).inv_mem hta
  obtain ⟨n, hn, m, hm, ha_eq⟩ := (y7b_mem_C c hb).mp (y7b_cent_tbar c hb a haX hat)
  obtain ⟨hnH, hnB⟩ := Subgroup.mem_inf.mp hn
  refine ⟨n, Subgroup.mem_inf.mpr ⟨hnH, ?_⟩, m, hm, ha_eq⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hcommF : ∀ b ∈ c.s.fr.B, n * b * n⁻¹ * b⁻¹ ∈ c.s.fr.F := by
    intro b hbB
    have hba : ⁅b, a⁆ ∈ M3 c.s := ha.2.2 b (Subgroup.mem_sup_left hbB)
    have hbm0 : b * m⁻¹ * b⁻¹ ∈ M3 c.s :=
      (Subgroup.mem_normalizer_iff.mp (y7b_B_le_NM3 c hb hbB) m⁻¹).mp ((M3 c.s).inv_mem hm)
    have hbm : ⁅b, m⁻¹⁆ ∈ M3 c.s := by
      have h : ⁅b, m⁻¹⁆ = (b * m⁻¹ * b⁻¹) * m := by
        simp only [commutatorElement_def]; group
      rw [h]
      exact (M3 c.s).mul_mem hbm0 hm
    have hbam : a * ⁅b, m⁻¹⁆ * a⁻¹ ∈ M3 c.s :=
      (Subgroup.mem_normalizer_iff.mp ha.2.1 ⁅b, m⁻¹⁆).mp hbm
    have hn_eq : n = a * m⁻¹ := by rw [ha_eq]; group
    have hbnM3 : ⁅b, n⁆ ∈ M3 c.s := by
      rw [hn_eq]
      have h : ⁅b, a * m⁻¹⁆ = ⁅b, a⁆ * (a * ⁅b, m⁻¹⁆ * a⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [h]
      exact (M3 c.s).mul_mem hba hbam
    have hbnB : ⁅b, n⁆ ∈ c.s.fr.B := by
      have hconj : n * b⁻¹ * n⁻¹ ∈ c.s.fr.B :=
        (Subgroup.mem_normalizer_iff.mp hnB b⁻¹).mp ((c.s.fr.B).inv_mem hbB)
      have h : ⁅b, n⁆ = b * (n * b⁻¹ * n⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [h]
      exact (c.s.fr.B).mul_mem hbB hconj
    have hbnF : ⁅b, n⁆ ∈ c.s.fr.F := by
      rw [← y7b_B_inf_M3 c hb]
      exact Subgroup.mem_inf.mpr ⟨hbnB, hbnM3⟩
    have h : n * b * n⁻¹ * b⁻¹ = (⁅b, n⁆)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h]
    exact (c.s.fr.F).inv_mem hbnF
  have hnv : n * v = v * n := by
    calc n * v = n * v * n⁻¹ * n := by group
      _ = v * n := by rw [y7b_cent_V_of_comm_F hb.hH hnB hcommF v hv]
  exact hnv.symm

theorem y7b_X0_le_K (c : Ctx7 G L) (hb : B5Std c) : y7bX0 c.s ≤ y7bK c.s := by
  intro a ha
  obtain ⟨n, hn, m, hm, ha_eq⟩ := y7b_X0_decomp c hb a ha
  refine Subgroup.mem_inf.mpr ⟨y7b_X0_le_X c ha, ?_⟩
  rw [ha_eq, Subgroup.mem_centralizer_iff]
  intro v hv
  have hvM3 : v ∈ M3 c.s := by
    have hle : cen c.s.fr.B ≤ c.s.fr.F := by
      rw [← y7b_E_inf_F hb.hH]
      exact inf_le_right
    exact (le_sup_right : c.s.fr.F ≤ M3 c.s) (hle hv)
  haveI : IsMulCommutative ↥(M3 c.s) := (y7b_M3_elem c hb).1
  have hmv : v * m = m * v :=
    congrArg Subtype.val (mul_comm' (⟨v, hvM3⟩ : ↥(M3 c.s)) ⟨m, hm⟩)
  have hnv : v * n = n * v := (Subgroup.mem_centralizer_iff.mp hn.2) v hv
  calc v * (n * m) = (v * n) * m := by group
    _ = (n * v) * m := by rw [hnv]
    _ = n * (v * m) := by group
    _ = n * (m * v) := by rw [hmv]
    _ = (n * m) * v := by group

theorem y7b_X0_cosets (c : Ctx7 G L) (hb : B5Std c) :
    ∀ a ∈ y7bX0 c.s, ∀ b ∈ y7bX0 c.s, a ∈ y7bW c.s ∨ b ∈ y7bW c.s ∨ a⁻¹ * b ∈ y7bW c.s := by
  have hf3P_le_W : f3P c.s ≤ y7bW c.s := by
    rw [f3P, y7bW, y54_C3_eq_M3 c.toCtx5 hb.hH]
    exact sup_le le_sup_left (le_sup_right.trans le_sup_right)
  have hM3_le_W : M3 c.s ≤ y7bW c.s := by
    rw [y7bW, y54_C3_eq_M3 c.toCtx5 hb.hH]
    exact le_sup_left.trans le_sup_right
  intro a ha b hbX
  obtain ⟨n, hn, m, hm, rfl⟩ := y7b_X0_decomp c hb a ha
  obtain ⟨n', hn', m', hm', rfl⟩ := y7b_X0_decomp c hb b hbX
  rcases f3_X0_cosets hb.hH n hn n' hn' with hnP | hn'P | hnn'P
  · exact Or.inl ((y7bW c.s).mul_mem (hf3P_le_W hnP) (hM3_le_W hm))
  · exact Or.inr (Or.inl ((y7bW c.s).mul_mem (hf3P_le_W hn'P) (hM3_le_W hm')))
  · refine Or.inr (Or.inr ?_)
    have heq : (n * m)⁻¹ * (n' * m') = (m⁻¹ * (n⁻¹ * n')) * m' := by
      group
    rw [heq]
    exact (y7bW c.s).mul_mem
      ((y7bW c.s).mul_mem ((y7bW c.s).inv_mem (hM3_le_W hm)) (hf3P_le_W hnn'P))
      (hM3_le_W hm')

end CFSG.OddStandard.HigherRank.YamadaG23
