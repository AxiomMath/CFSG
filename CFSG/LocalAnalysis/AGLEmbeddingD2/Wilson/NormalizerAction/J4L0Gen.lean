module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4Slp
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.ThetaDefs
public import Certificates.Certificate12611

public noncomputable section

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ CFSG.SectionRank.Native
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Quasithin.J4M2
  CFSG.Quasithin.J4Loc
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem z0_mem_closure_of_prod {p : ℕ} (hp : p.Prime) {a b : J}
    (ha : a ∈ Coordinator.L0) (hb : b ∈ Coordinator.L0)
    (ha1 : a ^ p = 1) (hb1 : b ^ p = 1) (ha0 : a ≠ 1) (hb0 : b ≠ 1)
    (hab : (a * b) ^ p = z0) :
    z0 ∈ Subgroup.closure {g : J | g ∈ Coordinator.L0 ∧ orderOf g = p} := by
  have : Fact p.Prime := ⟨hp⟩
  have hao : orderOf a = p := orderOf_eq_prime ha1 ha0
  have hbo : orderOf b = p := orderOf_eq_prime hb1 hb0
  have hmem : ∀ g, g ∈ ({g : J | g ∈ Coordinator.L0 ∧ orderOf g = p} : Set J) →
      g ∈ Subgroup.closure {g : J | g ∈ Coordinator.L0 ∧ orderOf g = p} := fun g hg =>
    Subgroup.subset_closure hg
  rw [← hab]
  exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (hmem a ⟨ha, hao⟩) (hmem b ⟨hb, hbo⟩)) p

section Main


theorem l0OK_true : l0OK = true := Certificates.certificate12611

theorem l0OK_parts :
    l0Prog.all (Instr.lt l0N) = true ∧ cEOK = true ∧ gamZ0OK = true ∧
    O.eq (O.mul gamZ0 gamZ0) O.one = true ∧ l0Elt 160 7 = true ∧ l0Elt 161 7 = true ∧
    l0Elt 162 11 = true ∧ l0Elt 163 11 = true ∧
    O.eq (O.pow (mulP (l0P 160) (l0P 161)).1 7) gamZ0 = true ∧
    O.eq (O.pow (mulP (l0P 162) (l0P 163)).1 11) gamZ0 = true := by
  have h := l0OK_true
  unfold l0OK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem rep_z0_of (h1 : gamZ0OK = true) (h2 : O.eq (O.mul gamZ0 gamZ0) O.one = true) :
    Rep Sp φ z0 gamZ0P := by
  have hsz : gamZ0.size = 112 := by
    have h := h1
    unfold gamZ0OK at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact h.1.2
  have hzM : CFSG.Quasithin.J4M2.zM = pairRows gamZ0P := by
    have h := h1
    unfold gamZ0OK at h
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
    obtain ⟨⟨h1', h2'⟩, h3⟩ := h
    refine Array.ext (by rw [h1']; simp [pairRows, gamZ0P, h2']) fun i hi _ => ?_
    have hi' : i < 112 := by rwa [h1'] at hi
    have e := V2.beq_iff.1 (h3 i hi')
    rw [getElem!_pos _ i (by omega)] at e
    have hg : i < gamZ0.size := by omega
    rw [getElem!_pos gamZ0 i hg] at e
    simpa [pairRows, gamZ0P] using e
  have hMx : Mx z0 = CFSG.Sporadic.SmallF2.rowsMatrix 112 gamZ0 := by
    rw [← CFSG.Quasithin.J4M2.rowsMatrix_zM matFacts, hzM, rowsMatrix_pairRows]
    rfl
  have hwf : Sp.WF gamZ0 := hsz
  have hz : Sp.toMat gamZ0 = φ z0 := hMx.symm
  have hsq : Sp.toMat gamZ0 * Sp.toMat gamZ0 = 1 := by
    have e := Sp.toMat_eq (Sp.mul_wf hwf hwf) Sp.one_wf h2
    rwa [Sp.toMat_mul hwf hwf, Sp.toMat_one] at e
  have hinv : z0⁻¹ = z0 := by
    refine inv_eq_of_mul_eq_one_right (φ_injective ?_)
    rw [map_mul, ← hz, hsq, map_one]
  refine ⟨hwf, hwf, hz, ?_⟩
  rw [hinv]
  exact hz

@[expose] def lE (r : ℕ) : J := slpRegs l0Prog r

theorem rep_l0Reg {r : ℕ} (hr : r < l0N) : Rep Sp φ (lE r) (l0P r) :=
  rep_slpRegs (n := l0N) l0OK_parts.1 hr

theorem rep_cE_l0 : Rep Sp φ cE cEP := rep_cE_of l0OK_parts.2.1

theorem rep_z0_l0 : Rep Sp φ z0 gamZ0P := rep_z0_of l0OK_parts.2.2.1 l0OK_parts.2.2.2.1

theorem l0Elt_spec {r p : ℕ} (hr : r < l0N) (h : l0Elt r p = true) :
    lE r ∈ Coordinator.L0 ∧ lE r ^ p = 1 ∧ lE r ≠ 1 := by
  unfold l0Elt at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hr' := rep_l0Reg hr
  refine ⟨Coordinator.mem_L0_iff.2 ⟨?_, ?_⟩, ?_, ?_⟩
  · exact eq_of_rep (rep_mulP hr' rep_z0_l0) (rep_mulP rep_z0_l0 hr') h1
  · exact eq_of_rep (rep_mulP hr' rep_cE_l0) (rep_mulP rep_cE_l0 hr') h2
  · exact eq_of_rep (rep_powP hr' p) rep_oneP h3
  · intro e
    refine ne_of_neOK hr'.1 Sp.one_wf h4 ?_
    rw [hr'.2.2.1, e, map_one, Sp.toMat_one]

theorem z0_mem_closure_orderSeven :
    z0 ∈ Subgroup.closure {g : J | g ∈ Coordinator.L0 ∧ orderOf g = 7} := by
  obtain ⟨ha, ha1, ha0⟩ := l0Elt_spec (r := 160) (by unfold l0N; omega) l0OK_parts.2.2.2.2.1
  obtain ⟨hb, hb1, hb0⟩ := l0Elt_spec (r := 161) (by unfold l0N; omega) l0OK_parts.2.2.2.2.2.1
  refine z0_mem_closure_of_prod (by norm_num) ha hb ha1 hb1 ha0 hb0 ?_
  exact eq_of_rep (rep_powP (rep_mulP (rep_l0Reg (r := 160) (by unfold l0N; omega))
    (rep_l0Reg (r := 161) (by unfold l0N; omega))) 7) rep_z0_l0 l0OK_parts.2.2.2.2.2.2.2.2.1

theorem z0_mem_closure_orderEleven :
    z0 ∈ Subgroup.closure {g : J | g ∈ Coordinator.L0 ∧ orderOf g = 11} := by
  obtain ⟨ha, ha1, ha0⟩ := l0Elt_spec (r := 162) (by unfold l0N; omega)
    l0OK_parts.2.2.2.2.2.2.1
  obtain ⟨hb, hb1, hb0⟩ := l0Elt_spec (r := 163) (by unfold l0N; omega)
    l0OK_parts.2.2.2.2.2.2.2.1
  refine z0_mem_closure_of_prod (by norm_num) ha hb ha1 hb1 ha0 hb0 ?_
  exact eq_of_rep (rep_powP (rep_mulP (rep_l0Reg (r := 162) (by unfold l0N; omega))
    (rep_l0Reg (r := 163) (by unfold l0N; omega))) 11) rep_z0_l0
    l0OK_parts.2.2.2.2.2.2.2.2.2

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
