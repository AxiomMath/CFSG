module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4Fix11
public import Certificates.Certificate12607
public import CFSG.Sporadic.Schreier.J4SElevenBase1

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ CFSG.SectionRank.Native
  CFSG.Sporadic.SmallF2.Native CFSG.Quasithin.J4Loc CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem gamOK_spec :
    gamZ0OK = true ∧ O.eq (O.mul gamZ0 gamZ0) O.one = true ∧
      O.eq (gamConjP gamJP).1 gamZ0 = true ∧
      O.eq (mulP gamC1P gamJP).1 (mulP gamJP gamC1P).1 = true ∧
      O.eq (gamConjP gamC1P).1 gamAP.1 = true ∧ O.eq (gamConjP gamC1P).2 gamAP.2 = true ∧
      O.eq (gamConjP H2n).1 gamBP.1 = true ∧ O.eq (gamConjP H2n).2 gamBP.2 = true ∧
      O.eq (gamConjP QZn).1 gamZP.1 = true ∧ O.eq (gamConjP QZn).2 gamZP.2 = true := by
  have h : gamOK = true := Certificates.certificate12607
  unfold gamOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem wordProd_two_letters {G : Type*} [Group G] (x y : G) :
    wordProd (fun m => if m = 0 then x else y) Coordinator.hWord =
      CFSG.Sporadic.GLQ.signedWord x y gamWord := by
  simp [wordProd, CFSG.Sporadic.GLQ.signedWord, Coordinator.hWord, gamWord,
    CFSG.Sporadic.GLQ.letter]

theorem hW_eq_signedWord : Coordinator.hW = CFSG.Sporadic.GLQ.signedWord a b gamWord :=
  @wordProd_two_letters J (Subgroup.toGroup J) a b

theorem zM_eq_map :
    CFSG.Quasithin.J4M2.zM = pairRows gamZ0P := by
  have h := gamOK_spec.1
  unfold gamZ0OK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine Array.ext (by rw [h1]; simp [pairRows, gamZ0P, h2]) fun i hi _ => ?_
  have hi' : i < 112 := by rwa [h1] at hi
  have e := V2.beq_iff.1 (h3 i hi')
  rw [getElem!_pos _ i (by omega)] at e
  have hg : i < gamZ0.size := by omega
  rw [getElem!_pos gamZ0 i hg] at e
  simpa [pairRows, gamZ0P] using e

theorem Mx_z0_gam :
    Mx z0 = CFSG.Sporadic.SmallF2.rowsMatrix 112 gamZ0 := by
  rw [← CFSG.Quasithin.J4M2.rowsMatrix_zM matFacts, zM_eq_map, rowsMatrix_pairRows]
  rfl

theorem rep_gamZ0 :
    Rep Sp φ z0 gamZ0P := by
  have hsz : gamZ0.size = 112 := by
    have h := gamOK_spec.1
    unfold gamZ0OK at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact h.1.2
  have hwf : Sp.WF gamZ0 := hsz
  have hz : Sp.toMat gamZ0 = φ z0 := Mx_z0_gam.symm
  have hsq : Sp.toMat gamZ0 * Sp.toMat gamZ0 = 1 := by
    have e := Sp.toMat_eq (Sp.mul_wf hwf hwf) Sp.one_wf gamOK_spec.2.1
    rwa [Sp.toMat_mul hwf hwf, Sp.toMat_one] at e
  have hinv : z0⁻¹ = z0 := by
    refine inv_eq_of_mul_eq_one_right (φ_injective ?_)
    rw [map_mul, ← hz, hsq, map_one]
  refine ⟨hwf, hwf, hz, ?_⟩
  rw [hinv]
  exact hz

theorem rep_gamHW : Rep Sp φ Coordinator.hW gamHP := by
  rw [hW_eq_signedWord]
  exact rep_wordP (rep_a matFacts) (rep_b matFacts) gamWord

theorem rep_gamJ :
    Rep Sp φ Coordinator.jInv gamJP := rep_powP rep_nrm₂ 20

theorem rep_gamGam :
    Rep Sp φ Coordinator.gam gamGP :=
  rep_mulP (rep_powP (rep_mulP rep_gamZ0 (rep_mulP (rep_mulP rep_gamHW rep_gamJ)
    (rep_invP rep_gamHW))) 6) rep_gamHW

theorem rep_gamC1 :
    Rep Sp φ Coordinator.c1j gamC1P :=
  rep_mulP (rep_powP rep_qy 10) rep_nrm₁

theorem rep_gamConj
    {g : J} {P : Pair}
    (hg : Rep Sp φ g P) :
    Rep Sp φ (Coordinator.gam * g * Coordinator.gam⁻¹) (gamConjP P) :=
  rep_mulP (rep_mulP rep_gamGam hg) (rep_invP rep_gamGam)

theorem gam_conj_jInv :
    Coordinator.gam * Coordinator.jInv * Coordinator.gam⁻¹ = z0 :=
  eq_of_rep (rep_gamConj rep_gamJ) rep_gamZ0 gamOK_spec.2.2.1

theorem c1j_comm_jInv :
    Coordinator.c1j * Coordinator.jInv = Coordinator.jInv * Coordinator.c1j :=
  eq_of_rep (rep_mulP rep_gamC1 rep_gamJ) (rep_mulP rep_gamJ rep_gamC1) gamOK_spec.2.2.2.1

theorem rep_cA :
    Rep Sp φ Coordinator.cA gamAP := by
  have h := rep_gamConj rep_gamC1
  have e : gamConjP gamC1P = gamAP := Prod.ext
    (beq_iff_eq.1 gamOK_spec.2.2.2.2.1) (beq_iff_eq.1 gamOK_spec.2.2.2.2.2.1)
  rw [e] at h
  exact h

theorem rep_cB :
    Rep Sp φ Coordinator.cB gamBP := by
  have h := rep_gamConj rep_nrm₂
  have e : gamConjP H2n = gamBP := Prod.ext
    (beq_iff_eq.1 gamOK_spec.2.2.2.2.2.2.1) (beq_iff_eq.1 gamOK_spec.2.2.2.2.2.2.2.1)
  rw [e] at h
  exact h

theorem rep_cZ :
    Rep Sp φ Coordinator.cZ gamZP := by
  have h := rep_gamConj rep_qz
  have e : gamConjP QZn = gamZP := Prod.ext
    (beq_iff_eq.1 gamOK_spec.2.2.2.2.2.2.2.2.1) (beq_iff_eq.1 gamOK_spec.2.2.2.2.2.2.2.2.2)
  rw [e] at h
  exact h

theorem Mx_cA :
    Mx Coordinator.cA = CFSG.Sporadic.J4.rowsMatrix cArows := by
  rw [cArows, rowsMatrix_pairRows]
  exact rep_cA.2.2.1.symm

theorem Mx_cB :
    Mx Coordinator.cB = CFSG.Sporadic.J4.rowsMatrix cBrows := by
  rw [cBrows, rowsMatrix_pairRows]
  exact rep_cB.2.2.1.symm

theorem Mx_cZ :
    Mx Coordinator.cZ = CFSG.Sporadic.J4.rowsMatrix cZrows := by
  rw [cZrows, rowsMatrix_pairRows]
  exact rep_cZ.2.2.1.symm

theorem Mx_cAinv :
    Mx Coordinator.cA⁻¹ = CFSG.Sporadic.J4.rowsMatrix cAinvRows := by
  rw [cAinvRows, rowsMatrix_pairRows]
  exact (rep_invP rep_cA).2.2.1.symm

theorem Mx_cBinv :
    Mx Coordinator.cB⁻¹ = CFSG.Sporadic.J4.rowsMatrix cBinvRows := by
  rw [cBinvRows, rowsMatrix_pairRows]
  exact (rep_invP rep_cB).2.2.1.symm

theorem Mx_cZinv :
    Mx Coordinator.cZ⁻¹ = CFSG.Sporadic.J4.rowsMatrix cZinvRows := by
  rw [cZinvRows, rowsMatrix_pairRows]
  exact (rep_invP rep_cZ).2.2.1.symm

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
