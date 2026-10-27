module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentSplit
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentPlanes
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentRotation

public section

namespace CFSG.AGLEmbedding.OmegaMinusCent

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
  {x : V ≃ₗ[ZMod 2] V}

theorem AnisoPair.orth_of_mem_move_fix (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {P P' : AnisoPair Q} (ha : P.a ∈ moveSpace x) (hb : P.b ∈ moveSpace x)
    (ha' : P'.a ∈ fixSpace x) (hb' : P'.b ∈ fixSpace x) : P.Orth P' where
  aa := by rw [polar_comm]; exact polar_fix_move hx ha' ha
  ab := by rw [polar_comm]; exact polar_fix_move hx hb' ha
  ba := by rw [polar_comm]; exact polar_fix_move hx ha' hb
  bb := by rw [polar_comm]; exact polar_fix_move hx hb' hb

theorem exists_pairs_commuting [FiniteDimensional (ZMod 2) V] (hQ : (polarBilin Q).Nondegenerate)
    (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hx3 : ∀ v, x (x (x v)) = v) {m : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * m) :
    ∃ Ps : List (AnisoPair Q), Ps.Pairwise AnisoPair.Orth ∧
      (∀ P ∈ Ps, x * P.rot = P.rot * x) ∧
      (Ps.length = m ∨ (Ps.length + 1 = m ∧ ∃ e : V, e ≠ 0 ∧ Q e = 0 ∧
        ∀ P ∈ Ps, polar Q P.a e = 0 ∧ polar Q P.b e = 0)) := by
  have hC := polarNondegOn_fix hQ hx hx3
  have hM := polarNondegOn_move hQ hx hx3
  obtain ⟨PsM, hMpw, hMmem, hMdim⟩ := exists_aniso_pairs_move hx hx3 _ (moveSpace x) rfl le_rfl
    (fun w hw => apply_mem_moveSpace hx3 hw) hM
  have hsum := Submodule.finrank_add_eq_of_isCompl (isCompl_fix_move hx3 (x := x))
  have hkm : PsM.length ≤ m := by omega
  have hCdim : finrank (ZMod 2) (fixSpace x) = 2 * (m - PsM.length) := by omega
  obtain ⟨PsC, hCpw, hCmem, hCcases⟩ := exists_aniso_pairs_nondeg (m - PsM.length) (fixSpace x)
    hCdim hC
  have hMb : ∀ P ∈ PsM, P.b ∈ moveSpace x := fun P hP => by
    rw [(hMmem P hP).2]
    exact apply_mem_moveSpace hx3 (hMmem P hP).1
  have hMcomm : ∀ P ∈ PsM, x * P.rot = P.rot * x := fun P hP => by
    have hmem := mem_moveSpace.1 (hMmem P hP).1
    have h1 : x P.a = P.b := ((hMmem P hP).2).symm
    have h2 : x P.b = P.a + P.b := by
      rw [(hMmem P hP).2]
      refine eq_of_add_eq_zero' ?_
      calc x (x P.a) + (P.a + x P.a) = x (x P.a) + x P.a + P.a := by abel
        _ = 0 := hmem
    exact P.rot_comm_of_cyc hx h1 h2
  have hCcomm : ∀ P ∈ PsC, x * P.rot = P.rot * x := fun P hP =>
    P.rot_comm_of_fix hx (mem_fixSpace.1 (hCmem P hP).1) (mem_fixSpace.1 (hCmem P hP).2)
  have hpw : (PsM ++ PsC).Pairwise AnisoPair.Orth := by
    rw [List.pairwise_append]
    exact ⟨hMpw, hCpw, fun P hP P' hP' => AnisoPair.orth_of_mem_move_fix hx (hMmem P hP).1
      (hMb P hP) (hCmem P' hP').1 (hCmem P' hP').2⟩
  refine ⟨PsM ++ PsC, hpw, ?_, ?_⟩
  · intro P hP
    rcases List.mem_append.1 hP with hP | hP
    · exact hMcomm P hP
    · exact hCcomm P hP
  · rw [List.length_append]
    rcases hCcases with h | ⟨h, e, heC, he0, heQ, heP⟩
    · left
      omega
    · right
      refine ⟨by omega, e, he0, heQ, fun P hP => ?_⟩
      rcases List.mem_append.1 hP with hP | hP
      · exact ⟨by rw [polar_comm]; exact polar_fix_move hx heC (hMmem P hP).1,
          by rw [polar_comm]; exact polar_fix_move hx heC (hMb P hP)⟩
      · exact heP P hP

end CFSG.AGLEmbedding.OmegaMinusCent
