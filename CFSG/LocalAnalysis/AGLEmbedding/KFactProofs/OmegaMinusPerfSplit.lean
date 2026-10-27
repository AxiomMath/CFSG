module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentPairs

public section

namespace CFSG.AGLEmbedding.OmegaMinusCent

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

@[expose] def AnisoPair.ofRestrict {W : Submodule (ZMod 2) V}
    (P : AnisoPair (Q.restrict W)) : AnisoPair Q where
  a := P.a
  b := P.b
  Q_a := P.Q_a
  Q_b := P.Q_b
  polar_ab := by
    have := P.polar_ab
    rwa [polar_restrict] at this

theorem AnisoPair.Orth.ofRestrict {W : Submodule (ZMod 2) V}
    {P P' : AnisoPair (Q.restrict W)} (h : P.Orth P') : P.ofRestrict.Orth P'.ofRestrict where
  aa := by have := h.aa; rwa [polar_restrict] at this
  ab := by have := h.ab; rwa [polar_restrict] at this
  ba := by have := h.ba; rwa [polar_restrict] at this
  bb := by have := h.bb; rwa [polar_restrict] at this

end CFSG.AGLEmbedding.OmegaMinusCent

namespace CFSG.AGLEmbedding.OmegaMinusPerf

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module CFSG.AGLEmbedding.OmegaMinusCent

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
  {x : V ≃ₗ[ZMod 2] V}

theorem exists_move_pairs [FiniteDimensional (ZMod 2) V] (hQ : (polarBilin Q).Nondegenerate)
    (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hx3 : ∀ v, x (x (x v)) = v) {m : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * m) :
    ∃ PsM : List (AnisoPair Q), PsM.length ≤ m ∧ PsM.Pairwise AnisoPair.Orth ∧
      (∀ P ∈ PsM, P.a ∈ moveSpace x ∧ P.b = x P.a) ∧
      finrank (ZMod 2) (fixSpace x) = 2 * (m - PsM.length) := by
  have hM := polarNondegOn_move hQ hx hx3
  obtain ⟨PsM, hMpw, hMmem, hMdim⟩ := exists_aniso_pairs_move hx hx3 _ (moveSpace x) rfl le_rfl
    (fun w hw => apply_mem_moveSpace hx3 hw) hM
  have hsum := Submodule.finrank_add_eq_of_isCompl (isCompl_fix_move hx3 (x := x))
  exact ⟨PsM, by omega, hMpw, hMmem, by omega⟩

theorem orth_of_split (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hx3 : ∀ v, x (x (x v)) = v) {P P' : AnisoPair Q}
    (hP : P.a ∈ moveSpace x ∧ P.b = x P.a) (hP' : P'.a ∈ fixSpace x ∧ P'.b ∈ fixSpace x) :
    P.Orth P' :=
  AnisoPair.orth_of_mem_move_fix hx hP.1 (hP.2 ▸ apply_mem_moveSpace hx3 hP.1) hP'.1 hP'.2

end CFSG.AGLEmbedding.OmegaMinusPerf
