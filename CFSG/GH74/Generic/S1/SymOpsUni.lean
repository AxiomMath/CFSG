module

public import CFSG.GH74.Generic.S1.SymCore
public import CFSG.GH74.Generic.S1.SymDiagUni

public section

namespace CFSG.GH74.Generic.S1

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.LieType.Universal.Unitary

variable {F : Type} [Field F]

def uniOps [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1) :
    ModelOps F (StatedSU 4 q F) where
  norm := fun P => (((P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map (fun x : F => x ^ q))ᵀ *
    ((P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1
  norm_conj := fun P hP => by
    obtain ⟨p, f, h, rfl, hp2⟩ := FrameUni.exists_unitaryFieldData hF hq
    have hP' : conjTr (FrameUni.frameBar h) ((P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        ((P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := hP
    refine ⟨fun k hk => FrameUni.unitary_conj_mem h hP' hk, fun k hk => ?_⟩
    have hPinv : ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        conjTr (FrameUni.frameBar h) ((P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) :=
      Units.inv_eq_of_mul_eq_one_left hP'
    have hP'' : conjTr (FrameUni.frameBar h) ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
      rw [hPinv, FrameUni.conjTr_conjTr]
      exact mul_eq_one_comm.1 hP'
    have := FrameUni.unitary_conj_mem h hP'' hk
    rwa [inv_inv] at this
  std := fun ρ => (((ρ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map (fun x : F => x ^ q))ᵀ *
    ((ρ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1
  to_std := fun ρ hρ hdet hnorm => FrameUni.exists_refl_unitary hF hq hρ hdet hnorm
  commutant := fun M hM => by
    obtain ⟨p, f, h, rfl, hp2⟩ := FrameUni.exists_unitaryFieldData hF hq
    exact FrameUni.eq_scalar_of_commute h hp2 (fun A hA => congrArg Units.val (hM A hA))
  diag := fun ρ hρ2 hdet hstd hcomm hne => by
    obtain ⟨P, ε, hε, hP, h⟩ := exists_diag_frame_uni hF hq ρ hρ2 hdet hstd hcomm hne
    exact ⟨P, ε, hP, hε, h⟩

end CFSG.GH74.Generic.S1
