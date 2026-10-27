module

public import CFSG.ClassicalInvolution.Q3.Q3T6AutConj
public import CFSG.ClassicalInvolution.AschTight.S19KUni
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

section Aut

variable {F : Type} [Field F] [Finite F]

theorem Fa.nonempty_ringEquiv_zmod_three (hF : Nat.card F = 3) : Nonempty (F ≃+* ZMod 3) := by
  have := Fintype.ofFinite F
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ⟨FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, hF, ZMod.card])⟩

omit [Finite F] in
private theorem sl2_aut_eq_conj_of_ringEquiv (ρ : F ≃+* ZMod 3) (α : MulAut SL(2, F)) :
    ∃ G : GL (Fin 2) F, ∀ b : SL(2, F), α b = conjSL G b := by
  let e : SL(2, F) ≃* SL(2, ZMod 3) := S19K.slMap2 ρ
  have hcoe : ∀ c : SL(2, F), ((e c : SL(2, ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      (c : Matrix (Fin 2) (Fin 2) F).map ρ := fun c => by
    change ((Matrix.SpecialLinearGroup.map (ρ : F →+* ZMod 3) c : SL(2, ZMod 3)) :
      Matrix (Fin 2) (Fin 2) (ZMod 3)) = _
    rw [Matrix.SpecialLinearGroup.map_apply_coe]
    rfl
  obtain ⟨g, hg⟩ := sl2Three_aut_eq_conj (((e.symm.trans α).trans e) : MulAut SL(2, ZMod 3))
  refine ⟨Matrix.GeneralLinearGroup.map (ρ.symm : ZMod 3 →+* F) g, fun b => ?_⟩
  have h1 := hg (e b)
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
  rw [hcoe, hcoe] at h1
  apply Subtype.ext
  have h3 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod 3) => M.map ρ.symm) h1
  have hmm : ∀ M : Matrix (Fin 2) (Fin 2) F, (M.map ρ).map ρ.symm = M := fun M => by
    ext i j
    simp
  simp only [Matrix.map_mul, hmm] at h3
  rw [coe_conjSL]
  have e1 : ((Matrix.GeneralLinearGroup.map (ρ.symm : ZMod 3 →+* F) g : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = (g : Matrix (Fin 2) (Fin 2) (ZMod 3)).map ρ.symm := rfl
  have e2 : (((Matrix.GeneralLinearGroup.map (ρ.symm : ZMod 3 →+* F) g)⁻¹ : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = ((g⁻¹ : GL (Fin 2) (ZMod 3)) :
        Matrix (Fin 2) (Fin 2) (ZMod 3)).map ρ.symm := by
    rw [← map_inv]
    rfl
  rw [e1, e2, ← h3]

theorem Fa.sl2_aut_eq_conj_of_card_three (hF : Nat.card F = 3) (α : MulAut SL(2, F)) :
    ∃ G : GL (Fin 2) F, ∀ b : SL(2, F), α b = conjSL G b := by
  obtain ⟨ρ⟩ := Fa.nonempty_ringEquiv_zmod_three hF
  exact sl2_aut_eq_conj_of_ringEquiv ρ α

omit [Finite F] in
theorem semilinHom_refl_eq_conjSL (G : GL (Fin 2) F) (b : SL(2, F)) :
    AscL62.semilinHom G (RingEquiv.refl F) b = conjSL G b :=
  Subtype.ext (by rw [AscL62.coe_semilinHom, coe_conjSL]; rfl)

theorem exists_eq_semilinHom_three (hF : Nat.card F = 3) (α : MulAut SL(2, F)) :
    ∃ G : GL (Fin 2) F, ∀ b, α b = AscL62.semilinHom G (RingEquiv.refl F) b := by
  obtain ⟨G, hG⟩ := Fa.sl2_aut_eq_conj_of_card_three hF α
  exact ⟨G, fun b => (hG b).trans (semilinHom_refl_eq_conjSL G b).symm⟩

end Aut

end CFSG.ClassicalInvolution.Q3.Q3T6
