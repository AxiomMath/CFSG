module

public import CFSG.FeitThompson.Local.AveragingProjectionFixedVectors
import CFSG.FeitThompson.Local.IdempotentTraceResidueRing
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Matrix Module

section Averaging

variable {R S : Type*} [CommRing R] [CommRing S] {B : Type*} [Group B] [Fintype B]
  {n : Type*} [Fintype n] [DecidableEq n] [Invertible (Fintype.card B : R)]

theorem averagingMatrix_eq_smul_sum (ρ : B →* GL n R) :
    averagingMatrix ρ = ⅟(Fintype.card B : R) • ∑ b : B, (ρ b : Matrix n n R) := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_apply', Matrix.toLin'_apply']
  refine LinearMap.ext fun v => ?_
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, averagingMatrix_mulVec, smul_mulVec,
    sum_mulVec]

theorem trace_averagingMatrix (ρ : B →* GL n R) :
    (averagingMatrix ρ).trace = ⅟(Fintype.card B : R) * ∑ b : B, (ρ b : Matrix n n R).trace := by
  rw [averagingMatrix_eq_smul_sum, Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul]

theorem card_mul_trace_averagingMatrix (ρ : B →* GL n R) :
    (Fintype.card B : R) * (averagingMatrix ρ).trace = ∑ b : B, (ρ b : Matrix n n R).trace := by
  rw [trace_averagingMatrix, ← mul_assoc, mul_invOf_self, one_mul]

theorem rank_averagingMatrix (ρ : B →* GL n R) :
    (averagingMatrix ρ).rank = finrank R (glRepresentation ρ).invariants := by
  rw [← range_mulVecLin_averagingMatrix ρ]
  rfl

theorem map_averagingMatrix [Invertible (Fintype.card B : S)] (f : R →+* S) (ρ : B →* GL n R) :
    (averagingMatrix ρ).map f = averagingMatrix ((Matrix.GeneralLinearGroup.map f).comp ρ) := by
  have hinv : f (⅟(Fintype.card B : R)) = ⅟(Fintype.card B : S) := by
    refine (invOf_eq_right_inv (a := (Fintype.card B : S)) ?_).symm
    rw [← map_natCast f (Fintype.card B), ← map_mul, mul_invOf_self, map_one]
  ext i j
  rw [Matrix.map_apply, averagingMatrix_eq_smul_sum, averagingMatrix_eq_smul_sum]
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, map_mul, map_sum, hinv,
    MonoidHom.coe_comp, Function.comp_apply, Matrix.GeneralLinearGroup.map_apply]

end Averaging

section FixedSpace

variable {R : Type*} [CommRing R] {A : Type*} [Group A] {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def glFixedSpace (ρ : A →* GL n R) (B : Subgroup A) : Submodule R (n → R) :=
  (glRepresentation (ρ.comp B.subtype)).invariants

theorem glFixedSpace_eq_invariants (ρ : A →* GL n R) (B : Subgroup A) :
    glFixedSpace ρ B = (glRepresentation (ρ.comp B.subtype)).invariants := (rfl)

@[simp]
theorem mem_glFixedSpace {ρ : A →* GL n R} {B : Subgroup A} {v : n → R} :
    v ∈ glFixedSpace ρ B ↔ ∀ b ∈ B, (ρ b : Matrix n n R) *ᵥ v = v := by
  rw [glFixedSpace_eq_invariants, mem_invariants_glRepresentation]
  exact ⟨fun h b hb => h ⟨b, hb⟩, fun h b => h b b.2⟩

theorem coe_glFixedSpace (ρ : A →* GL n R) (B : Subgroup A) :
    (glFixedSpace ρ B : Set (n → R)) = {v | ∀ b ∈ B, (ρ b : Matrix n n R) *ᵥ v = v} := by
  ext v
  exact mem_glFixedSpace

@[simp]
theorem glFixedSpace_bot (ρ : A →* GL n R) : glFixedSpace ρ ⊥ = ⊤ := by
  ext v
  simp +contextual

theorem glFixedSpace_antitone (ρ : A →* GL n R) : Antitone (glFixedSpace ρ) := by
  intro B C hBC v hv
  rw [mem_glFixedSpace] at hv ⊢
  exact fun b hb => hv b (hBC hb)

end FixedSpace

section Main

variable {p e d : ℕ} {A : Type*} [Group A]

theorem generalLinearGroup_map_comp_eq_of_entry (he : e ≠ 0)
    {ρ : A →* GL (Fin d) (ZMod p)} {ρe : A →* GL (Fin d) (ZMod (p ^ e))}
    (h : ∀ (a : A) (i j : Fin d), ZMod.castHom (dvd_pow_self p he) (ZMod p)
      ((ρe a : Matrix (Fin d) (Fin d) (ZMod (p ^ e))) i j) = (ρ a : Matrix _ _ _) i j) :
    (Matrix.GeneralLinearGroup.map (ZMod.castHom (dvd_pow_self p he) (ZMod p))).comp ρe = ρ := by
  ext a i j
  simpa [Matrix.GeneralLinearGroup.map_apply] using h a i j

theorem sum_trace_eq_natCard_mul_finrank_glFixedSpace
    (hp : p.Prime) (he : e ≠ 0) (hA : ¬ p ∣ Nat.card A)
    (ρ : A →* GL (Fin d) (ZMod p)) (ρe : A →* GL (Fin d) (ZMod (p ^ e)))
    (hρ : (Matrix.GeneralLinearGroup.map (ZMod.castHom (dvd_pow_self p he) (ZMod p))).comp ρe = ρ)
    (B : Subgroup A) [Fintype B] :
    ∑ b : B, (ρe (b : A) : Matrix (Fin d) (Fin d) (ZMod (p ^ e))).trace
      = (Nat.card B : ZMod (p ^ e)) * (finrank (ZMod p) (glFixedSpace ρ B) : ZMod (p ^ e)) := by
  have hcardB : ¬ p ∣ Nat.card B := fun h => hA (h.trans B.card_subgroup_dvd_card)
  have hcop : (Nat.card B).Coprime p :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hcardB)
  have hcard : Nat.card B = Fintype.card B := Nat.card_eq_fintype_card
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  have : Invertible ((Fintype.card B : ZMod (p ^ e))) := by
    refine ((ZMod.isUnit_iff_coprime _ _).2 ?_).invertible
    rw [← hcard]
    exact hcop.pow_right e
  have : Invertible ((Fintype.card B : ZMod p)) := by
    refine ((ZMod.isUnit_iff_coprime _ _).2 ?_).invertible
    rw [← hcard]
    exact hcop
  set σ : B →* GL (Fin d) (ZMod (p ^ e)) := ρe.comp B.subtype with hσ
  have hcomp : (Matrix.GeneralLinearGroup.map
      (ZMod.castHom (dvd_pow_self p he) (ZMod p))).comp σ = ρ.comp B.subtype := by
    rw [hσ, ← MonoidHom.comp_assoc, hρ]
  have hrank : finrank (ZMod p) (glFixedSpace ρ B)
      = ((ZMod.castHom (dvd_pow_self p he) (ZMod p)).mapMatrix (averagingMatrix σ)).rank := by
    rw [RingHom.mapMatrix_apply, map_averagingMatrix, hcomp, rank_averagingMatrix,
      glFixedSpace_eq_invariants]
  have htr := trace_eq_rank_map_of_isIdempotentElem_zmod hp he
    (T := averagingMatrix σ) (averagingMatrix_mul_self σ) hrank
  have key : (Fintype.card B : ZMod (p ^ e)) * (averagingMatrix σ).trace
      = ∑ b : B, (ρe (b : A) : Matrix (Fin d) (Fin d) (ZMod (p ^ e))).trace :=
    card_mul_trace_averagingMatrix σ
  rw [← key, htr, hcard]

end Main

end CFSG.FeitThompson
