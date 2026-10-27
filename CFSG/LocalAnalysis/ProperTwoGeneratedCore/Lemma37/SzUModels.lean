module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzUCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BenderGroupFactsUnitary

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.BenderFacts

section Suzuki

variable (m : ℕ)

local notation "K" => BinaryGaloisField (2 * m + 1)

theorem suzukiCoverRootElement_sq_eq_one_iff (hm : 0 < m) (a b : K) :
    suzukiCoverRootElement m a b ^ 2 = 1 ↔ a = 0 := by
  rw [suzukiCoverRootElement_sq m hm, ← suzukiCoverRootElement_zero_zero]
  constructor
  · intro h
    rcases mul_eq_zero.mp (suzukiCoverRootElement_injective m _ _ _ _ h).2 with h' | h'
    · exact h'
    · exact (map_eq_zero_iff _ (suzukiCoverTits m).injective).mp h'
  · rintro rfl
    rw [zero_mul]

theorem exists_eq_suzukiCoverRootElement_zero (hm : 0 < m) {x : suzukiCoverRoot m}
    (hx : x ^ 2 = 1) : ∃ b : K, x = suzukiCoverRootElement m 0 b := by
  obtain ⟨a, b, rfl⟩ := suzukiCoverRootElement_surjective m x
  rw [(suzukiCoverRootElement_sq_eq_one_iff m hm a b).mp hx]
  exact ⟨b, rfl⟩

theorem mem_center_suzukiCoverRoot_iff (hm : 0 < m) (x : suzukiCoverRoot m) :
    x ∈ Subgroup.center (suzukiCoverRoot m) ↔ ∃ b : K, x = suzukiCoverRootElement m 0 b := by
  obtain ⟨-, -, hcomm, hcoord⟩ := suzukiCoverRoot_structure m hm
  rw [← hcomm, hcoord]

theorem benderRootData_suzukiCoverRoot (hm : 0 < m) :
    BenderRootData (suzukiCoverRoot m) (2 ^ (2 * m + 1)) (2 ^ (2 * m + 1)) where
  card_sq_one := by
    rw [← GaloisField.card 2 (2 * m + 1) (by omega)]
    refine Nat.card_congr
      { toFun := fun x => ((((x.1 : SuzukiMatrixGroup m) : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K) 0 2)
        invFun := fun b => ⟨suzukiCoverRootElement m 0 b,
          (suzukiCoverRootElement_sq_eq_one_iff m hm 0 b).mpr rfl⟩
        left_inv := fun x => ?_
        right_inv := fun b => ?_ }
    · obtain ⟨b, hb⟩ := exists_eq_suzukiCoverRootElement_zero m hm x.2
      apply Subtype.ext
      simp only
      rw [hb]
      simp [SuzukiRootGL, SuzukiRootMatrix]
    · simp [SuzukiRootGL, SuzukiRootMatrix]
  card_sq _ hr1 hr2 := card_sq_eq_of_mem_suzukiCoverRoot m hm hr1 hr2
  comm x hx y := by
    obtain ⟨b, rfl⟩ := exists_eq_suzukiCoverRootElement_zero m hm hx
    exact (Subgroup.mem_center_iff.mp ((mem_center_suzukiCoverRoot_iff m hm _).mpr ⟨b, rfl⟩)
      y).symm

theorem benderCenterSqOne_suzukiCoverRoot (hm : 0 < m) :
    BenderCenterSqOne (suzukiCoverRoot m) := by
  intro x hx
  obtain ⟨b, rfl⟩ := (mem_center_suzukiCoverRoot_iff m hm x).mp
    (Subgroup.mem_center_iff.mpr fun y => (hx y).symm)
  exact (suzukiCoverRootElement_sq_eq_one_iff m hm 0 b).mpr rfl

theorem benderRootData_of_mulEquiv_suzukiMatrixGroup (hm : 0 < m) {L : Type*} [Group L]
    (e : L ≃* SuzukiMatrixGroup m) (R : Sylow 2 L) :
    BenderRootData (R : Subgroup L) (2 ^ (2 * m + 1)) (2 ^ (2 * m + 1)) ∧
      BenderCenterSqOne (R : Subgroup L) := by
  have : Finite L := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨θ⟩ : Nonempty ((R : Subgroup L) ≃* suzukiCoverRoot m) :=
    nonempty_sylow_mulEquiv_of_mulEquiv e R (suzukiCoverSylow m hm)
  exact ⟨(benderRootData_suzukiCoverRoot m hm).congr θ.symm,
    (benderCenterSqOne_suzukiCoverRoot m hm).congr θ.symm⟩

end Suzuki

section Unitary

open CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism CFSG.BenderSuzuki.External

variable {F : Type*} [Field F] [Finite F] [CharP F 2] (U : HermitianForm 3 F) {q : ℕ}

theorem benderRootData_hermitianUnipotentCoord (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // U.conj x = x} = q) :
    BenderRootData (hermitianUnipotentCoord U) q (q * (q + 1)) where
  card_sq_one := by
    rw [← card_ker_firstCoord U hfixed]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x =>
      (pow_two_eq_one_iff U x).trans (mem_ker_firstCoord U).symm)
  card_sq _ hr1 hr2 := card_sq_eq_coord_of_sq_eq_one U hcard hfixed hr1 hr2
  comm x hx y := mul_comm_of_fst_eq_zero U ((pow_two_eq_one_iff U x).mp hx) y

theorem benderRootData_of_mulEquiv_projectiveSpecialUnitary {f : ℕ} (hf : 2 ≤ f)
    (hcard : Nat.card F = (2 ^ f) ^ 2) (hfixed : Nat.card {x : F // U.conj x = x} = 2 ^ f)
    (hU : U.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {L : Type*} [Group L]
    (e : L ≃* ProjectiveSpecialUnitaryMatrixGroup U) (R : Sylow 2 L) :
    BenderRootData (R : Subgroup L) (2 ^ f) (2 ^ f * (2 ^ f + 1)) := by
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup U) :=
    Finite.of_injective (fun x : ProjectiveSpecialUnitaryMatrixGroup U =>
      (x : Matrix.ProjGenLinGroup (Fin 3) F)) Subtype.coe_injective
  have : Finite L := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨θ⟩ : Nonempty ((R : Subgroup L) ≃* unitaryCoverRoot U hU) :=
    nonempty_sylow_mulEquiv_of_mulEquiv e R (unitaryCoverSylow U f hf hcard hfixed hU)
  exact (benderRootData_hermitianUnipotentCoord U hcard hfixed).congr
    (θ.trans (unitaryCoverRootEquiv U hU).symm).symm

end Unitary

end CFSG.ProperTwoGeneratedCore.Lemma37
