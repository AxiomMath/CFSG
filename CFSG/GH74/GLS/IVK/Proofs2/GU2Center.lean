module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U3Frame

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.Q3.TA3

variable {p f : ℕ} {F : Type} [Field F]

theorem scalar_mem_GU2Stated_iff (h : UnitaryFieldData p f F) {c : Fˣ} :
    GeneralLinearGroup.scalar (Fin 2) c ∈ GU2Stated (p ^ f) F ↔ c ∈ rootsOfUnity (p ^ f + 1) F := by
  rw [Lemma41aU3.mem_GU2Stated_iff h, ← h.ker_normUnits, h.mem_ker_normUnits,
    UnitaryFieldData.norm, mul_comm, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  constructor
  · intro hc
    simpa using congrFun (congrFun hc 0) 0
  · intro hc
    simp [hc]

theorem mem_center_GU2Stated_iff (h : UnitaryFieldData p f F) {A : GU2Stated (p ^ f) F} :
    A ∈ center (GU2Stated (p ^ f) F) ↔
      ∃ c ∈ rootsOfUnity (p ^ f + 1) F,
        (A : GL (Fin 2) F) = GeneralLinearGroup.scalar (Fin 2) c := by
  constructor
  · intro hA
    obtain ⟨c, hc⟩ := Q5U3.slCentScalar_GU2 h A fun B _ =>
      congrArg Subtype.val (mem_center_iff.mp hA B).symm
    exact ⟨c, (scalar_mem_GU2Stated_iff h).mp (hc ▸ A.2), hc⟩
  · rintro ⟨c, -, hc⟩
    refine mem_center_iff.mpr fun B => Subtype.ext ?_
    change (B : GL (Fin 2) F) * A = A * B
    rw [hc]
    exact (Q5GL2.scalar_mul_comm c B).symm

theorem natCard_center_GU2Stated (h : UnitaryFieldData p f F) :
    Nat.card (center (GU2Stated (p ^ f) F)) = p ^ f + 1 := by
  let ρ : rootsOfUnity (p ^ f + 1) F → center (GU2Stated (p ^ f) F) := fun ζ =>
    ⟨⟨GeneralLinearGroup.scalar (Fin 2) ζ, (scalar_mem_GU2Stated_iff h).mpr ζ.2⟩,
      (mem_center_GU2Stated_iff h).mpr ⟨ζ, ζ.2, rfl⟩⟩
  have hρ : Function.Bijective ρ := by
    refine ⟨fun a b hab => Subtype.ext (Q5GL2.scalar_injective ?_), fun A => ?_⟩
    · exact congrArg (fun x : center (GU2Stated (p ^ f) F) => ((x : GU2Stated (p ^ f) F) :
        GL (Fin 2) F)) hab
    · obtain ⟨c, hc, hA⟩ := (mem_center_GU2Stated_iff h).mp A.2
      exact ⟨⟨c, hc⟩, Subtype.ext (Subtype.ext hA.symm)⟩
  rw [← Nat.card_congr (Equiv.ofBijective ρ hρ), ← h.ker_normUnits,
    h.card_ker_normUnits_and_surjective.1]

end CFSG.GH74.GLS.IVK.Proofs2
