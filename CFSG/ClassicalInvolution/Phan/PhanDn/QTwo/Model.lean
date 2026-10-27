module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.AmalgamFamily
public import CFSG.LieType.CurtisTits.AmalgamStrip
public import CFSG.LieType.CurtisTits.AmalgamTransport

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.LieType.BorelTits CFSG.LieType.CurtisTits CFSG.LieType.Steinberg

structure QTwoModelD (K : Type) [Field K] [Finite K] [CharP K 2] (m : ℕ) (X : Type)
    [Group X] where
  S : QTwoPhanFamily K (CFSG.StandardType.ggCoxeterMatrixD m) X
  faithful : S.Faithful
  P : Set (Fin m) → Subgroup X
  T : Fin m → Subgroup X
  completion : IsUniversalCompletion.{0, 0, 0}
    (fun C : ↥(qTwoShape (CFSG.StandardType.ggCoxeterMatrixD m)) => P C.1)
  strip : StripData (qTwoShape (CFSG.StandardType.ggCoxeterMatrixD m)) P S.levi T

namespace QTwoModelD

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {m : ℕ} {X : Type} [Group X]

theorem isUniversal (hK : Nat.card K = 4) (hm : 4 ≤ m) (d : QTwoModelD K m X) :
    d.S.IsUniversal ∧ d.S.Generates := by
  have hU : IsUniversalCompletion.{0, 0, 0}
      (fun C : ↥(qTwoShape (CFSG.StandardType.ggCoxeterMatrixD m)) => d.S.levi C.1) :=
    d.strip.isUniversalCompletion d.completion
  have huniv : d.S.IsUniversal :=
    QTwoPhanFamily.isUniversal_of_isUniversalCompletion hK hm
      (fun i j h => ggCoxeterMatrixD_two_or_three i j h)
      (fun i j k => ggCoxeterMatrixD_not_triangle hm i j k) d.faithful hU
  refine ⟨huniv, ?_⟩
  change (⨆ (i) (j) (_ : CFSG.StandardType.ggCoxeterMatrixD m i j = 3),
    (d.S.θ i j).range) = ⊤
  rw [eq_top_iff, ← iSup_eq_top_of_isUniversalCompletion hU]
  refine iSup_le fun C => ?_
  rw [QTwoPhanFamily.levi]
  refine sup_le ?_ ?_
  · refine iSup_le fun i => iSup_le fun _ => ?_
    obtain ⟨j, h3⟩ := ggCoxeterMatrixD_exists_three hm i
    refine le_trans ?_ (le_iSup_of_le i (le_iSup_of_le j (le_iSup_of_le h3 le_rfl)))
    rw [← d.S.left i j h3]
    rintro x ⟨a, rfl⟩
    exact ⟨embSUid (unitaryInvolution K 2 1) 2 a, rfl⟩
  · refine iSup_le fun i => iSup_le fun _ => iSup_le fun j => iSup_le fun _ =>
      iSup_le fun h3 => ?_
    exact le_iSup_of_le i (le_iSup_of_le j (le_iSup_of_le h3 le_rfl))

end QTwoModelD

end CFSG.ClassicalInvolution.PhanDn.QTwo
