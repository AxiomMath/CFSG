module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalInvolution.Generic.SL2Anticommute
public import CFSG.ClassicalInvolution.ModelFacts.MF15Sq
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Pairs
public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.Timmesfeld.RankTwo.LevisSpin
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.Timmesfeld.RankTwo.LevisBRankOne

public section

namespace CFSG.ClassicalInvolution.PhanD4

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap CFSG.ClassicalInvolution.ModelFacts
open CFSG.Timmesfeld (edgeD)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair Su B12 B23)
open CFSG.LieType.Steinberg
open scoped MatrixGroups commutatorElement

section Basic

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem La_range_inf_of_orth {F F' : Frame Q}
    (h : ∀ X Y, polar Q (F.incl X) (F'.incl Y) = 0) : F.La.range ⊓ F'.La.range = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨A, rfl⟩, ⟨B, hB⟩⟩
  rw [Subgroup.mem_bot]
  have h' : ∀ X Y, polar Q (F'.incl X) (F.incl Y) = 0 := fun X Y => by
    rw [polar_comm]
    exact h Y X
  have hfix : ∀ Y, F.La A (F'.incl Y) = F'.incl Y := fun Y =>
    F.La_apply_of_coords_eq_zero A (Frame.coords_incl_eq_zero_of_orth h' Y)
  have hB1 : B = 1 := by
    apply Subtype.ext
    have := Frame.incl_injective F' ((F'.La_apply_incl B 1).symm.trans ((congrFun (congrArg
      DFunLike.coe hB) (F'.incl 1)).trans (hfix 1)))
    simpa using this
  rw [← hB, hB1, map_one]

end Basic

section Su

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem B12_inf_B23 : B12 K p f ⊓ B23 K p f = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨A, rfl⟩, ⟨A', hA'⟩⟩
  rw [Subgroup.mem_bot]
  have h' := congrArg (fun g : Su K p f 3 => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hA'
  simp only [coe_embSUid] at h'
  have e00 := congrFun (congrFun h' 0) 0
  have e01 := congrFun (congrFun h' 0) 1
  have e10 := congrFun (congrFun h' 1) 0
  simp [embPair] at e00 e01 e10
  have hdet := A.2.1
  rw [Matrix.det_fin_two] at hdet
  have e11 : ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    rw [← e00, ← e01, ← e10] at hdet
    simpa using hdet
  have hA1 : A = 1 := by
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    fin_cases i <;> fin_cases j <;> simp [← e00, ← e01, ← e10, e11]
  rw [hA1, map_one]

end Su

end CFSG.ClassicalInvolution.PhanD4
