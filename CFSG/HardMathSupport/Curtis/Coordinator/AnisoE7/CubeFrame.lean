module

public import CFSG.LieType.SeitzGeneration.ExcTorusE7Six
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.KE.E7ThreeFrame

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration

section Cube


theorem exists_cube_in_frame {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (F : E7ThreeFrame K L ℓ f p (-1)) (hp : p.Prime)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 6) :
    ∃ (c : adjointGroup .E7 K) (E : Subgroup (adjointGroup .E7 K)),
      IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      ∀ x ∈ E, F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0 ∈
        twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
  obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_E7_six K hp hord
  have hEp : IsPGroup p E := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hE.2 x x.2⟩
  obtain ⟨c, hc⟩ := F.hconj E hEp
  exact ⟨c, E, hE, hEc, hc⟩

end Cube

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
