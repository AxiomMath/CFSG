module

public import CFSG.ClassicalInvolution.Sp62Rec.PkgNoHat
import CFSG.ClassicalInvolution.Sp62Rec.SylowCentral
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance CFSG.Open

variable {G : Type} [Group G] [Finite G] {z e : G}
  {E B : Subgroup G}

theorem I1Six.exists_sylow_B (P : I1Six z e E B) (hz2 : z * z = 1) :
    ∃ TB : Sylow 2 ↥B, (⟨z, P.z_mem⟩ : ↥B) ∈ (TB : Subgroup ↥B) ∧
      ∀ x ∈ (TB : Subgroup ↥B), (⟨z, P.z_mem⟩ : ↥B) * x = x * ⟨z, P.z_mem⟩ := by
  obtain ⟨φ, hsurj, hker, -, -, hodd⟩ := P.hat
  have hEB : oddCoreIn E ≤ B := (oddCoreIn_le E).trans P.E_le_B
  have hK : Odd (Nat.card φ.ker) := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEB).toEquiv]
    exact odd_card_oddCoreIn E
  exact exists_sylow_central_of_surjective φ hsurj hK
    (b := (⟨z, P.z_mem⟩ : ↥B)) (Subtype.ext hz2) hodd

end CFSG.ClassicalInvolution.Sp62Rec

set_option linter.unusedSectionVars false

