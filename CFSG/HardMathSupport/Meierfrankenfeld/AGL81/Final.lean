module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFFamily
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.Structure
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.ThreeConstrained
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710XA1

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81

open CFSG.Quasithin CFSG.Quasithin.B2F CFSG.QuasithinUnique CFSG.Open
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

theorem agl81I59 :
    AGL81I59 := by
  intro G _ _ M T V hK hF hT hV hcon hJ
  subst hV
  obtain ⟨hU, -⟩ := B2_15 hF hT
  obtain ⟨-, -, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
  have hMN : M ≤ Subgroup.normalizer
      ((conjClosure (quasithinOmegaOneCenter T) M : Subgroup G) : Set G) := hred.2.1
  have hO2 := fun Q (hQ : Q ≤ autI hU M) hQn hQ2 => eq_bot_of_normal_isPGroup hU hred hQ hQn hQ2
  let f : ↥M →* ↥(autI hU M) :=
    ((convI hU).comp (Subgroup.inclusion hMN)).codRestrict (autI hU M)
      (fun m => convI_mem_autI hU m.2 (hMN m.2))
  have hf : Function.Surjective f := by
    rintro ⟨φ, hφ⟩
    obtain ⟨g, hgM, rfl⟩ := (mem_autI hU).1 hφ
    exact ⟨⟨g, hgM⟩, Subtype.ext rfl⟩
  have hKX : CFSG.Open.IsKGroup ↥(autI hU M) :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710.isKGroup_of_surjective f hf hK
  have hW : ∀ w : IntMod (conjClosure (quasithinOmegaOneCenter T) M) hU, w ^ 2 = 1 :=
    fun w => IntMod.sq_eq_one w
  have hsolvD := isSolvable_closure_transvectionsIn hW hKX hO2 hcon
  have hoff := fun A (hA : IsFFStarOffender (autI hU M) A) =>
    le_closure_transvectionsIn_of_isFFStarOffender hW hKX hO2 hcon hA
  exact ⟨hU, hred, structure_of_not_le_of_le_closure hU hred hsolvD hoff hT hJ⟩

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81
