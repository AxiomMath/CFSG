module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3SF4DatumBits
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicAlphaData

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F4Sym

open CFSG.AGLEmbedding CFSG.AGLEmbedding.R3 CFSG.Assembly CFSG.Blueprint.Chevalley

theorem charP_two_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    CharP K 2 := by
  haveI := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact hK)

section Spec0


@[expose] noncomputable def f4Spec0 (K : Type) [Field K] [CharP K 2] :
    ModuleSpec (adjointGroup .F4 K) 2 where
  n := f4Mod.basis.length
  m := f4Mod.acts.length
  a := f4a K
  g := f4g K
  M := fun j => actMatN 2 f4Mod.basis.length (f4Mod.acts.get j)
  comm := f4a_comm
  pow := f4a_sq
  indep := f4_indep
  act := f4_act

end Spec0

section Spec


@[expose] noncomputable def f4Spec (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    ModuleSpec (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 K false)) 2 :=
  haveI := charP_two_of_card_two hK
  (f4Spec0 K).map (CFSG.StandardType.TableBF4.recipeEquiv K).symm.toMonoidHom
    (CFSG.StandardType.TableBF4.recipeEquiv K).symm.injective

end Spec

end CFSG.LocalAnalysis.GLTheoremA.F4Sym
