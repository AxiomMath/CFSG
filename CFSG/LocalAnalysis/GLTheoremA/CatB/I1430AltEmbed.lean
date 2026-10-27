module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430AltModel
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430AltTrans

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.I1430AltEmbed

open Equiv CFSG.LocalAnalysis.GLTheoremA.S8.L84.I1430AltModel

def altEmb (n : ℕ) (hn : 10 ≤ n) : Fin 10 ↪ Fin n := Fin.castLEEmb hn

theorem sign_viaEmbeddingHom (n : ℕ) (hn : 10 ≤ n) (σ : Perm (Fin 10)) :
    Equiv.Perm.sign (Equiv.Perm.viaEmbeddingHom (altEmb n hn) σ) = Equiv.Perm.sign σ := by
  rw [Equiv.Perm.viaEmbeddingHom_apply]
  unfold Equiv.Perm.viaEmbedding
  convert Equiv.Perm.sign_extendDomain σ _

noncomputable def altEmbed (n : ℕ) (hn : 10 ≤ n) : alternatingGroup (Fin 10) →* alternatingGroup (Fin n) :=
  MonoidHom.codRestrict
    ((Equiv.Perm.viaEmbeddingHom (altEmb n hn)).comp (alternatingGroup (Fin 10)).subtype)
    (alternatingGroup (Fin n)) fun x => by
      show Equiv.Perm.sign (Equiv.Perm.viaEmbeddingHom (altEmb n hn) (x : Perm (Fin 10))) = 1
      rw [sign_viaEmbeddingHom]
      exact Equiv.Perm.mem_alternatingGroup.1 x.2

theorem altEmbed_injective (n : ℕ) (hn : 10 ≤ n) : Function.Injective (altEmbed n hn) := by
  intro x y hxy
  apply Subtype.ext
  apply Equiv.Perm.viaEmbeddingHom_injective (altEmb n hn)
  exact congrArg Subtype.val hxy

theorem i1430TwoLocal_alt (n : ℕ) (hn : 10 ≤ n) : I1430TwoLocal (alternatingGroup (Fin n)) 3 :=
  CFSG.LocalAnalysis.GLTheoremA.S8.L84.i1430TwoLocal_of_injective (altEmbed n hn) (altEmbed_injective n hn)
    i1430TwoLocal_altTen

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.I1430AltEmbed
