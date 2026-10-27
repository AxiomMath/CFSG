module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeHeart
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltModel

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Cooperstein

noncomputable instance altHeartAddCommGroup (N : ℕ) : AddCommGroup (altHeart N) :=
  { (inferInstance : AddGroup (altHeart N)) with
    add_comm := fun a b => by
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective b
      rw [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_add]
      exact congrArg _ (Subtype.ext (add_comm _ _)) }

noncomputable instance altHeartAltAction (N : ℕ) :
    MulAction (alternatingGroup (Fin N)) (altHeart N) where
  smul σ v := Coordinator.altAct (σ : Perm (Fin N)) v
  one_smul v := Coordinator.altAct_one v
  mul_smul _ _ v := Coordinator.altAct_mul _ _ v

theorem isAltPermSubImage_altHeart (N : ℕ) :
    IsAltPermSubImage (alternatingGroup (Fin N)) (altHeart N) N := by
  classical
  refine ⟨MulEquiv.refl _, {f | f ∈ evenWeight N},
    fun f => if h : f ∈ evenWeight N then (QuotientAddGroup.mk (⟨f, h⟩ : evenWeight N) : altHeart N)
      else 0, ?_, ?_⟩
  · intro w
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective w
    exact ⟨x.1, x.2, by simp [x.2]⟩
  · intro g f hf
    have hg : g • f = ((evenWeightPerm (g : Perm (Fin N)) ⟨f, hf⟩ : evenWeight N) :
        Fin N → ZMod 2) := rfl
    have hmem : g • f ∈ evenWeight N := by rw [hg]; exact (evenWeightPerm _ ⟨f, hf⟩).2
    have hf' : f ∈ evenWeight N := hf
    simp only [hmem, hf', ↓reduceDIte]
    show (QuotientAddGroup.mk ⟨g • f, hmem⟩ : altHeart N) =
      Coordinator.altAct (g : Perm (Fin N)) (QuotientAddGroup.mk ⟨f, hf'⟩)
    rw [Coordinator.altAct_mk]
    congr 1

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle

end
