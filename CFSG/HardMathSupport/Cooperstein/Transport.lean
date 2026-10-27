module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.GroupTheory.PCore.Transport
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Cooperstein.Transport

open CFSG.Open

variable {G G' : Type*} [Group G] [Group G']

theorem comm_of_isElemAbelian {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

theorem card_map_mulEquiv (f : G ≃* G') (A : Subgroup G) :
    Nat.card (A.map f.toMonoidHom) = Nat.card A :=
  (Nat.card_congr (A.equivMapOfInjective f.toMonoidHom f.injective)).symm

theorem pCore_eq_open_local (p : ℕ) (K : Type*) [Group K] :
    CFSG.pCore p K = CFSG.Open.pCore p K := (CFSG.Open.pCore_eq_pCore p K).symm

theorem pCoreOf_map_mulEquiv (p : ℕ) (f : G ≃* G') (H : Subgroup G) :
    pCoreOf p (H.map f.toMonoidHom) = (pCoreOf p H).map f.toMonoidHom := by
  let e : H ≃* ↥(H.map f.toMonoidHom) := H.equivMapOfInjective f.toMonoidHom f.injective
  have hcore : (CFSG.pCore p H).map e.toMonoidHom = CFSG.pCore p ↥(H.map f.toMonoidHom) :=
    CFSG.pCore_map_iso p e
  have hh : (H.map f.toMonoidHom).subtype.comp e.toMonoidHom = f.toMonoidHom.comp H.subtype :=
    MonoidHom.ext fun x => rfl
  unfold pCoreOf
  rw [← hcore, Subgroup.map_map, Subgroup.map_map, hh]

end CFSG.HardMathSupport.Cooperstein.Transport

end
