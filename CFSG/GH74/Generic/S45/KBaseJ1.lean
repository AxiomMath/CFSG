module

public import CFSG.GH74.Generic.S45.KBaseGen
public import CFSG.Walter.J1Props.Aut
public import CFSG.Walter.Models

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.Blueprint

theorem kBase_walterJ1 : KBase ↥CFSG.Open.walterJ1 := by
  let h := CFSG.Walter.J1Props.jankoHyp
  refine kBase_of_data h.isSimpleGroup ?_ h.t h.orderOf_t (fun x hx => h.exists_conj_eq_t hx) ?_
  · intro α _
    obtain ⟨g, hg⟩ := CFSG.Walter.J1Props.J3_aut α
    exact ⟨g, hg.symm⟩
  · intro S htS
    exact ⟨h.card_sylow S htS, fun x hx => h.mul_self_of_mem_sylow S htS hx,
      h.centralizer_sylow S htS, h.card_normalizer_sylow S htS⟩

theorem kBase_of_isSporadic_J1 {K : Type} [Group K] [Finite K]
    (h : NativeSporadic.IsSporadic K .J1) : KBase K := by
  obtain ⟨e⟩ := h
  exact KBase.of_mulEquiv (CFSG.Walter.walterJ1EquivNative.trans e.symm) kBase_walterJ1

end CFSG.GH74.Generic.S45
