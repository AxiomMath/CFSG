module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Ord
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvRee
public import CFSG.Walter.J1Props.Factor
public import CFSG.Walter.Models
public import CFSG.Walter.AStar.Basic

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG

theorem Ivk714Hyp.false_of_abelian_sylow {K : Type} [Group K] [Finite K] {z : MulAut K}
    (h : Ivk714Hyp K z) (hab : CFSG.Walter.HasAbelianSylowTwo K) : False := by
  obtain ⟨H, hH2, x, hx, y, hy, hxy⟩ := h.exists_nonabelian_two_subgroup
  obtain ⟨P, hP⟩ := hH2.exists_le_sylow
  apply hxy
  have hc := (hab P).is_comm.comm
  exact congrArg Subtype.val (hc ⟨x, hP hx⟩ ⟨y, hP hy⟩)

end CFSG.GH74.GLS.IVK

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.Blueprint CFSG.LieType.Ree CFSG.GH74.GLS.IVK

theorem ivk714_j1 :
    Ivk714Empty (fun X _ => NativeSporadic.IsSporadic X .J1) := by
  intro K _ _ _ hK z hz h
  obtain ⟨e0⟩ := hK
  let e : K ≃* CFSG.Open.walterJ1 := e0.trans CFSG.Walter.walterJ1EquivNative.symm
  exact h.false_of_abelian_sylow
    (CFSG.Walter.HasAbelianSylowTwo.of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
      CFSG.Walter.J1Props.hasAbelianSylowTwo)

theorem ivk714_ree :
    ∀ f : ℕ, Ivk714Empty (fun X _ => LieModel X .twistedG2 0 3 f) := by
  intro f K _ _ _ hK z hz h
  have hR : ReeTitsModel K .twistedG2 3 f := by
    rcases hK with ⟨hh, -⟩ | ⟨-, hh, -⟩ | ⟨-, -, hR⟩ | ⟨-, hh, -⟩
    · exact absurd hh (by decide)
    · exact absurd hh (by decide)
    · exact hR
    · exact absurd hh (by decide)
  obtain ⟨a, K', _, _, _, hK', ⟨e⟩⟩ := GHInv.ree_model_data hR
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (CFSG.LieType.Chevalley.coxeterSystem ReeTag.G2.tag).length
  exact h.false_of_abelian_sylow
    (CFSG.Walter.HasAbelianSylowTwo.of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
      (CFSG.Walter.Ree.Model.hasAbelianSylowTwo_reeGamma hK' hw₀))

end CFSG.GH74.GLS.IVK.Proofs2
