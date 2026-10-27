module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5Defs
public import CFSG.LocalAnalysis.EvenBN.GMSK.FixedRootDatum
public import Certificates.Data.A5

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.EvenBN.GMSK

theorem alt5_pow_four : ∀ g : Equiv.Perm (Fin 5), g ∈ alternatingGroup (Fin 5) →
    g ^ 4 = 1 → g ^ 2 = 1 := by
  decide +kernel

theorem z2a5_no_four (g : Multiplicative (ZMod 2) × ↥(alternatingGroup (Fin 5))) :
    orderOf g ≠ 4 := by
  intro h
  have h4 : g ^ 4 = 1 := by rw [← h]; exact pow_orderOf_eq_one g
  have hb : g.2 ^ 2 = 1 := Subtype.ext (by
    simpa using alt5_pow_four g.2 g.2.2
      (by simpa using congrArg (fun x => (x.2 : Equiv.Perm (Fin 5))) h4))
  have ha : g.1 ^ 2 = 1 := by
    have : ∀ a : Multiplicative (ZMod 2), a ^ 2 = 1 := by decide
    exact this _
  have h2 : g ^ 2 = 1 := Prod.ext ha hb
  have := orderOf_le_of_pow_eq_one (by norm_num) h2
  omega

theorem z2a5_eqLocus_no_four {Y : Type} [Group Y] {τ : Y} (h : Z2A5Hyp Y τ) {S : Subgroup Y}
    [S.Normal] (x : S)
    (hx : x ∈ (MulAut.conjNormal τ : MulAut S).toMonoidHom.eqLocus (MonoidHom.id S)) :
    orderOf x ≠ 4 := by
  intro h4
  obtain ⟨e⟩ := h.2.1
  have hc := mem_centralizer_of_mem_eqLocus hx
  have : orderOf (e ⟨(x : Y), hc⟩) = 4 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, Subgroup.orderOf_coe, h4]
  exact z2a5_no_four _ this

end CFSG.OddStandard.SmallF3.Omega
