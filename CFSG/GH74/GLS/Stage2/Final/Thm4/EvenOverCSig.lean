module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.EvenOverCCore
public import CFSG.GH74.GLS.Stage2.Final.Thm4.EvenOverCComp
import CFSG.GH74.GLS.Stage2.Final.L26.GLevel
public import CFSG.GH74.GLS.Stage2.Final.Thm4.EvenOverCTrans
public import CFSG.GH74.GLS.Stage2.Signalizer.L64Sub

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4.EvenOver

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

theorem rigid_false
    {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} (h43 : Prop4_3E)
    (ctx : Stage2Ctx G z k S) (hk : ∃ ε : Bool, k = Kind.l4 ε) (hR : Rigid z M) : False := by
  obtain ⟨t, htS, htc, htz⟩ := L26.exists_conj_ne_of_ctx ctx
  have ht : t ∈ Cen z := ctx.S_le_Cen htS
  have htz' : z ∈ Cen t :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp ht).symm
  have ht2 : orderOf t = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp htc
    have h1 := MulEquiv.orderOf_eq (MulAut.conj g) z
    rw [MulAut.conj_apply, hg] at h1
    rw [h1]
    exact ctx.orderOf_z
  obtain ⟨p, X, hp, hp2, hXt, hXp, hX0, hXinv, hXcomm⟩ := hR.exists_X ht ht2 htz
  have hH : PairData ↥(Cen t) := pairData_Cen_conj ctx hk hR.oddCore htc
  have hproper : Cen t ≠ ⊤ := by
    intro htop
    have hcen : t ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ Cen t := htop ▸ Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_singleton_iff.mp this)
    rcases ctx.std.kps.1.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h0 | h1
    · rw [h0, Subgroup.mem_bot] at hcen
      rw [hcen, orderOf_one] at ht2
      exact absurd ht2 (by norm_num)
    · obtain ⟨a, b, hab⟩ := ctx.std.kps.2.1
      have ha : a ∈ Subgroup.center G := h1 ▸ Subgroup.mem_top a
      exact hab ((Subgroup.mem_center_iff.mp ha b).symm)
  have hsub : Sig4Sub G z (Cen t) p X :=
    ⟨hproper, ⟨hp, hp2, htz', hXt, hXp, hX0, fun c hc hcz => hXinv c hc hcz, hXcomm⟩⟩
  have hE : ⁅Em (Cen t), X⁆ ≠ ⊥ := comm_Em_ne_bot hH hp hp2 hXt hXp hX0
  have hconcl := L64.prop4_3Esub_of h43 ctx hsub hE
  have hsig := sig4B_of_sub ctx.orderOf_z hsub (L64.not_le_Op_of_Em hp hXt hE)
  obtain ⟨ε, rfl⟩ := hk
  exact false_of_concl43E (hH.sec hp hp2) hp hp2 hsig.A.pgroup hsig.A.ne_bot hconcl

end CFSG.GH74.GLS.Stage2.Final.Thm4.EvenOver
