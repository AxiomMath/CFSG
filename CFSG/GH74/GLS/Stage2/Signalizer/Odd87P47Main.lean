module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47Red
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47SL2
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47PGL
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47CStmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop47
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

theorem prop4_7cS_typeOne (h41b : Prop4_1b) (h43 : Prop4_3Ep)
    (hF : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Stage2Ctx G z k S → E4Facts G z k)
    (hC : P47BranchC) {G : Type} [Group G] [Finite G] {z : G} {k : Kind}
    {S : Subgroup G} (ctx : Stage2Ctx G z k S) {H X : Subgroup G} {p : ℕ}
    (sig : Sig4Sub G z H p X) (hSH : S ≤ H) : X ≤ Op p H := by
  by_contra hnot
  have hz : z ∈ H := sig.A.z_mem
  have hsig := sig4B_of_sub ctx.orderOf_z sig hnot
  have hpp : Fact p.Prime := ⟨sig.A.prime⟩
  have hSz : S ≤ centralizer ({z} : Set G) := ctx.sylow.le
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf 2 S H := ctx.sylow_top.of_le hSH le_top
  have hS'syl := xBar_isSylowOf_top (p := p) hSsyl
  have hS'n := xBar_le_normalizer sig hSz
  have hS'c := xBar_le_centralizer_z (p := p) hz hSz
  have hR : ⁅pCore 2 (Sec H (pCore p ↥H)), xBar p H X⁆ = ⊥ :=
    commutator_eq_bot_of_normal_two (pCore_isPGroup (p := 2) (G := Sec H (pCore p ↥H)))
      sig.A.prime sig.A.odd hsig.A.pgroup ((pCore_two_le_sylow hS'syl).trans hS'n)
  have hL := comm_layer_ne_bot hsig.A.ne_bot (h41b G z k S ctx H (pCore p ↥H) hz p _ hsig) hR
  have hK : (ncl (xBar p H X)).Normal := Subgroup.normalClosure_normal
  have hTop : ∀ N : Subgroup (Sec H (pCore p ↥H)), N.Normal → ⊤ ≤ normalizer (N : Set (Sec H (pCore p ↥H))) :=
    fun N hN => (Subgroup.normalizer_eq_top_iff.mpr hN).ge
  rcases h43 G z k S ctx H (pCore p ↥H) hz p _ hsig hL with hb | ⟨hc, hcp⟩ | hd1 | he
  · exact not_sylow2_le_normalizer_C43b sig.A.prime sig.A.odd hb
      (hS'syl.inf_of_le_normalizer le_top (hTop _ hK)) (inf_le_left.trans hS'n)
  · have hz2 : zSec z H hz (pCore p ↥H) * zSec z H hz (pCore p ↥H) = 1 := by
      have h := orderOf_zSec ctx.orderOf_z hz (pCore p ↥H) hsig.odd
      have h1 := pow_orderOf_eq_one (zSec z H hz (pCore p ↥H))
      rw [h, pow_two] at h1
      exact h1
    have h3 : 3 ≤ CFSG.pRank 2 ↥S := three_le_pRank_S ctx
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h3
    obtain ⟨E, hES, hEab, hEcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 2) S
    have h8 : 8 ≤ Nat.card ↥E := by
      rw [hEcard]
      exact (Nat.pow_le_pow_right (by norm_num) h3 : 2 ^ 3 ≤ _)
    obtain ⟨E', hE'S, hE'ab, hE'card⟩ := exists_elemAbelian_xBar hsig.odd hES hSH hEab
    have := hC G z k S ctx (hF G z k S ctx) (Sec H (pCore p ↥H)) (zSec z H hz (pCore p ↥H))
      (SecOfG.of_sig4B hsig) hz2 p _ hsig.A hsig.op hc hcp (xBar p H S)
      hS'syl.isPGroup hS'c hS'n E' hE'S hE'ab
    omega
  · have hKK : ⁅ncl (xBar p H X), ncl (xBar p H X)⁆.Normal := inferInstance
    exact false_of_C43d1_sylow_normalizes hd1 (hS'syl.inf_of_le_normalizer le_top (hTop _ hKK))
      (inf_le_left.trans hS'n)
  · exact not_sylow2_le_normalizer_C43e he
      (hS'syl.inf_of_le_normalizer le_top (hTop _ hK)) (inf_le_left.trans hS'n)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
