module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47RStmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47CStmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47SStmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47Rank4
public import CFSG.GH74.GLS.Stage2.Signalizer.Kinds

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

theorem isPGroup_xBar {G : Type} [Group G] {p q : ℕ} {H S : Subgroup G} (hSH : S ≤ H)
    (hS : IsPGroup q ↥S) : IsPGroup q ↥(xBar p H S) :=
  (hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm).map (QuotientGroup.mk' (pCore p ↥H))

theorem prop4_7cS_fourC2 (h41b : Prop4_1b) (h43 : Prop4_3Ep)
    (hF : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Stage2Ctx G z k S → E4Facts G z k)
    (hR : Prop47R) (hSL2 : P47BranchSL2) (hC : P47BranchC) {G : Type} [Group G] [Finite G] {z : G}
    {k : Kind} {S : Subgroup G} (ctx : Stage2Ctx G z k S) (hn : ¬ TypeOneCase G k)
    {H X T : Subgroup G} {p : ℕ} (sig : Sig4Sub G z H p X) (hTHS : T ≤ H ⊓ S)
    (hT : T4CS z k S T) (hTX : T ≤ normalizer (X : Set G)) : X ≤ Op p H := by
  by_contra hnot
  have hz : z ∈ H := sig.A.z_mem
  have hsig := sig4B_of_sub ctx.orderOf_z sig hnot
  have hTH : T ≤ H := hTHS.trans inf_le_left
  have hTS : T ≤ S := hTHS.trans inf_le_right
  have hTz : T ≤ centralizer ({z} : Set G) := hTS.trans ctx.sylow.le
  have hR' := hR G z k S ctx H X T p sig hTHS hT hTX hnot
  have hL := comm_layer_ne_bot hsig.A.ne_bot (h41b G z k S ctx H (pCore p ↥H) hz p _ hsig) hR'
  have hz2 : zSec z H hz (pCore p ↥H) * zSec z H hz (pCore p ↥H) = 1 := by
    have h := orderOf_zSec ctx.orderOf_z hz (pCore p ↥H) hsig.odd
    have h1 := pow_orderOf_eq_one (zSec z H hz (pCore p ↥H))
    rw [h, pow_two] at h1
    exact h1
  obtain ⟨E, hET, hEab, hEcard⟩ := T4CS.exists_elemAbelian_sixteen ctx hn hT
  obtain ⟨E', hE'T, hE'ab, hE'card⟩ := exists_elemAbelian_xBar hsig.odd hET hTH hEab
  have hT2 : IsPGroup 2 ↥(xBar p H T) := isPGroup_xBar hTH (ctx.sylow.isPGroup.to_le hTS)
  have hTc := xBar_le_centralizer_z (p := p) hz hTz
  have hTn := xBar_le_normalizer sig hTz
  have h16 : Nat.card ↥E' = 16 := by rw [hE'card, hEcard]
  rcases h43 G z k S ctx H (pCore p ↥H) hz p _ hsig hL with hb | ⟨hc, hcp⟩ | hd1 | he
  · have := hSL2 G z k S ctx (hF G z k S ctx) (Sec H (pCore p ↥H)) (zSec z H hz (pCore p ↥H))
      (SecOfG.of_sig4B hsig) hz2 p _ hsig.A hsig.op (Or.inl hb) (xBar p H T) hT2 hTc hTn E' hE'T hE'ab
    omega
  · have := hC G z k S ctx (hF G z k S ctx) (Sec H (pCore p ↥H)) (zSec z H hz (pCore p ↥H))
      (SecOfG.of_sig4B hsig) hz2 p _ hsig.A hsig.op hc hcp (xBar p H T) hT2 hTc hTn E' hE'T hE'ab
    omega
  · have hcl := Stage2Ctx.isClassicalKind_of_not_typeOneCase ctx hn
    rcases hd1.1 with h | h <;> subst h <;> rcases hcl with h' | ⟨ε, h'⟩ <;> cases h'
  · have := hSL2 G z k S ctx (hF G z k S ctx) (Sec H (pCore p ↥H)) (zSec z H hz (pCore p ↥H))
      (SecOfG.of_sig4B hsig) hz2 p _ hsig.A hsig.op (Or.inr he) (xBar p H T) hT2 hTc hTn E' hE'T hE'ab
    omega

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
