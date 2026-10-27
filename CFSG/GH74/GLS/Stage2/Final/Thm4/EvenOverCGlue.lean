module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.EvenOverCSig
public import CFSG.GH74.GLS.Stage2.Final.Named
import CFSG.GH74.GLS.Stage2.Final.Thm6.DerOddCore
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Core

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4.EvenOver

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

theorem oddCore_eq_bot_of_even_member (h34 : Leaf_Prop34) (h20 : OddCoreOverC) {G : Type} [Group G]
    [Finite G] {z : G} {k : Kind} {S : Subgroup G} (ctx : Stage2Ctx G z k S) {N : Subgroup G}
    (hN : N ∈ maximalOverCentralizer z) (hNC : N ≠ Cen z)
    (hev : Even (Nat.card ↥(generalizedFitting ↥N))) : pPrimeCoreOf 2 (Cen z) = ⊥ := by
  have h : Ctx17 G z k S N := ⟨ctx, hN, hev⟩
  rcases h34 G z k S ctx N h.cen_le h.ne_top with hc | hd |
    ⟨ε, q, L₁, L₂, hk, hL4, -, hq3, hF, hcoat, -, -, -, hFm⟩
  · exact absurd (h.eq_of_oddCover hc) hNC
  · exact absurd hd (not_isDihedral_S ctx)
  · have hz : z ^ 2 = 1 := by
      rw [← ctx.orderOf_z]
      exact pow_orderOf_eq_one z
    have h1 : OddCore z ≤ pPrimeCoreOf 2 N :=
      Thm6.oddCore_le_pPrimeCoreOf_of_fitting h.cen_le hz hFm
    have h2 : pPrimeCoreOf 2 N = ⊥ := by
      by_contra hne
      exact hNC (h20 G z k S ctx N hN hev hne)
    exact le_bot_iff.mp (h2 ▸ h1)

theorem evenOverC_proved
    (h34 : Leaf_Prop34) (h20 : OddCoreOverC) (hex : ExistsEvenFStar) (h43 : Prop4_3E) :
    EvenOverC := by
  intro G _ _ z k S ctx hk M hM hlt
  by_contra hne
  have hodd : Odd (Nat.card ↥(generalizedFitting ↥M)) := Nat.not_even_iff_odd.mp hne
  by_cases hO : pPrimeCoreOf 2 (Cen z) = ⊥
  · exact rigid_false h43 ctx hk ⟨ctx.orderOf_z, hM.1, hM.2, hodd, hO⟩
  · obtain ⟨N, hN, hNev⟩ := hex G z k S ctx
    have hNC : N ≠ Cen z := by
      intro h
      subst h
      exact hM.1.1 (hN.1.2 M hlt)
    exact hO (oddCore_eq_bot_of_even_member h34 h20 ctx hN hNC hNev)

end CFSG.GH74.GLS.Stage2.Final.Thm4.EvenOver
