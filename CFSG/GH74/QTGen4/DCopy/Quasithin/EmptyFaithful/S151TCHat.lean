module

public import CFSG.Quasithin.EmptyFaithful.S151TCHat
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S151TBMain
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S151TCOrd

public section

namespace CFSG.Quasithin.S151TC

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open CFSG.Quasithin.H13.Orbit CFSG.Quasithin.HatA6 CFSG.Quasithin.S151TB

section Top

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {L T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G}

theorem input15120NoHatA6_holds_F4
    (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G) :
    S151TB.Input15120NoHatA6_F4 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hcomp hHat
  obtain ⟨-, hhat, -, hcent⟩ := hHat
  have hq : CFSG.IsQuasisimple (LStar L) := hc.hL.quasi
  obtain ⟨-, hZ3, ⟨eA⟩⟩ := hhat
  have hD : ListD' L := Or.inr (Or.inl ⟨eA⟩)
  have hN := g1_le_normalizer h37 h38 hc hcomp hD
  have hRN : q1_1516 Mc Z₁ ≤ Subgroup.normalizer (L : Set G) :=
    (q1_1516_le Mc Z₁).trans ((mZ1516_le_g1 Mc Z₁).trans hN)
  have hSN : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G) := (s1516_le_g1 T Z₁).trans hN
  have hcard : Nat.card (LStar L) = 1080 := (quasisimple_card hq.1 hZ3 eA).2
  obtain ⟨-, -, F, _, _, hF4, ρ, e, hequiv, W, hW2, hWM⟩ :=
    c27_c_of_card1080_F4 (hC27 G) hc.h18.five.2.2 hcomp hq hchar hc.hL.not_le hRN hcard
  obtain ⟨w, hwU, hw1, hwfix, hwM⟩ := exists_fixed_vec hc hchar hcomp hSN
  exact hat_contra hq hZ3 eA hcent (sylow_inf hc) hF4 ρ e hequiv W hW2 w hwU hw1 hwfix
    (fun k hk w' hw' => (hWM k).1 (hwM k k.2 hk) w' hw')

end Top

end CFSG.Quasithin.S151TC
