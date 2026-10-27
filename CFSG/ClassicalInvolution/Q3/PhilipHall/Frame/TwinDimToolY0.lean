module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Pf4Type

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section DimC

variable {n : ℕ}

@[expose] def P23Y5DimC (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → SecNoExit R u →
      ∀ D : OmegaLieU 3 1 (liftFam (TwinDisc.secFam (Om R) u)), ∀ h : D.card = 1,
        ∀ (tag : CFSG.Assembly.LowTwoRank.StatedLieTag) (k d : ℕ) (ε : Bool),
          IsOrthTag d ε tag k → CompIs 3 1 (D.kind ⟨0, by omega⟩) tag k →
            d = 5 ∨ (d = 6 ∧ ε = !piSign 3 1)

theorem p23Y5Type_of_dimC (hd : P23Y5DimC n) (htr : P23Y5Trans n) : P23Y5Type n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno D
  have htr' := htr hcit hP Y R S t K' W u e g hc hno
  have hne := (p23Members n Y R S t K' W u e g hc).2
  have hcard := secDecomp_card_one hcit hP hc.std.perp hc.data.hu2 hc.data.hu1 hne hno htr' D
  obtain ⟨tag, k, d, ε, -, hort, hcis⟩ := u_orthTag hP hc hno (p23Members n) htr' D hcard
  rcases hd hcit hP Y R S t K' W u e g hc hno D hcard tag k d ε hort hcis with rfl | ⟨rfl, rfl⟩
  · have hort5 : IsOrthTag 5 true tag k := by
      rcases hort with ⟨-, h1, h2⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
        first | exact Or.inl ⟨rfl, h1, h2⟩ | omega
    exact Or.inl fun _ => ⟨tag, k, hort5, hcis⟩
  · exact Or.inr fun _ => ⟨tag, k, hort, hcis⟩

end DimC

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
