module

public import CFSG.ClassicalInvolution.Q3.Sec13End16K

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin hiding centMembers

variable {G : Type} [Group G] [Finite G]

namespace Sit16

variable {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z u e g : G}

theorem natCard_zGroup_eq_sixtyFour (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) : Nat.card (zGroup Ω) = 64 :=
  (natCard_zGroup_eq_sixtyFour_of_frame c h h9 h13).1

theorem exists_points (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) :
    ∃ pt : Fin 7 → G, Function.Injective pt ∧ (∀ i, pt i ∈ zGroup Ω) ∧ pt 0 = e ∧
      (∀ i, ∃ x : G, pt i = x * e * x⁻¹) ∧ (List.ofFn pt).prod = 1 ∧
      Subgroup.closure (Set.range pt) = zGroup Ω ∧ ∀ x : G, ∀ i, ∃ j, x * pt i * x⁻¹ = pt j := by
  obtain ⟨pt, σ, hinj, hD, h0, hconj, hprod, hspan, hperm, -, -, -⟩ :=
    exists_points_sigma c h h9 h13
  exact ⟨pt, hinj, hD, h0, hconj, hprod, hspan, fun x i => ⟨σ x i, hperm x i⟩⟩

theorem natCard_eq (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω)
    (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) : Nat.card G = 161280 :=
  natCard_eq_of_frame c h h9 h13

end Sit16

end CFSG.ClassicalInvolution.Q3.Sec13
