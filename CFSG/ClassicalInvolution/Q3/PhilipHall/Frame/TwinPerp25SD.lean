module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25Pf2C
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25Pf3A
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5Stmt

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S

open CFSG.ClassicalInvolution.Asc77.C25W (InFour)
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Q8P.Asc77.P25R
  CFSG.ClassicalInvolution.Q8P.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank

@[expose] def P25_NoMixed : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G)
    (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) (a : G), FourData hyp a → BadElt z a → BadElt z (a * z)

theorem no_mixed_of_sqz (hSq : P25_SqZ) : P25_NoMixed := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a hFD hbad hgood
  exact no_mixed hSq hFD hbad hgood

theorem c25_9P_of_a4_nomixed (hA4 : P25_A4) (hNM : P25_NoMixed) : C25_9P := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hz1 : z ≠ 1 := hyp.std.setting.hz.ne_one
  have hzA := (z_facts hyp).1
  have h4 := hA4 G Ω K K' W S R R' z t u₁ u₂ hyp
  by_cases hA : (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
      Subgroup.zpowers z
  · have hz2' : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
    have hcard : Nat.card ↥((S : Subgroup G) ⊓
        Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) = 2 := by
      rw [hA, Nat.card_zpowers, hz2']
    exact ⟨by omega, fun h4 => by omega⟩
  · obtain ⟨a, haA, ha2, ha1, haz, hconj, hbad⟩ := exists_normal_four_bad hyp hA
    have haz' : a * z = z * a := hyp.hzS a haA.1
    have hE := T7A.isElemAbelian2_closure_pair ha2 hz2 ha1 hz1 haz haz'
    have hFA : Subgroup.closure ({a, z} : Set G) ≤
        (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
      rw [Subgroup.closure_le]
      rintro x (rfl | hx)
      · exact haA
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hzA
    have hAeq : Subgroup.closure ({a, z} : Set G) =
        (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :=
      Subgroup.eq_of_le_of_card_ge hFA (by rw [hE.1]; exact h4)
    have hA0 : ∀ b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
        InFour a z b := fun b hb =>
      (inFour_iff_mem_closure ha2 hz2 haz').mpr (hAeq ▸ hb)
    have hFD : FourData hyp a := ⟨ha2, ha1, haz, haA, hconj, hA0⟩
    have hcard : Nat.card ↥((S : Subgroup G) ⊓
        Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) = 4 := by
      rw [← hAeq, hE.1]
      norm_num
    exact ⟨hcard.le, fun _ => ⟨a, hAeq, hbad, hNM G Ω K K' W S R R' z t u₁ u₂ hyp a hFD hbad⟩⟩

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S

