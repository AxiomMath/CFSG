module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzEightSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralTwoCoverTransfer

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.ProperTwoGeneratedCore.TheoremC

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

theorem mul_comm_of_mul_self_eq_one {X : Type*} [Group X] {a b : X} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b * (a * b) = 1) : a * b = b * a := by
  calc a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left hab
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]

namespace SzEightSetting

variable (hs : SzEightSetting S H z J)
include hs

theorem false_of_psl2
    (e : (J ⧸ Subgroup.center J) ≃* CFSG.Theory.Comparator.PSL2Model 2) : False := by
  have := hs.normal
  set Q := sylowJ hs.central J with hQ
  have hab : ∀ a ∈ (sylowStar hs.central J : Subgroup (J ⧸ Subgroup.center J)),
      ∀ b ∈ (sylowStar hs.central J : Subgroup (J ⧸ Subgroup.center J)), a * b = b * a := by
    set U : Sylow 2 (CFSG.Theory.Comparator.PSL2Model 2) :=
      (sylowStar hs.central J).mapSurjective (f := e.toMonoidHom) e.surjective with hU
    obtain ⟨hUel, -⟩ := CFSG.Walter.psl2_even_sylow_two le_rfl U
    have hmem : ∀ a ∈ (sylowStar hs.central J : Subgroup (J ⧸ Subgroup.center J)),
        e a ∈ (U : Subgroup _) := fun a ha => by
      have hUc : (U : Subgroup (CFSG.Theory.Comparator.PSL2Model 2)) =
          (sylowStar hs.central J : Subgroup (J ⧸ Subgroup.center J)).map e.toMonoidHom := rfl
      rw [hUc]
      exact ⟨a, ha, rfl⟩
    intro a ha b hb
    have h := congrArg Subtype.val
      (hUel.toIsMulCommutative.is_comm.comm ⟨e a, hmem a ha⟩ ⟨e b, hmem b hb⟩)
    apply e.injective
    simpa using h
  have hc : ∀ w : J, w ∈ (Q : Subgroup J) →
      InCenterOf ((Q : Subgroup J).map (QuotientGroup.mk' _)) (w : J ⧸ Subgroup.center J) := by
    intro w hw
    have hw' : (w : J ⧸ Subgroup.center J) ∈ (sylowStar hs.central J : Subgroup _) := by
      rw [coe_sylowStar]
      exact ⟨w, hw, rfl⟩
    refine ⟨⟨w, hw, rfl⟩, fun q hq => ?_⟩
    rw [← coe_sylowStar] at hq
    exact hab q hq _ hw'
  obtain ⟨x, hxQ, hxx, hxZ⟩ := hs.exists_involution_sylowJ
  have hsq : ∀ w ∈ (Q : Subgroup J), w * w = 1 := fun w hw =>
    hs.mul_self_eq_one_of_inCenterOf hxx hxZ (hc x hxQ) (hc w hw)
  have hQab : ∀ a ∈ (Q : Subgroup J), ∀ b ∈ (Q : Subgroup J), a * b = b * a :=
    fun a ha b hb => mul_comm_of_mul_self_eq_one (hsq a ha) (hsq b hb) (hsq _ (mul_mem ha hb))
  have hbot := CentralTwoCover.central_pSubgroup_eq_bot_of_perfect hs.commutator_eq_top Q
    le_rfl hs.center_le_sylowJ hQab
  have hcard := hs.card_center
  rw [hbot, Subgroup.card_bot] at hcard
  exact absurd hcard (by decide)

end SzEightSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
