module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25W01
public import CFSG.ClassicalInvolution.Asc77.AscCX1
public import CFSG.Goldschmidt75.CorollaryA2

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

section Quaternion

variable {G : Type} [Group G]

theorem exists_quaternion_comm_of_card_eight {R : Subgroup G} (hQ : IsQuatSub R)
    (h8 : Nat.card R = 8) :
    ∃ x ∈ R, ∃ y ∈ R, x * y * x⁻¹ * y⁻¹ = x * x ∧ x * x * (x * x) = 1 ∧ x * x ≠ 1 ∧
      x * y ≠ y * x := by
  obtain ⟨k, hk, ⟨e⟩⟩ := hQ
  have hcard : Nat.card R = 4 * 2 ^ k := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hk1 : k = 1 := by
    have h4 : 4 * 2 ^ k = 8 := by rw [← hcard]; exact h8
    have h2 : 2 ^ k = 2 ^ 1 := by omega
    exact Nat.pow_right_injective (le_refl 2) h2
  subst hk1
  have e' : R ≃* QuaternionGroup 2 := e
  have k0 : ((QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 1 *
      (QuaternionGroup.xa 0)⁻¹ * (QuaternionGroup.xa 1)⁻¹ =
      QuaternionGroup.xa 0 * QuaternionGroup.xa 0) := by decide
  have k2 : ((QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0) *
      (QuaternionGroup.xa 0 * QuaternionGroup.xa 0) = 1 := by decide
  have k3 : ((QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0) ≠ 1 := by decide
  have k4 : ((QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 1) ≠
      QuaternionGroup.xa 1 * QuaternionGroup.xa 0 := by decide
  refine ⟨(e'.symm (QuaternionGroup.xa 0) : G), (e'.symm _).2,
    (e'.symm (QuaternionGroup.xa 1) : G), (e'.symm _).2, ?_, ?_, ?_, ?_⟩
  · have := congrArg e'.symm k0
    simp only [map_mul, map_inv] at this
    exact congrArg Subtype.val this
  · have := congrArg e'.symm k2
    simp only [map_mul, map_one] at this
    exact congrArg Subtype.val this
  · intro h
    apply k3
    apply e'.symm.injective
    simp only [map_mul, map_one]
    exact Subtype.ext h
  · intro h
    apply k4
    apply e'.symm.injective
    simp only [map_mul]
    exact Subtype.ext h

end Quaternion

section Odd

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem goldschmidtOddCore_eq_bot_of_simple {z : G} (hz2 : orderOf z = 2) :
    goldschmidtOddCore G = ⊥ := by
  unfold goldschmidtOddCore
  rw [sSup_eq_bot]
  rintro N ⟨hN, hodd⟩
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    rw [h, Subgroup.card_top] at hodd
    obtain ⟨k, hk⟩ : 2 ∣ Nat.card G := hz2 ▸ orderOf_dvd_natCard z
    have := Nat.odd_iff.mp hodd
    omega

theorem normalClosure_eq_top_of_ne_bot {H : Subgroup G} (hH : H ≠ ⊥) :
    Subgroup.normalClosure (H : Set G) = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure (H : Set G)) with h | h
  · exfalso
    apply hH
    rw [eq_bot_iff]
    intro a ha
    have h1 := Subgroup.subset_normalClosure ha
    rw [h] at h1
    exact h1
  · exact h

end Odd

section Standins

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G} {t u₁ u₂ : G}

theorem false_of_stronglyClosed (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {E : Subgroup G}
    (hEA : E ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hE1 : E ≠ ⊥) (hsc : fusionStronglyClosed (E : Set G) S) : False := by
  classical
  obtain ⟨t', h⟩ := T7T.exists_hyp25T hyp
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hst := hs.stand
  have hΩ : HypOmegaModT Ω := hst.modU
  have hzK : IsUniqueInvolution K z := hs.hz
  have hz1 : z ≠ 1 := hzK.ne_one
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzK.sq) hz1
  have hRsyl : IsSylow2In R K := h.hRsyl
  have h8 : Nat.card R = 8 := CFSG.ClassicalInvolution.Q3.Q3T7P25.natCard_isSylow2In_member hΩ
    hst.mem hRsyl
  obtain ⟨x, hxR, y, hyR, hcomm, hx4, hx1, hxy⟩ :=
    exists_quaternion_comm_of_card_eight (hΩ.isQuatSub_of_mem_RSet hyp.hR.1) h8
  have hxz : x * x = z :=
    (hzK.unique (x * x) (K.mul_mem (hRsyl.1 hxR) (hRsyl.1 hxR)) hx4).resolve_left hx1
  have hES : E ≤ (S : Subgroup G) := fun a ha => (hEA ha).1
  have hRC : ∀ r ∈ R, r ∈ Subgroup.centralizer (E : Set G) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (Subgroup.mem_centralizer_iff.mp (hEA he).2 r (Subgroup.mem_sup_left hr)).symm
  set C : Subgroup G := Subgroup.centralizer (E : Set G) with hC
  set S₀ : Subgroup G := ⁅C, C⁆ ⊓ (S : Subgroup G) with hS₀
  have hS₀sc : fusionStronglyClosed (S₀ : Set G) (S : Subgroup G) :=
    Goldschmidt75.theoremB_c S hES hsc
  have hS₀C : S₀ ≤ C := by
    intro s hs₀
    refine (Subgroup.commutator_le.mpr (fun g₁ h₁ g₂ h₂ => ?_)) hs₀.1
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem h₁ h₂) (C.inv_mem h₁)) (C.inv_mem h₂)
  have hzS₀ : z ∈ S₀ := by
    refine ⟨?_, (T7T.z_mem_centralizer_of_hyp hyp).1⟩
    have hcm : ⁅x, y⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator (hRC x hxR) (hRC y hyR)
    rw [commutatorElement_def, hcomm, hxz] at hcm
    exact hcm
  have hS₀1 : S₀ ≠ ⊥ := fun h0 => hz1 (by simpa [h0] using hzS₀)
  have hcomm0 : ⁅E, S₀⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro s hs₀
    exact (Subgroup.mem_centralizer_iff.mp (hS₀C hs₀) e he).symm
  have hA2 := Goldschmidt75.corollaryA2 S S hES (inf_le_right : S₀ ≤ (S : Subgroup G)) hsc hS₀sc
    hcomm0
  have hperf : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆) with
      h0 | h0
    · exfalso
      apply hxy
      have hm : ⁅x, y⁆ ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
      exact hm
    · exact h0
  rw [normalClosure_eq_top_of_ne_bot hE1, normalClosure_eq_top_of_ne_bot hS₀1, hperf,
    goldschmidtOddCore_eq_bot_of_simple hz2, sup_bot_eq] at hA2
  have hF1 : E ⊓ S₀ ≠ ⊥ := by
    intro hF
    rw [hF] at hA2
    have h1 : Subgroup.normalClosure (((⊥ : Subgroup G)) : Set G) = ⊥ :=
      le_bot_iff.mp (Subgroup.normalClosure_le_normal (N := ⊥) (fun a ha => ha))
    rw [h1] at hA2
    exact hz1 (Subgroup.mem_bot.mp (hA2 (Subgroup.mem_top z)))
  have hFS : E ⊓ S₀ ≤ (S : Subgroup G) := fun a ha => hES ha.1
  have hFab : ∀ a ∈ E ⊓ S₀, ∀ b ∈ E ⊓ S₀, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (hS₀C hb.2) a ha.1
  have hFsc : ∀ a ∈ E ⊓ S₀, ∀ g : G, g * a * g⁻¹ ∈ (S : Subgroup G) → g * a * g⁻¹ ∈ E ⊓ S₀ := by
    intro a ha g hg
    have h1 := hsc a ha.1 g⁻¹ (by simpa using hg)
    have h2 := hS₀sc a ha.2 g⁻¹ (by simpa using hg)
    simp only [inv_inv] at h1 h2
    exact ⟨h1, h2⟩
  exact l17_8_of_hyp25 hyp hFS hF1 hFab ⟨hFS, hFsc⟩

end Standins

@[expose] def LayerTwinFactsFive3 : Prop :=
  ∀
    {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)} (D : LieSystemData 3 1 Y Φ)
    {A A' : Subgroup Y} {z' a₀ b₀ : Y},
    D.card = 1 → (∃ i : Fin D.card, IsOrthTag 5 true (D.tag i) (D.rank i)) →
      TwinSect0 Φ A A' z' a₀ b₀ → CFSG.ClassicalInvolution.Asc77.CX.LayerTwinFacts A A' z'

class Facts25V : Prop where
  nc4 :
        Q3T8.Asc77.C25X.NC4Fact
  layer5Sq :
        Q3T8.Asc77.C25W.Layer5Sq
  layerTwin : LayerTwinFactsFive3

section TwinFacts

variable [Facts25V]

theorem layerTwinFacts_five {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)}
    (D : LieSystemData 3 1 Y Φ) {A A' : Subgroup Y} {z' a₀ b₀ : Y} (hD1 : D.card = 1)
    (hi : ∃ i : Fin D.card, IsOrthTag 5 true (D.tag i) (D.rank i))
    (htw : TwinSect0 Φ A A' z' a₀ b₀) :
    CFSG.ClassicalInvolution.Asc77.CX.LayerTwinFacts A A' z' :=
  Facts25V.layerTwin D hD1 hi htw

end TwinFacts

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX
