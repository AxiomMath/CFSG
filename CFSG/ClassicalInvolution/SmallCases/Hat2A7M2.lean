module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7M1

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false
namespace CFSG.ClassicalInvolution.Hat2A7M
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7C
open CFSG.ClassicalInvolution.Asc77.T7C
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
theorem mem_of_isSylow2In (hΩ : HypOmegaMod Ω) {K R : Subgroup G} {z : G}
    (hK : K ∈ Ω) (hR : IsSylow2In R K) (hz : IsUniqueInvolution K z) : z ∈ R :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7C.mem_of_isSylow2In hΩ hK hR hz
theorem exists_normal_zpowers_order_four (hΩ : HypOmegaMod Ω) {K R : Subgroup G}
    {z : G} (hK : K ∈ Ω) (hR : IsSylow2In R K) (hz : IsUniqueInvolution K z) :
    ∃ u ∈ R, orderOf u = 4 ∧ ∀ r ∈ R, r * u * r⁻¹ ∈ Subgroup.zpowers u :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7C.exists_normal_zpowers_order_four hΩ hK hR hz
end T7C

@[expose] def C25_RS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23Setting Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → MuIsoE4 Ω W →
      ∃ (S : Sylow 2 G) (R R' : Subgroup G),
        (R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)) ∧
        (R' ∈ RSet Ω ∧ R' ≤ K' ∧ R' ≤ (S : Subgroup G)) ∧
        ∀ X ∈ RSet Ω, X ≤ (S : Subgroup G) → X = R ∨ X = R'

theorem c25_setup_of (h : C25_RS) : C25_setup := by
  intro G _ _ _ Ω K K' z hs W hW hzW hE4
  obtain ⟨S, R, R', hR, hR', hRS⟩ := h G Ω K K' z hs.setting W hW hzW hE4
  have hst : AscStand Ω K := hs.1.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.1.hK'.1
  have hz : IsUniqueInvolution K z := hs.1.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.1.hK'
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hR.1 hR.2.1
  have hR'syl : IsSylow2In R' K' := T7C.isSylow2In_of_mem_RSet_of_le hΩ hK' hR'.1 hR'.2.1
  have hzR : z ∈ R := T7C.mem_of_isSylow2In hΩ hK hRsyl hz
  have hzR' : z ∈ R' := T7C.mem_of_isSylow2In hΩ hK' hR'syl hz'
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := by
    intro s hs'
    have h1 : conjSub s R ∈ RSet Ω := RSet.conj hΩ.conjInvariant hR.1 s
    have h2 : conjSub s R ≤ (S : Subgroup G) := by
      intro x hx
      obtain ⟨r, hr, rfl⟩ := hx
      exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hs' (hR.2.2 hr))
        ((S : Subgroup G).inv_mem hs')
    have hconj : s * z * s⁻¹ ∈ conjSub s R := conj_mem_conjSub hzR
    have hsq : (s * z * s⁻¹) * (s * z * s⁻¹) = 1 := by
      calc (s * z * s⁻¹) * (s * z * s⁻¹) = s * (z * z) * s⁻¹ := by group
        _ = 1 := by rw [hz.sq]; group
    have hne : s * z * s⁻¹ ≠ 1 := by
      intro he
      apply hz.ne_one
      calc z = s⁻¹ * (s * z * s⁻¹) * s := by group
        _ = 1 := by rw [he]; group
    have hzz : s * z * s⁻¹ = z := by
      rcases hRS _ h1 h2 with e | e
      · rw [e] at hconj
        exact (hz.unique _ (hR.2.1 hconj) hsq).resolve_left hne
      · rw [e] at hconj
        exact (hz'.unique _ (hR'.2.1 hconj) hsq).resolve_left hne
    calc s * z = s * z * s⁻¹ * s := by group
      _ = z * s := by rw [hzz]
  have hnab : ∃ a b : G, a * b ≠ b * a := T7C.exists_not_commute_of_stand hst
  obtain ⟨g, hgS, hgne⟩ := T7C.exists_conj_mem_sylow_ne hnab S (hR.2.2 hzR) hzS hz.sq hz.ne_one
  obtain ⟨u₁, hu₁R, o₁, hu₁n⟩ := T7C.exists_normal_zpowers_order_four hΩ hK hRsyl hz
  obtain ⟨u₂, hu₂R, o₂, hu₂n⟩ := T7C.exists_normal_zpowers_order_four hΩ hK' hR'syl hz'
  exact ⟨S, R, R', g⁻¹ * z * g, u₁, u₂,
    Hyp25Data.hyp25 ⟨hW, hzW, hE4, hR, hR', hRS, hzS, ⟨hgS, hgne, g⁻¹, by simp⟩,
      ⟨hu₁R, o₁, hu₁n⟩, ⟨hu₂R, o₂, hu₂n⟩⟩ hs⟩
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
theorem c25_RS_proved : C25_RS := by
  intro G _ _ _ Ω K K' z hs W hW hzW hE4
  exact CFSG.ClassicalInvolution.T7F25.Asc77.c25_RS_proved G Ω K K' z hs.toF W hW hzW
    (hs.stand.e4All hW hE4)
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

theorem c25_E4_of_exits (h19 : C25_19) (h21 : C25_21) : C25_E4 :=
  c25_E4_of_steps (c25_setup_of c25_RS_proved) h19 h21

end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7ER
open CFSG.ClassicalInvolution.Asc77.T7ER
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}

theorem not_commute_of_conj (hs : Hyp23Setting Ω K K' z) {W₀ : Subgroup G}
    (hW₀ : W₀ ∈ WSet Ω) (hE4 : MuIsoE4 Ω W₀) {J : Subgroup G} (hJ : J ∈ Ω) {a : G}
    (ha : IsUniqueInvolution J a) {y : G} (hya : y * z * y⁻¹ ≠ a) {x : G} (hx : x ∈ J)
    (hx4 : orderOf x = 4) : (y * z * y⁻¹) * x ≠ x * (y * z * y⁻¹) :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7ER.not_commute_of_conj hs.toF hW₀ (hs.stand.e4All hW₀ hE4)
    hJ ha hya hx hx4
end T7ER
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

theorem c25_2_t_proved : C25_2_t := by
    intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
    exact CFSG.ClassicalInvolution.T7F25.Asc77.c25_2_t_proved G Ω K K' W S R R' z t u₁ u₂ hyp.toF
end Asc77
end
end CFSG.ClassicalInvolution.Hat2A7M
