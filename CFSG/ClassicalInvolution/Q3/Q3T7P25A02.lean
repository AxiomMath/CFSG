module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25A01
public import CFSG.ClassicalInvolution.Q3.Q3T7F25PW

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

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
open CFSG.ClassicalInvolution.Asc77.T7C2
open scoped commutatorElement

@[expose] def C25_20 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R') →
        ∃ s t' : G, s ∈ (S : Subgroup G) ∧ t' ∈ (S : Subgroup G) ∧ (∃ g : G, g * z * g⁻¹ = t') ∧
          conjSub t' R = R' ∧ s * s = 1 ∧ s * t' = t' * s ∧ conjSub s R = R ∧
          (∃ r ∈ R, ⁅s, r⁆ ∉ T7DR.squaresSub R) ∧
          Subgroup.closure (((R ⊔ R' : Subgroup G) : Set G) ∪ {s, t'}) = (S : Subgroup G)

theorem c25_20_coord_of (h : C25_20) : C25_20_coord := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  exact CFSG.ClassicalInvolution.T7F25.Asc77.c25_20_coord_of_at hyp.toF
    (h G Ω K K' W S R R' z t u₁ u₂ hyp)

theorem c25_21_of_sylow (h20 : C25_20) : C25_21 :=
  c25_21_of_sylow_coord (c25_20_coord_of h20)
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
namespace T75
open CFSG.ClassicalInvolution.Asc77.T75
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
  {S : Sylow 2 G} {η β : Set (Subgroup G)}

theorem Data.false_of_sup_mem_RSet (D : Data Ω S η β) {U V : Subgroup G} (hU : U ∈ β)
    (hV : V ∈ β) (hne : U ≠ V) (hR : U ⊔ V ∈ RSet Ω) : False := by
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR
  exact D.symm.distinct hU hV hne hK (le_sup_left.trans hRK.1) (le_sup_right.trans hRK.1)

theorem Data.exists_conj_eq [Finite G] (D : Data Ω S η β) :
    ∃ c : G, conjSub c (⨆ A ∈ η, A) = ⨆ A ∈ β, A :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T75.Data.exists_conj_eq D.toF
end T75

theorem l7_5_2_proved : L7_5_2 := by
  intro G _ _ Ω hU W hW W' hW'
  exact CFSG.ClassicalInvolution.T7F25.Asc77.l7_5_2_of (Q3T7P25.hyp_of_modU hU) (T75.oddConj hU)
    hW hW'

end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7D
open CFSG.ClassicalInvolution.Asc77.T7D
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem ctx_of_stand {K : Subgroup G} (hs : AscStand Ω K) (hW : W ∈ WSet Ω) :
    Q3CL.Thompson.Ctx Ω W :=
  ⟨hs.hyp, hW,
    Q3CL.thompsonKey ⟨hs.hyp, hs.cls, hs.aEmpty⟩ W hW, hs.aEmpty⟩

theorem exists_rep (hΩ : HypOmegaMod Ω) (hW : W ∈ WSet Ω)
    {K R : Subgroup G} (hK : K ∈ Ω) (hRK : IsSylow2In R K) (hRD : R ∈ DSet Ω W) :
    ∃ ρ : Thompson.Rep Ω W, ρ.K = K ∧ ρ.R = R :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7D.exists_rep hΩ hW hK hRK hRD

theorem exists_sylow_frame {K K' : Subgroup G} {z : G} (hs : Hyp23Setting Ω K K' z)
    (hW : W ∈ WSet Ω) (hzW : z ∈ W) :
    ∃ (S : Sylow 2 G) (R R' : Subgroup G), W ≤ (S : Subgroup G) ∧ IsSylow2In R K ∧
      IsSylow2In R' K' ∧ R ≤ (S : Subgroup G) ∧ R' ≤ (S : Subgroup G) :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7D.exists_sylow_frame hs.toF hW hzW
end T7D

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

theorem c25_E4_of_sylow (h2 : C25_2_t) (h17 : C25_17_idx) (h20 : C25_20) :
    C25_E4 :=
  c25_E4_of_exits (c25_19_of_sylow h2 h17) (c25_21_of_sylow h20)
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

theorem omegaStarNbr_subset_omegaNbr_of_E4 {K K₁ : Subgroup G} (hs : AscStand Ω K)
    {W₀ : Subgroup G} (hW₀ : W₀ ∈ WSet Ω) (hE4 : MuIsoE4 Ω W₀) (hK₁ : K₁ ∈ Ω) :
    omegaStarNbr Ω K₁ ⊆ omegaNbr Ω K₁ :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7ER.omegaStarNbr_subset_omegaNbr_of_E4 hs.toF hW₀
    (hs.e4All hW₀ hE4) hK₁
end T7ER
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

theorem not_le_centralizer_of_mem_USet (hs : Hyp23Setting Ω K K' z) {W₀ : Subgroup G}
    (hW₀ : W₀ ∈ WSet Ω) (hE4 : MuIsoE4 Ω W₀) {J : Subgroup G} (hJ : J ∈ Ω)
    (hJt : J ∉ twinSet Ω K) {V : Subgroup G} (hV : V ∈ USet Ω) (hVJ : V ≤ J) :
    ¬ V ≤ Subgroup.centralizer ({z} : Set G) :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7ER.not_le_centralizer_of_mem_USet hs.toF hW₀
    (hs.stand.e4All hW₀ hE4) hJ hJt hV hVJ

theorem not_commute_of_orderOf_four (hs : Hyp23Setting Ω K K' z) {W₀ : Subgroup G}
    (hW₀ : W₀ ∈ WSet Ω) (hE4 : MuIsoE4 Ω W₀) {J : Subgroup G} (hJ : J ∈ Ω)
    (hJt : J ∉ twinSet Ω K) {x : G} (hx : x ∈ J) (hx4 : orderOf x = 4) : z * x ≠ x * z :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7ER.not_commute_of_orderOf_four hs.toF hW₀
    (hs.stand.e4All hW₀ hE4) hJ hJt hx hx4

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
namespace T7ER
open CFSG.ClassicalInvolution.Asc77.T7ER
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}

theorem conjSub_eq_of_centralizes (hs : Hyp23Setting Ω K K' z) {u : G} (hu : u * z = z * u) :
    conjSub u K = K ∨ conjSub u K = K' :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7ER.conjSub_eq_of_centralizes hs.toF hu

theorem normalizes_iff_of_centralizes (hs : Hyp23Setting Ω K K' z) {u : G}
    (hu : u * z = z * u) : conjSub u K = K ↔ conjSub u K' = K' :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7ER.normalizes_iff_of_centralizes hs.toF hu
end T7ER
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
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem exists_notNormalizing_conj (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {g : G}
    (hg : g * z * g⁻¹ = t) (hRt : conjSub t R = R) :
    ∃ s' : G, s' * s' = 1 ∧ s' * z = z * s' ∧ (∃ y : G, y * z * y⁻¹ = s') ∧
      conjSub s' K ≠ K :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7ER.exists_notNormalizing_conj hyp.toF hg hRt
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

end CFSG.ClassicalInvolution.Q3.Q3T8
