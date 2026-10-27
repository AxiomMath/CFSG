module

public import CFSG.GH74.E2.TermPumpUp
public import CFSG.GH74.E2.Leaves
public import CFSG.GH74.Orders.LieType
public import CFSG.LocalAnalysis.ComponentInitial.OddLinearTwoAliases

public section

namespace CFSG.GH74.E2

open Subgroup Blueprint CFSG.GH74.GLS

section Conj

variable {G : Type} [Group G]

theorem conjugate_eq_of_mem_centralizer {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer (K : Set G)) : conjugate K g = K := by
  ext x
  rw [AS16.mem_conjugate_iff']
  constructor
  · intro h
    have hc := Subgroup.mem_centralizer_iff.1 hg _ h
    have h2 : g * x = g * (g * x * g⁻¹) := by
      calc g * x = (g * x * g⁻¹) * g := by group
        _ = g * (g * x * g⁻¹) := hc
    have h3 : x = g * x * g⁻¹ := mul_left_cancel h2
    rw [h3]
    exact h
  · intro hx
    have hc := Subgroup.mem_centralizer_iff.1 hg x hx
    have : g * x * g⁻¹ = x := by
      calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [← hc]
        _ = x := by rw [mul_inv_cancel_right]
    rw [this]
    exact hx

theorem conjugate_Cen_eq {t g y : G} (h : g⁻¹ * t * g = y) : conjugate (Cen t) g = Cen y := by
  rw [← h]
  exact AS16.conjugate_centralizer_singleton t g

end Conj

theorem isTerminalPair_of_card (hComp : ComponentList) (hP : PumpUpData) {G : Type} [Group G]
    [Finite G] (hH : Hyp G) {t : G} (ht : orderOf t = 2) {K : Subgroup G} (hK : IsCompCen t K)
    (h60 : Nat.card ↥K ≠ 60) (h120 : Nat.card ↥K ≠ 120) : IsTerminalPair 2 t K := by
  have ht2 : t * t = 1 := by rw [← sq]; exact sq_eq_one_of_orderOf ht
  refine ⟨ht, hK, ?_, ?_⟩
  · obtain ⟨i, hiK, hi⟩ := AS16.exists_involution_of_isQuasisimple (isCompCen_quasisimple hK)
    have h2 : orderOf (⟨i, hiK⟩ : ↥K) = 2 := by rw [← Subgroup.orderOf_coe]; exact hi
    rw [← h2]
    exact orderOf_dvd_natCard _
  · intro y hy hyK
    have hy2 : y * y = 1 := by rw [← sq]; exact sq_eq_one_of_orderOf hy
    have hKy : K ≤ Cen y := fun k hk =>
      mem_Cen.2 (Subgroup.mem_centralizer_iff.1 hyK k hk).symm
    by_cases hcomm : t * y = y * t
    · exact isCompCen_of_commute hComp hP hH ht hy hcomm hK hKy h60 h120
    · have hty : t * y ∈ Subgroup.centralizer (K : Set G) := by
        refine Subgroup.mem_centralizer_iff.2 fun k hk => ?_
        have h1 : t * k = k * t := mem_Cen.1 (hK.1 hk)
        have h2 : k * y = y * k := Subgroup.mem_centralizer_iff.1 hyK k hk
        calc k * (t * y) = (k * t) * y := by rw [mul_assoc]
          _ = (t * k) * y := by rw [h1]
          _ = t * (k * y) := by rw [mul_assoc]
          _ = t * (y * k) := by rw [h2]
          _ = (t * y) * k := by rw [mul_assoc]
      have hcK : ∀ g ∈ Subgroup.zpowers (t * y), g ∈ Subgroup.centralizer (K : Set G) :=
        fun g hg => Subgroup.zpowers_le.2 hty hg
      rcases dihedral_cases ht2 hy2 with ⟨g, hg, hgty⟩ | ⟨z, hz, hz2, hz1, hzt, hzy⟩
      ·
        have hconjK := conjugate_eq_of_mem_centralizer (hcK g hg)
        have h := AS16.isCompIn_conj hK g
        rw [conjugate_Cen_eq hgty, hconjK] at h
        exact h
      ·
        have hz' : z ^ 2 = 1 := by rw [pow_two]; exact hz2
        have hzo : orderOf z = 2 := by
          have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          exact orderOf_eq_prime hz' hz1
        have hzK : K ≤ Cen z := fun k hk =>
          mem_Cen.2 (Subgroup.mem_centralizer_iff.1 (hcK z hz) k hk).symm
        have hKz : IsCompCen z K :=
          isCompCen_of_commute hComp hP hH ht hzo hzt.symm hK hzK h60 h120
        exact isCompCen_of_commute hComp hP hH hzo hy hzy hKz hKy h60 h120

section Shapes

theorem card_of_shapeL27 {K : Type} [Group K] (h : ShapeL27 K) : Nat.card K = 168 := by
  rcases h with h | h
  · rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) h]
    decide
  · rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) h]
    decide

theorem lieModel_of_shapeL27 {K : Type} [Group K] (h : ShapeL27 K) : LieModel K .PSL 2 7 1 := by
  rcases h with h | h
  · exact h
  · exact CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism K h

theorem card_of_shapeL217 {K : Type} [Group K] (h : ShapeL217 K) : Nat.card K = 2448 := by
  rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) h]
  decide

theorem lieModel_of_shapeA6 {K : Type} [Group K] (h : ShapeA6 K) : LieModel K .PSL 2 3 2 := by
  rcases h with h | h
  · exact Or.inl ⟨by decide,
      CFSG.LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_nine_of_alternating_six K h⟩
  · exact h

theorem card_of_shapeA6 {K : Type} [Group K] (h : ShapeA6 K) : Nat.card K = 360 := by
  rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) (lieModel_of_shapeA6 h)]
  decide

end Shapes

section Consequences

variable (hComp : ComponentList) (hP : PumpUpData) {G : Type} [Group G] [Finite G] (hH : Hyp G)
  {t : G} (ht : orderOf t = 2) {K : Subgroup G} (hK : IsCompCen t K)

include hComp hP hH ht hK

theorem no_component_L27 (hsh : ShapeL27 ↥K) : False := by
  have hcard : Nat.card ↥K = 168 := card_of_shapeL27 hsh
  have hterm := isTerminalPair_of_card hComp hP hH ht hK (by omega) (by omega)
  obtain ⟨-, -, h5 | h9⟩ := hH.restrictedEven.2.2.1 t K hterm 7 1 Nat.prime_seven (by norm_num)
    (lieModel_of_shapeL27 hsh)
  · exact absurd h5.1 (by norm_num)
  · exact absurd h9.1 (by norm_num)

theorem no_component_L217 (hsh : ShapeL217 ↥K) : False := by
  have hcard : Nat.card ↥K = 2448 := card_of_shapeL217 hsh
  have hterm := isTerminalPair_of_card hComp hP hH ht hK (by omega) (by omega)
  obtain ⟨-, -, h5 | h9⟩ := hH.restrictedEven.2.2.1 t K hterm 17 1 (by norm_num) (by norm_num)
    hsh
  · exact absurd h5.1 (by norm_num)
  · exact absurd h9.1 (by norm_num)

theorem a6_terminal_facts (hsh : ShapeA6 ↥K) :
    4 ≤ pRank 2 ↥(Cen t) ∧ ¬ IsCentralInvolution t ∧
      pRank 2 ↥(Subgroup.centralizer (K : Set G)) = 1 := by
  have hcard : Nat.card ↥K = 360 := card_of_shapeA6 hsh
  have hterm := isTerminalPair_of_card hComp hP hH ht hK (by omega) (by omega)
  obtain ⟨h4, hc, h5 | h9⟩ := hH.restrictedEven.2.2.1 t K hterm 3 2 Nat.prime_three (by norm_num)
    (lieModel_of_shapeA6 hsh)
  · exact absurd h5.1 (by norm_num)
  · exact ⟨h4, hc, h9.2⟩

end Consequences

theorem noCaseIIBetaL27_of (hComp : ComponentList) (hP : PumpUpData) : NoCaseIIBetaL27 := by
  intro G _ _ hH t t' a A B K hc hK hsh _ _
  exact no_component_L27 hComp hP hH hc.order_t hK hsh

theorem noCaseIIBetaL217_of (hComp : ComponentList) (hP : PumpUpData) : NoCaseIIBetaL217 := by
  intro G _ _ hH t t' a A B K hc hK hsh _ _
  exact no_component_L217 hComp hP hH hc.order_t hK hsh

theorem noCaseIIBeta_of_pumpup (hComp : ComponentList) (hP : PumpUpData)
    (hA5 : NoCaseIIBetaA5) (hA6 : NoCaseIIBetaA6) (hL3 : NoCaseIIBetaL33)
    (hM : NoCaseIIBetaM11) : NoCaseIIBeta :=
  noCaseIIBeta_of_shapes hA5 (noCaseIIBetaL27_of hComp hP) hA6 (noCaseIIBetaL217_of hComp hP) hL3 hM

end CFSG.GH74.E2
