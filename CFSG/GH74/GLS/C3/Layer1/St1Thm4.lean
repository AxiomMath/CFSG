module

public import CFSG.GH74.GLS.C3.Layer1.St1Bal
public import CFSG.GH74.GLS.C3.Layer1.St1Leaves
public import CFSG.GH74.GLS.C3.Layer1.BackLeaves
public import CFSG.GH74.GLS.Bg.Rank
public import CFSG.GH74.GLS.TwoThin.ClassCongr
public import CFSG.LieType.Catalog.Realization

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

@[expose] def B_iv2_4_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x : G) (K : Subgroup G), IsIL2Pair x K →
    InU2 (kBar K) → ∀ A : Subgroup G, IsEStar A → x ∈ A → A ≤ normalizer (K : Set G)

@[expose] def B_ivk_L29_rank : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K : Subgroup G),
    IsUnbalancingTriple x y K → HasL2Model (kBar K) (fun q => q = 9) →
      ∀ A : Subgroup G, A ≤ NxK x K → CFSG.IsElementaryAbelian 2 ↥A → y ∈ A →
        Nat.card ↥A ≤ 4 * Nat.card ↥(A ⊓ CxK x K)

@[expose] def B_ivk_rank_add_L29 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x : G) (K : Subgroup G), IsIL2Pair x K →
    HasL2Model (kBar K) (fun q => q = 9) → pRank 2 ↥(CxK x K) + 2 ≤ pRank 2 G

section EStarBasic

variable {G : Type} [Group G]

theorem IsEStar.pow_two {A : Subgroup G} (hA : IsEStar A) {a : G} (ha : a ∈ A) : a ^ 2 = 1 := by
  have := hA.1
  exact CFSG.elemPow_eq_one_of_isElementaryAbelian a ha

theorem IsEStar.orderOf_eq_two {A : Subgroup G} (hA : IsEStar A) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) : orderOf a = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (hA.pow_two ha) ha1

theorem IsEStar.commute {A : Subgroup G} (hA : IsEStar A) {a b : G} (ha : a ∈ A) (hb : b ∈ A) :
    a * b = b * a := by
  have := hA.1
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩)

theorem IsEStar.isPGroup {A : Subgroup G} (hA : IsEStar A) : IsPGroup 2 ↥A := by
  have := hA.1
  exact CFSG.IsElementaryAbelian.isPGroup 2 ↥A

theorem IsEStar.sub {A B : Subgroup G} (hA : IsEStar A) (hBA : B ≤ A) :
    CFSG.IsElementaryAbelian 2 ↥B :=
  { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (hA.commute (hBA x.2) (hBA y.2))⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
      Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hA.pow_two (hBA x.2)) }

end EStarBasic

section EStar

variable {G : Type} [Group G] [Finite G]

theorem le_pRank_of_elem {H B : Subgroup G} (hBH : B ≤ H) (hB : CFSG.IsElementaryAbelian 2 ↥B)
    {k : ℕ} (hk : Nat.card ↥B = 2 ^ k) : k ≤ pRank 2 ↥H := by
  have := hB
  rw [Bg.pRank_subgroup_eq_open]
  exact CFSG.SectionRank.le_pRank one_lt_two hBH
    ⟨inferInstance, fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩ hk

theorem le_pRank_group_of_elem {B : Subgroup G} (hB : CFSG.IsElementaryAbelian 2 ↥B)
    {k : ℕ} (hk : Nat.card ↥B = 2 ^ k) : k ≤ pRank 2 G := by
  have := hB
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.le_pRank one_lt_two le_top
    ⟨inferInstance, fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩ hk

theorem IsEStar.isStar2 {A : Subgroup G} (hA : IsEStar A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    IsStar2 a := by
  refine ⟨hA.orderOf_eq_two ha ha1, le_antisymm (Bg.pRank_subgroup_le one_lt_two _) ?_⟩
  refine le_pRank_of_elem (B := A) ?_ hA.1 hA.2
  intro c hc
  exact mem_centralizer_singleton_iff.mpr (hA.commute hc ha)

theorem IsEStar.mem_of_commute {A : Subgroup G} (hA : IsEStar A) {z : G} (hz : orderOf z = 2)
    (hc : ∀ a ∈ A, z * a = a * z) : z ∈ A := by
  by_contra hzA
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  set k : Set G := (A : Set G) ∪ {z} with hk
  have hcomm : k.Pairwise Commute := by
    intro u hu v hv _
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact hA.commute hu hv
    · rw [Set.mem_singleton_iff.mp hv]
      exact (hc u hu).symm
    · rw [Set.mem_singleton_iff.mp hu]
      exact hc v hv
    · rw [Set.mem_singleton_iff.mp hu, Set.mem_singleton_iff.mp hv]
  set A' : Subgroup G := Subgroup.closure k with hA'
  have : IsMulCommutative A' := Subgroup.isMulCommutative_closure hcomm
  have hpow : ∀ x ∈ A', x ^ 2 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact hA.pow_two hx
      · rw [Set.mem_singleton_iff.mp hx]; exact hz2
    | one => exact one_pow 2
    | mul x y hx hy hx2 hy2 =>
      have hxy : Commute x y := by
        have := mul_comm' (⟨x, hx⟩ : A') ⟨y, hy⟩
        exact congrArg Subtype.val this
      rw [hxy.mul_pow, hx2, hy2, one_mul]
    | inv x hx hx2 => rw [inv_pow, hx2, inv_one]
  have hA'ea : CFSG.IsElementaryAbelian 2 ↥A' :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by
          rw [Subgroup.coe_pow, Subgroup.coe_one]
          exact hpow x x.2) }
  have hpg : IsPGroup 2 ↥A' := by
    have := hA'ea
    exact CFSG.IsElementaryAbelian.isPGroup 2 ↥A'
  obtain ⟨m, hm⟩ := hpg.exists_card_eq
  have hAA' : A ≤ A' := fun a ha => Subgroup.subset_closure (Or.inl ha)
  have hzA' : z ∈ A' := Subgroup.subset_closure (Or.inr rfl)
  have hlt : A < A' := lt_of_le_of_ne hAA' (fun h => hzA (h ▸ hzA'))
  have hcard : Nat.card ↥A < Nat.card ↥A' := Subgroup.card_lt_of_lt hlt
  have hm' : m ≤ pRank 2 G := le_pRank_group_of_elem hA'ea hm
  rw [hA.2, hm] at hcard
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hcard
  omega

theorem exists_isSylowOf_ge {N K : Subgroup G} (hKN : K ≤ N) (hK : IsPGroup 2 ↥K) :
    ∃ R : Subgroup G, IsSylowOf 2 R N ∧ K ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hKR, hRN, hRp, hRidx⟩ := C3.Layer1.P34.exists_sylow_ge hKN hK
  exact ⟨R, isSylowOf_iff.2 ⟨hRN, hRp, hRidx⟩, hKR⟩

end EStar

section Thm4

theorem isElementaryAbelian_bot {X : Type} [Group X] : CFSG.IsElementaryAbelian 2 ↥(⊥ : Subgroup X) :=
  { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
      Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.mem_bot.mp x.2, one_pow, Subgroup.coe_one]) }

theorem center_eq_bot_of_simple_quasisimple {Q : Type} [Group Q] (hs : IsSimpleGroup Q)
    (hq : CFSG.IsQuasisimple Q) : center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have hx : x ∈ center Q := h ▸ Subgroup.mem_top x
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (Subgroup.mem_center_iff.mp hx y).symm

variable {G : Type} [Group G] [Finite G]

theorem false_of_unbalancing_estar
    (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem)
    (h47 : B_iv2_4_7) (hrank : B_ivk_L29_rank) (hadd : B_ivk_rank_add_L29)
    (hG : C3Hyp G) (hN : NoU2Triple G) (h41 : St1Prop41 G) (h51 : St1Prop51 G)
    {A : Subgroup G} (hA : IsEStar A) {a b : G} (ha : a ∈ A) (hb : b ∈ A) {J : Subgroup G}
    (hJ : IsUnbalancingTriple a b J) : False := by
  have hr4 : pRank 2 G = 4 := hG.pRank_eq_four
  have ha1 : a ≠ 1 := fun h => by
    have := hJ.1.1
    rw [h, orderOf_one] at this
    omega
  have hStar : IsStar2 a := hA.isStar2 ha ha1
  have hU2 : InU2 (kBar J) := h102 G hG a b J hJ.isLocallyUnbalancing
  have hAC : A ≤ centralizer ({a} : Set G) := fun c hc =>
    mem_centralizer_singleton_iff.mpr (hA.commute hc ha)
  have hAN : A ≤ NxK a J := le_inf hAC (h47 G hG a J hJ.1 hU2 A hA ha)
  obtain ⟨R, hRsyl, hAR⟩ := exists_isSylowOf_ge hAN hA.isPGroup
  obtain ⟨-, hcase, z, J', hpump, htriv, hterm, -, hzcent, -, hzStar⟩ :=
    h51 a b J R hJ hStar hRsyl (hAR hb)
  have hzA : z ∈ A := hA.mem_of_commute hzStar.1 fun c hc => hzcent c (hAR hc)
  have hJ'u : IsUnbalancingTriple z b J' := hterm.unbalancing
  have hU2' : InU2 (kBar J') := h102 G hG z b J' hJ'u.isLocallyUnbalancing
  have hL29 : HasL2Model (kBar J) (fun q => q = 9) := by
    rcases hcase with h | ⟨hl34, hel, hcard⟩
    · exact h
    · exact (hL34 G hG.gen4 a J hJ.1.1 hJ.1.2 ⟨hl34, hel, hcard⟩).elim
  obtain ⟨-, ⟨e⟩⟩ := htriv J' hpump
  have hL29' : HasL2Model (kBar J') (fun q => q = 9) :=
    TwoThin.hasL2Model_of_mulEquiv e.symm hL29
  have hAN' : A ≤ NxK z J' :=
    le_inf (fun c hc => mem_centralizer_singleton_iff.mpr (hA.commute hc hzA))
      (h47 G hG z J' hJ'u.1 hU2' A hA hzA)
  have hAcard : Nat.card ↥A = 16 := by rw [hA.2, hr4]; norm_num
  have hB := hrank G hG z b J' hJ'u hL29' A hAN' hA.1 hb
  have hBle : A ⊓ CxK z J' ≤ A := inf_le_left
  have hBea := hA.sub hBle
  have hBpg : IsPGroup 2 ↥(A ⊓ CxK z J') := by
    have := hBea
    exact CFSG.IsElementaryAbelian.isPGroup 2 ↥(A ⊓ CxK z J')
  obtain ⟨k, hk⟩ := hBpg.exists_card_eq
  have hk2 : 2 ≤ k := by
    have h16 : 16 ≤ 4 * 2 ^ k := by rw [← hk, ← hAcard]; exact hB
    by_contra hlt
    have hlt' : k < 2 := not_le.mp hlt
    interval_cases k <;> omega
  have hrank2 : 2 ≤ pRank 2 ↥(CxK z J') := hk2.trans (le_pRank_of_elem inf_le_right hBea hk)
  have hrank_le : pRank 2 ↥(CxK z J') ≤ 2 := by
    have := hadd G hG z J' hJ'u.1 hL29'
    omega
  have hh : pRank 2 ↥(CxK z J') = 2 := le_antisymm hrank_le hrank2
  by_cases hT : IsTwoTerminal z J'
  ·
    apply hN
    refine ⟨z, b, J', hJ'u.isLocallyUnbalancing, hT, hzStar, ?_, ?_⟩
    · intro hl34
      exfalso
      have hsimple : IsSimpleGroup (kBar J') := by
        obtain ⟨p, f, hp, hf, hP, hL⟩ := hL29'
        exact (CFSG.LieType.Catalog.lieModel_finite_simple _ _ _ _ _ hL).2.2
      have hcen : center (kBar J') = ⊥ := center_eq_bot_of_simple_quasisimple hsimple hU2'.1
      refine hL34 G hG.gen4 z J' hJ'u.1.1 hJ'u.1.2 ⟨hl34, ?_, ?_⟩
      · rw [hcen]; exact isElementaryAbelian_bot
      · rw [hcen, Subgroup.card_bot]; norm_num
    · intro _
      exact ⟨by omega, Or.inr (by omega)⟩
  ·
    have h4B : Hyp4B z b J' := ⟨⟨hJ'u, hterm.trivialPumpups⟩, hT, hterm.sylow⟩
    have := h41.2 z b J' h4B
    omega

theorem thm4_of_leaves
    (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem) (h47 : B_iv2_4_7)
    (hrank : B_ivk_L29_rank) (hadd : B_ivk_rank_add_L29) (hG : C3Hyp G) (hN : NoU2Triple G)
    (h41 : St1Prop41 G) (h51 : St1Prop51 G) : St1Thm4 G := by
  intro A hA
  apply isBalancedWrt_of_forall
  intro a ha ha1 b hb hb1
  by_contra hnot
  obtain ⟨J, hJ⟩ := exists_isUnbalancingTriple_of_not_le (hA.orderOf_eq_two ha ha1)
    (hA.orderOf_eq_two hb hb1) (hA.commute ha hb) hnot
  exact false_of_unbalancing_estar h102 hL34 h47 hrank hadd hG hN h41 h51 hA ha hb hJ

end Thm4

theorem b_st1_thm4_of_leaves
    (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem) (h47 : B_iv2_4_7)
    (hrank : B_ivk_L29_rank) (hadd : B_ivk_rank_add_L29) : B_st1_thm4 :=
  fun _ _ _ hG hN _ h41 h51 => thm4_of_leaves h102 hL34 h47 hrank hadd hG hN h41 h51

end CFSG.GH74.GLS
