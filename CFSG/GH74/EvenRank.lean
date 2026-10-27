module

import CFSG.GroupTheory.LocalCores.Layer
import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
import CFSG.LocalAnalysis.PreuniquenessRankFour.GeneratorRank
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
public import CFSG.GH74.Defs
public import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.GH74

open Subgroup

theorem inf_centralizer_map_subtype_le_iff {G : Type*} [Group G] (H : Subgroup G)
    (Q : Subgroup H) :
    H ⊓ centralizer ((Q.map H.subtype : Subgroup G) : Set G) ≤ Q.map H.subtype ↔
      centralizer (Q : Set H) ≤ Q := by
  constructor
  · intro h x hx
    have hx' : (x : G) ∈ H ⊓ centralizer ((Q.map H.subtype : Subgroup G) : Set G) := by
      refine ⟨x.2, mem_centralizer_iff.2 ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (mem_centralizer_iff.1 hx y hy)
    obtain ⟨y, hy, hyx⟩ := h hx'
    exact (Subtype.ext hyx : y = x) ▸ hy
  · intro h x hx
    obtain ⟨hxH, hxc⟩ := hx
    have hx' : (⟨x, hxH⟩ : H) ∈ centralizer (Q : Set H) := by
      refine mem_centralizer_iff.2 fun y hy => Subtype.ext ?_
      exact mem_centralizer_iff.1 hxc _ ⟨y, hy, rfl⟩
    exact ⟨⟨x, hxH⟩, h hx', rfl⟩

theorem isCharTwoType_iff {G : Type*} [Group G] :
    CFSG.Assembly.IsCharTwoType G ↔ CFSG.IsCharacteristicPType G 2 :=
  CFSG.Assembly.isCharTwoType_iff_isCharacteristicPType

theorem SectionalTwoRankLE.rank_le_of_isPGroup {X : Type*} [Group X] [Finite X] {r : ℕ}
    (h : SectionalTwoRankLE X r) {P : Subgroup X} (hP : IsPGroup 2 P) : Group.rank P ≤ r := by
  obtain ⟨s, hs, hsP⟩ := h P hP
  exact (Subgroup.rank_congr hsP.symm).le.trans
    ((Subgroup.rank_closure_finset_le_card s).trans hs)

theorem Gen4.rank_le_four {X : Type*} [Group X] [Finite X] (h : Gen4 X) {P : Subgroup X}
    (hP : IsPGroup 2 P) : Group.rank P ≤ 4 :=
  SectionalTwoRankLE.rank_le_of_isPGroup h hP

open CFSG.PreuniquenessRankFour.Helpers in
theorem pRank_le_two_of_faithful_action_on_gen4_twoGroup {A Q : Type*} [Group A] [Finite A]
    [Group Q] [Finite Q] [MulDistribMulAction A Q] (hQ : IsPGroup 2 Q) (hQ4 : Group.rank Q ≤ 4)
    (hfaithful : Function.Injective (MulDistribMulAction.toMulAut A Q)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : CFSG.Open.pRank p (⊤ : Subgroup A) ≤ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, -, hE, hcard⟩ := pRank_attained p hp (⊤ : Subgroup A)
  have : IsMulCommutative E := hE.1
  let : CommGroup E := IsMulCommutative.instCommGroup
  have hEp : IsPGroup p E := IsPGroup.of_card hcard
  have hfaithfulE : Function.Injective (MulDistribMulAction.toMulAut E Q) := by
    intro a b hab
    apply Subtype.ext
    apply hfaithful
    apply MulEquiv.ext
    intro q
    exact congrArg (fun f : MulAut Q => f q) hab
  have hcop : ¬ p ∣ Nat.card (frattini Q) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hQ.to_subgroup (frattini Q))
    rw [hk]
    intro hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  let : IsMulCommutative (Q ⧸ frattini Q) := pGroup_frattini_quotient_isMulCommutative 2 hQ
  let : CommGroup (Q ⧸ frattini Q) := IsMulCommutative.instCommGroup
  let := pGroup_binary_frattini_quotient_module hQ
  let := characteristic_quotient_mulDistribMulAction (acting := E) (frattini Q)
  have hfaithfulQ := faithful_coprime_pGroup_action_on_frattini_quotient p hEp hcop hfaithfulE
  have hbound := faithful_binary_elementary_linear_action_order_dimension_bound p _ hp2 hcard
    (fun a => Subtype.ext (hE.2 a a.2))
    (multiplicative_action_zmod_linear_aut (acting := E) (source := Q ⧸ frattini Q) 2)
    (faithful_multiplicative_action_zmod_linear_aut 2 hfaithfulQ)
  have hdim := twoGroup_frattini_finrank_eq_group_rank hQ
  have hord := binary_prime_order_at_least_two p hp2
  have hmul : 2 * CFSG.Open.pRank p (⊤ : Subgroup A) ≤
      orderOf (2 : ZMod p) * CFSG.Open.pRank p (⊤ : Subgroup A) := Nat.mul_le_mul_right _ hord
  omega

open CFSG.PreuniquenessRankFour.Helpers in
theorem two_mul_pRank_le_rank_pCoreOf {G : Type*} [Group G] [Finite G]
    (hchar : CFSG.Assembly.IsCharTwoType G) {H : Subgroup G} (hH : CFSG.Assembly.IsTwoLocal H)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    2 * CFSG.Assembly.pRank p H ≤ Group.rank (CFSG.Assembly.pCoreOf 2 H) := by
  let : IsMulCommutative (CFSG.Open.pCoreOf 2 H ⧸ frattini (CFSG.Open.pCoreOf 2 H)) :=
    pGroup_frattini_quotient_isMulCommutative 2 (pCoreOf_isPGroup 2 H)
  let : CommGroup (CFSG.Open.pCoreOf 2 H ⧸ frattini (CFSG.Open.pCoreOf 2 H)) :=
    IsMulCommutative.instCommGroup
  let := pGroup_binary_frattini_quotient_module (pCoreOf_isPGroup 2 H)
  have hdim := local_twoCore_frattini_dimension_bound p hp hp2 hchar H hH
  rw [twoGroup_frattini_finrank_eq_group_rank (pCoreOf_isPGroup 2 H)] at hdim
  exact hdim

open CFSG.PreuniquenessRankFour.Helpers in
theorem pRank_le_two_of_charTwoType_gen4 {G : Type*} [Group G] [Finite G]
    (hchar : CFSG.Assembly.IsCharTwoType G) (hgen : Gen4 G) {H : Subgroup G}
    (hH : CFSG.Assembly.IsTwoLocal H) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Assembly.pRank p H ≤ 2 := by
  have h2 := two_mul_pRank_le_rank_pCoreOf hchar hH hp hp2
  have h4 : Group.rank (CFSG.Assembly.pCoreOf 2 H) ≤ 4 :=
    hgen.rank_le_four (pCoreOf_isPGroup 2 H)
  omega

theorem evenRank_le_two_of_charTwoType_gen4 {G : Type*} [Group G] [Finite G]
    (hchar : CFSG.Assembly.IsCharTwoType G) (hgen : Gen4 G) : CFSG.Assembly.evenRank G ≤ 2 := by
  refine csSup_le' ?_
  rintro k ⟨p, H, hp, hp2, hH, rfl⟩
  exact pRank_le_two_of_charTwoType_gen4 hchar hgen hH hp hp2

theorem twoLocalOddRank_le_two_of_isCharacteristicPType_gen4 {G : Type*} [Group G] [Finite G]
    (hchar : CFSG.IsCharacteristicPType G 2) (hgen : Gen4 G) : CFSG.twoLocalOddRank G ≤ 2 := by
  refine csSup_le' ?_
  rintro r ⟨H, hH, p, hp, hp2, -, rfl⟩
  have hbridge : CFSG.pRank p H = CFSG.Open.pRank p H :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top p H).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup H).symm
  rw [hbridge]
  exact pRank_le_two_of_charTwoType_gen4 (isCharTwoType_iff.2 hchar) hgen hH hp hp2

private theorem oddCore_eq_pPrimeCore_two (X : Type*) [Group X] :
    CFSG.Assembly.oddCore X = pPrimeCore 2 X :=
  (ComponentClassification.AssemblyBPredicates.oddCore_eq_piCore X).trans
    (CFSG.pPrimeCore_eq_piCore X 2).symm

theorem not_isComponentType_of_layerBar_eq_bot {G : Type*} [Group G] [Finite G]
    (h : ∀ x : G, orderOf x = 2 → layerBar x = ⊥) : ¬ CFSG.Assembly.IsComponentType G := by
  rintro ⟨t, ht, L, hL⟩
  have hL' : CFSG.IsComponent L :=
    (ComponentClassification.AssemblyBPredicates.isComponentOf_top_iff_native L).1 hL
  let e := QuotientGroup.quotientMulEquivOfEq
    (oddCore_eq_pPrimeCore_two ↥(centralizer ({t} : Set G)))
  have hK : CFSG.IsComponent (L.map e.toMonoidHom) :=
    (LocalAnalysis.ComponentInitial.isComponent_map_iff e L).2 hL'
  have hle : L.map e.toMonoidHom ≤ layerBar t := LocalCores.component_le_layer hK
  rw [h t ht, le_bot_iff] at hle
  have hL0 : L = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective L (f := e.toMonoidHom) e.injective).1 hle
  have : Nontrivial L := LocalCores.isQuasisimple_nontrivial hL'.1
  exact (Subgroup.nontrivial_iff_ne_bot L).1 this hL0

theorem isComponentType_of_layerBar_ne_bot {G : Type*} [Group G] {t : G} (ht : orderOf t = 2)
    (hL : layerBar t ≠ ⊥) : CFSG.Assembly.IsComponentType G := by
  have hex : ∃ K : Subgroup (CentralizerBar t), CFSG.IsComponent K := by
    by_contra hno
    exact hL (LocalCores.layer_eq_bot_of_forall fun K hK => hno ⟨K, hK⟩)
  obtain ⟨K, hK⟩ := hex
  let e := QuotientGroup.quotientMulEquivOfEq
    (oddCore_eq_pPrimeCore_two ↥(centralizer ({t} : Set G))).symm
  exact ⟨t, ht, K.map e.toMonoidHom,
    (ComponentClassification.AssemblyBPredicates.isComponentOf_top_iff_native _).2
      ((LocalAnalysis.ComponentInitial.isComponent_map_iff e K).2 hK)⟩

theorem isComponentType_iff_exists_layerBar_ne_bot {G : Type*} [Group G] [Finite G] :
    CFSG.Assembly.IsComponentType G ↔ ∃ x : G, orderOf x = 2 ∧ layerBar x ≠ ⊥ := by
  constructor
  · intro hcomp
    by_contra hno
    push Not at hno
    exact not_isComponentType_of_layerBar_eq_bot hno hcomp
  · rintro ⟨x, hx, hL⟩
    exact isComponentType_of_layerBar_ne_bot hx hL

end CFSG.GH74
