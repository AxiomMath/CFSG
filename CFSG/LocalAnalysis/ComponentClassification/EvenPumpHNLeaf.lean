module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddLie
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEven
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpHNOrders
public import CFSG.Sporadic.HNSchreier.Order
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def IsHNType (K : Type) [Group K] : Prop :=
  Nonempty (K ≃* NativeSporadic.Carrier .HN)

@[expose] def HNNotProperFixedLeaf : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ x y : S, x * y ≠ y * x) →
    Blueprint.Catalog S → ∀ (σ : MulAut S) (P : Subgroup S), ProperFixedComponent σ P →
    ¬ IsHNType (↥P ⧸ Open.fusionZStar ↥P)

theorem card_carrier_HN :
    Nat.card (NativeSporadic.Carrier .HN) = 273030912000000 :=
  Sporadic.HNSchreier.card_HN

theorem card_of_isHNType
    {K : Type} [Group K] (h : IsHNType K) :
    Nat.card K = 273030912000000 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, card_carrier_HN]

theorem hn_dvd_and_double_le
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P)
    (hH : IsHNType (P ⧸ Open.fusionZStar P)) :
    273030912000000 ∣ Nat.card S ∧ 2 * 273030912000000 ≤ Nat.card S := by
  have hP : 273030912000000 ∣ Nat.card (fixedSubgroup σ) := by
    rw [← card_of_isHNType hH]
    exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le h.2.1)
  have hne : fixedSubgroup σ ≠ ⊤ := by
    intro htop
    apply h.ne_one
    refine MulEquiv.ext fun y => ?_
    have hy : σ y = y :=
      LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff.mp (htop ▸ mem_top y)
    simpa using hy
  have hidx : 2 ≤ (fixedSubgroup σ).index := by
    have h0 : (fixedSubgroup σ).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : (fixedSubgroup σ).index ≠ 1 := fun h1 => hne (Subgroup.index_eq_one.mp h1)
    omega
  have hmul := (fixedSubgroup σ).card_mul_index
  refine ⟨hP.trans ⟨_, hmul.symm⟩, ?_⟩
  obtain ⟨k, hk⟩ := hP
  have hpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [mul_zero] at hk
      exact absurd hk (Nat.card_pos (α := fixedSubgroup σ)).ne'
    · exact hk0
  calc 2 * 273030912000000 ≤ 2 * Nat.card (fixedSubgroup σ) := by
        rw [hk]
        exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hpos)
    _ ≤ (fixedSubgroup σ).index * Nat.card (fixedSubgroup σ) := Nat.mul_le_mul_right _ hidx
    _ = Nat.card S := by rw [mul_comm]; exact hmul

theorem not_isHNType_of_isAltType
    {K : Type} [Group K] (h : IsAltType K) : ¬ IsHNType K := by
  intro hH
  obtain ⟨Ω, _, _, hΩ, ⟨eA⟩⟩ := h
  have : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hcard := card_of_isHNType hH
  rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card] at hcard
  exact factorial_div_two_ne_HN _ hcard

theorem not_isHNType_of_properFixedComponent_alternating
    {S : Type} [Group S] [Finite S]
    {n : ℕ} (hn : 5 ≤ n) (θ : S ≃* alternatingGroup (Fin n)) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) : ¬ IsHNType (P ⧸ Open.fusionZStar P) := by
  by_cases hn6 : n = 6
  · subst hn6
    intro hH
    have h1 := card_dvd_of_fusionZStar_equiv (Equiv.refl (P ⧸ Open.fusionZStar P))
    rw [card_of_isHNType hH, Nat.card_congr θ.toEquiv, nat_card_alternatingGroup,
      Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    have h2 := Nat.le_of_dvd (by norm_num [Nat.factorial]) h1
    norm_num [Nat.factorial] at h2
  obtain ⟨h', ⟨e⟩⟩ := h.map θ
  exact not_isHNType_of_isAltType
    ((isAltType_of_properFixedComponent_alternating hn hn6 h').of_mulEquiv e)

theorem not_isHNType_of_properFixedComponent_oddLie
    (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput) {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) (hodd : OddLieType S)
    {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P) :
    ¬ IsHNType (P ⧸ Open.fusionZStar P) := by
  intro hH
  have hσ1 := h.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h.1 y
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  set L := P.subgroupOf (fixedSubgroup σ) with hLdef
  have hq : IsQuasisimple L :=
    fixedTwoComponentsQuasisimple_of_oddLieType hna hodd σ hσσ hσ1 L h.2.2.1
  obtain ⟨hcomp, ⟨eZ⟩⟩ := h.fusionZStar_equiv_of_quasisimple hq
  have hcard : Nat.card (L ⧸ center L) = 273030912000000 := by
    rw [← Nat.card_congr eZ.toEquiv, card_of_isHNType hH]
  obtain ⟨τ, n, p, f, hp, hp2, hadm, hm⟩ := hodd
  rcases hGLS S τ n p f hp hp2 hadm hm σ hσ2 L hcomp with ⟨τ', n', f', hadm', hm'⟩ |
      ⟨-, -, -, h8⟩
  · exact lieModel_card_ne_HN hO hadm' hm' hcard
  · have h504 := card_of_lieModel_psl_two_eight hO h8
    have hle : Nat.card (L ⧸ center L) ≤ 504 := by
      rw [← h504]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    rw [hcard] at hle
    norm_num at hle

theorem not_isHNType_of_properFixedComponent_evenLie
    (hEO : EvenLieOuterTwoComponentsInput) (hO : LieOrderFormulasInput) {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) (heven : EvenLieType S)
    {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P) :
    ¬ IsHNType (P ⧸ Open.fusionZStar P) ∨ TBLit.UList S := by
  have hσ1 := h.ne_one
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by
    rw [sq]; exact MulEquiv.ext fun y => h.1 y) hσ1
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout
  ·
    obtain ⟨ht2, -, hPc, -⟩ := h.inner hna ht
    rcases oddCore_eq_bot_or_uList_of_evenLieType hna heven ht2 with hcore | hU
    · refine .inl fun _ => ?_
      have hq := Sporadic.HeldB.pComponent_quasisimple_of_oddCore_eq_bot hcore _ hPc
      exact involutionCentralizersComponentFree_of_evenLieType heven t ht2 _
        ⟨hq, hPc.choose_spec.2.1⟩
    · exact .inr hU
  ·
    refine .inl ?_
    intro hH
    obtain ⟨τ, n, f, hadm, hm⟩ := heven
    obtain ⟨eL⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe h.2.1)
    have hcard : Nat.card ((P.subgroupOf (fixedSubgroup σ)) ⧸
        Open.fusionZStar (P.subgroupOf (fixedSubgroup σ))) = 273030912000000 := by
      rw [Nat.card_congr eL.toEquiv, card_of_isHNType hH]
    rcases hEO S τ n f hadm hm σ hσ2 hout _ h.2.2.1 with ⟨τ', n', f', hadm', hm'⟩ | hA | hU
    · exact lieModel_card_ne_HN hO hadm' hm' hcard
    · obtain ⟨eA⟩ := hA
      rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hcard
      norm_num [Nat.factorial] at hcard
    · have hadm3 : StatedLieAdmissible .PSU 3 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
      exact lieModel_card_ne_HN hO hadm3 hU hcard

theorem not_isHNType_of_properFixedComponent_held
    {S : Type} [Group S] [Finite S] (eS : S ≃* NativeSporadic.He) {σ : MulAut S}
    {P : Subgroup S} (_h : ProperFixedComponent σ P) : ¬ IsHNType (P ⧸ Open.fusionZStar P) := by
  intro hH
  have h1 := card_dvd_of_fusionZStar_equiv (Equiv.refl (P ⧸ Open.fusionZStar P))
  rw [card_of_isHNType hH, Nat.card_congr eS.toEquiv, Sporadic.He.card_He] at h1
  norm_num at h1

end CFSG.ComponentClassification.EvenPump
