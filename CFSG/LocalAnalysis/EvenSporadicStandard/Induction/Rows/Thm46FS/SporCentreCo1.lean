module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.SporCentreBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1PairK
public import CFSG.Sporadic.Co1Block.Thirteen

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.SporCentre

open CFSG CFSG.LocalCores CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier Subgroup

theorem index_subgroupOf_le {G : Type*} [Group G] [Finite G] (K D : Subgroup G) :
    (K.subgroupOf D).index ≤ K.index := by
  have h : K.relIndex ⊤ ≠ 0 := by
    rw [relIndex_top_right]
    exact Subgroup.index_ne_zero_of_finite
  have := Subgroup.relIndex_le_of_le_right (H := K) (K := D) (L := ⊤) le_top h
  rwa [relIndex_top_right] at this

theorem center_eq_bot_of_component_C₁
    {B : Subgroup C₁}
    (hB : IsComponent B) : center B = ⊥ := by
  obtain ⟨K, -, hK⟩ := EvenSporadicStandard.Co1Pair.exists_perfect_K₁
  have hC : Nat.card C₁ = 2012774400 := card_cent_a₁
  have hidx : K.index = 8 := by
    have h := K.card_mul_index
    rw [hK, hC] at h
    omega
  have hcard : Nat.card (B ⧸ center B) = 251596800 := card_quotient_center_a₁ B hB
  have hbig : Nat.factorial 8 < Nat.card (B ⧸ center B) := by
    rw [hcard]
    decide
  have htop : K.subgroupOf B = ⊤ :=
    eq_top_of_index_le hB.1.1 hB.1.2.1 hbig ((index_subgroupOf_le K B).trans hidx.le)
  have hBK : B ≤ K := Subgroup.subgroupOf_eq_top.1 htop
  have hle : Nat.card B ≤ 251596800 := hK ▸ Subgroup.card_le_of_le hBK
  have h1 := (center B).card_mul_index
  have h2 : (center B).index = 251596800 := hcard
  rw [h2] at h1
  have h3 : 0 < Nat.card (center B) := Nat.card_pos
  have h4 : Nat.card (center B) = 1 := by nlinarith
  exact Subgroup.eq_bot_of_card_eq _ h4

theorem forall_center_eq_bot_of_mulEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K)
    (h : ∀ B : Subgroup H, IsComponent B → center B = ⊥) :
    ∀ B : Subgroup K, IsComponent B → center B = ⊥ := by
  intro B hB
  have h0 := h _ (isComponent_map_mulEquiv e.symm hB)
  have hc := Nat.card_congr (Subgroup.centerCongr
    (B.equivMapOfInjective e.symm.toMonoidHom e.symm.injective)).toEquiv
  rw [h0, Subgroup.card_bot] at hc
  exact Subgroup.eq_bot_of_card_eq _ hc

theorem forall_center_eq_bot_of_isConj {G : Type*} [Group G] {a t : G} (h : IsConj a t)
    (ha : ∀ B : Subgroup (centralizer ({a} : Set G)), IsComponent B → center B = ⊥) :
    ∀ B : Subgroup (centralizer ({t} : Set G)), IsComponent B → center B = ⊥ := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 h
  exact forall_center_eq_bot_of_mulEquiv (centralizerConjEquiv g a) ha

theorem center_eq_bot_of_forall_component {S G : Type*} [Group S] [Group G] (f : S ≃* G) {t : S}
    (h : ∀ B : Subgroup (centralizer ({f t} : Set G)), IsComponent B → center B = ⊥)
    {Q : Subgroup S} (hQC : Q ≤ centralizer ({t} : Set S))
    (hQ : IsComponent (Q.subgroupOf (centralizer ({t} : Set S)))) : center Q = ⊥ := by
  have h0 := h _ (isComponent_map_mulEquiv (centralizerMulEquiv f t) hQ)
  obtain ⟨c⟩ := nonempty_center_equiv_map (centralizerMulEquiv f t) hQC
  have hc := Nat.card_congr c.toEquiv
  rw [h0, Subgroup.card_bot] at hc
  exact Subgroup.eq_bot_of_card_eq _ hc

section GA


theorem center_eq_bot_of_component_GA {s : GA} (hs : orderOf s = 2)
    {B : Subgroup (centralizer ({s} : Set GA))} (hB : IsComponent B) : center B = ⊥ := by
  rcases ncard_fix_cases hs with h | h | h
  · obtain ⟨-, -, -, -, hno⟩ := cti_co1_2280_fixed_point_centralizer_has_no_components hs h
    exact absurd hB (hno B)
  · obtain ⟨-, -, -, -, -, hno⟩ := cti_co1_264_fixed_point_centralizer_has_no_components hs h
    exact absurd hB (hno B)
  · exact forall_center_eq_bot_of_isConj (isConj_a₁_of_ncard_fix hs h).symm
      (fun B' hB' => center_eq_bot_of_component_C₁ hB') B hB

theorem center_eq_bot_of_component_co1 {S : Type*} [Group S]
    (e : S ≃* Blueprint.NativeSporadic.Co1) {t : S} (ht : orderOf t = 2) {Q : Subgroup S}
    (hQC : Q ≤ centralizer ({t} : Set S))
    (hQ : IsComponent (Q.subgroupOf (centralizer ({t} : Set S)))) : center Q = ⊥ := by
  let f := mulEquivOfFun (H := S) (K := GA) (fun s => co1MatEquiv (e s))
    (fun g => e.symm (co1MatEquiv.symm g)) (fun s => by simp only [MulEquiv.symm_apply_apply])
    (fun g => by simp only [MulEquiv.apply_symm_apply]) (fun a b => by rw [map_mul, map_mul])
  have het : orderOf (e t) = orderOf t := by
    rw [orderOf_eq_orderOf_iff]
    intro n
    rw [← map_pow, ← map_one e, e.injective.eq_iff]
  have hft : orderOf (f t) = 2 := by
    show orderOf (co1MatEquiv (e t)) = 2
    rw [orderOf_co1MatEquiv, het, ht]
  exact center_eq_bot_of_forall_component f (fun B hB => center_eq_bot_of_component_GA hft hB)
    hQC hQ

end GA

end CFSG.EvenSporadicStandard.Induction.SporCentre
