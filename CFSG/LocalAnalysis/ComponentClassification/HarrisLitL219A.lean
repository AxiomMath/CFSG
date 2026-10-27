module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTwoComp
public import CFSG.GroupTheory.ConjugatePairSubnormality
public import CFSG.GH74.GLS.TwoThin.Struct

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.GH74.GLS.TwoThin CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace L219

section General

variable {G : Type*} [Group G] [Finite G]

theorem isTwoComponent_iff_twoComponents (J : Subgroup G) :
    IsTwoComponent J ↔ TwoComponents.IsTwoComponent J := by
  rw [isTwoComponent_iff_isPComponent, CatalogueBAlternating.pComponent_two_iff]

theorem isTwoComponentIn_iff_twoComponents {J A : Subgroup G} :
    IsTwoComponentIn J A ↔ J ≤ A ∧ TwoComponents.IsTwoComponent (J.subgroupOf A) := by
  constructor
  · intro h
    exact ⟨h.1, (CatalogueBAlternating.pComponent_two_iff _).mp
      ((HarrisLit.isTwoComponentIn_iff h.1).mp h)⟩
  · rintro ⟨hJA, h⟩
    exact (HarrisLit.isTwoComponentIn_iff hJA).mpr
      ((CatalogueBAlternating.pComponent_two_iff _).mpr h)

theorem twoLayer_eq : twoLayer G = TwoLayer.subgroup G := by
  unfold twoLayer TwoLayer.subgroup
  congr 1
  ext J
  exact isTwoComponent_iff_twoComponents J

theorem le_of_le_sup_of_odd {P X N : Subgroup G} (hP : Group.IsPerfect ↥P)
    (hN : Odd (Nat.card ↥N)) (hNX : N ≤ normalizer (X : Set G)) (hPX : P ≤ X ⊔ N) : P ≤ X := by
  have : Group.IsSolvable ↥N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hN
  have : (X.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hNX
  have : (X.subgroupOf (N ⊔ X)).Normal := normal_subgroupOf_sup_of_le_normalizer hNX
  have hsol : Group.IsSolvable (↥(N ⊔ X) ⧸ X.subgroupOf (N ⊔ X)) :=
    Group.isSolvable_of_surjective
      (f := (QuotientGroup.quotientInfEquivProdNormalizerQuotient N X hNX).toMonoidHom)
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient N X hNX).surjective
  have hPX' : P ≤ N ⊔ X := hPX.trans (sup_comm X N).le
  have hf := SolvableKernelContainment.hom_eq_one
    ((QuotientGroup.mk' (X.subgroupOf (N ⊔ X))).comp (Subgroup.inclusion hPX'))
  intro p hp
  have h1 := DFunLike.congr_fun hf ⟨p, hp⟩
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, MonoidHom.one_apply,
    QuotientGroup.eq_one_iff] at h1
  exact h1

theorem not_le_of_odd {P N : Subgroup G} [Nontrivial ↥P] (hP : Group.IsPerfect ↥P)
    (hN : Odd (Nat.card ↥N)) : ¬ P ≤ N := by
  intro hPN
  have : Group.IsSolvable ↥P :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (hN.of_dvd_nat (Subgroup.card_dvd_of_le hPN))
  exact Group.IsPerfect.not_isSolvable ↥P ‹_›

theorem not_le_of_odd_of_twoComponent {K N : Subgroup G} (hK : TwoComponents.IsTwoComponent K)
    (hN : Odd (Nat.card ↥N)) : ¬ K ≤ N := by
  have : Nontrivial ↥K := TwoComponents.nontrivial hK
  exact not_le_of_odd ⟨TwoComponents.perfect hK⟩ hN

theorem pPrimeCore_le_normalizer {K : Subgroup G} (hK : TwoComponents.IsTwoComponent K) :
    pPrimeCore 2 G ≤ normalizer (K : Set G) := by
  have hS := Components.chain_of_mathlib_subnormal
    (pPrimeCore_normal (p := 2) (G := G)).isSubnormal
  rcases TwoComponentSubnormal.contains_or_normalizes_core K _ hK hS with h | h
  · exact absurd h (not_le_of_odd_of_twoComponent hK (odd_card_pPrimeCore G))
  · exact h.1

theorem twoLayer_le_normalizer {K : Subgroup G} (hK : TwoComponents.IsTwoComponent K) :
    TwoLayer.subgroup G ≤ normalizer (K : Set G) := by
  unfold TwoLayer.subgroup
  refine sSup_le fun K' hK' => ?_
  rcases TwoComponentSubnormal.contains_or_normalizes_core K K' hK hK'.1 with h | h
  · rw [← TwoComponentSubnormal.eq_of_le K K' hK hK' h]
    exact le_normalizer
  · exact h.1

omit [Finite G] in
theorem le_normalizer_sup {N A B : Subgroup G} (hA : N ≤ normalizer (A : Set G))
    (hB : N ≤ normalizer (B : Set G)) : N ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    mem_normalizer_iff_map_conj_eq.mp (hA hg), mem_normalizer_iff_map_conj_eq.mp (hB hg)]

omit [Finite G] in
theorem conj_mem_commutator {A B : Subgroup G} {b x : G} (hb : b ∈ B) (hx : x ∈ ⁅A, B⁆) :
    b * x * b⁻¹ ∈ ⁅A, B⁆ := by
  have h : ⁅A, B⁆ ≤ ⁅A, B⁆.comap (MulAut.conj b).toMonoidHom := by
    rw [commutator_le]
    intro a ha c hc
    rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have : b * ⁅a, c⁆ * b⁻¹ = ⁅a, b⁆⁻¹ * ⁅a, b * c⁆ := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact mul_mem (inv_mem (commutator_mem_commutator ha hb))
      (commutator_mem_commutator ha (mul_mem hb hc))
  exact h hx

omit [Finite G] in
theorem le_normalizer_commutator (A B : Subgroup G) :
    B ≤ normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  intro b hb
  rw [mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_commutator hb, fun h => ?_⟩
  have := conj_mem_commutator (inv_mem hb) h
  rwa [show b⁻¹ * (b * x * b⁻¹) * b⁻¹⁻¹ = x by group] at this

omit [Finite G] in
theorem isTwoComponent_map_conj {K : Subgroup G} (hK : IsTwoComponent K) (g : G) :
    IsTwoComponent (K.map (MulAut.conj g).toMonoidHom) :=
  ⟨hK.1.map (MulAut.conj g).surjective,
    isTwoQuasisimple_of_mulEquiv (K.equivMapOfInjective _ (MulAut.conj g).injective) hK.2⟩

theorem twoComponent_map_conj {K : Subgroup G} (hK : TwoComponents.IsTwoComponent K) (g : G) :
    TwoComponents.IsTwoComponent (K.map (MulAut.conj g).toMonoidHom) :=
  (isTwoComponent_iff_twoComponents _).mp
    (isTwoComponent_map_conj ((isTwoComponent_iff_twoComponents K).mpr hK) g)

omit [Finite G] in
theorem isSubnormal_subgroupOf_of_le {J A B : Subgroup G} (hAB : A ≤ B)
    (hJ : (J.subgroupOf B).IsSubnormal) : (J.subgroupOf A).IsSubnormal :=
  (CFSG.GroupTheory.isSubnormal_subgroupOf_subgroupOf_iff hAB).mp hJ.subgroupOf

omit [Finite G] in
theorem part_a {z : G} {L : Subgroup G} (hL : L.IsSubnormal) {J : Subgroup G}
    (hJ : IsTwoComponentIn J (L ⊓ centralizer {z})) : IsTwoComponentIn J (centralizer {z}) := by
  obtain ⟨hJLH, hJsub, hJq⟩ := hJ
  refine ⟨hJLH.trans inf_le_right, ?_, hJq⟩
  have hLH : ((L ⊓ centralizer {z}).subgroupOf (centralizer {z})).IsSubnormal := by
    rw [inf_subgroupOf_right]
    exact hL.subgroupOf
  exact CFSG.GroupTheory.isSubnormal_subgroupOf_trans hJLH inf_le_right hJsub hLH

end General

section Bar

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_barMk_map_conj (K : Subgroup G) (g : G) :
    (K.map (MulAut.conj g).toMonoidHom).map (barMk G) =
      (K.map (barMk G)).map (MulAut.conj (barMk G g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem le_of_map_barMk_le {P X : Subgroup G} (hP : Group.IsPerfect ↥P)
    (hX : pPrimeCore 2 G ≤ normalizer (X : Set G)) (h : P.map (barMk G) ≤ X.map (barMk G)) :
    P ≤ X := by
  refine le_of_le_sup_of_odd hP (odd_card_pPrimeCore G) hX ?_
  have h' := Subgroup.map_le_iff_le_comap.mp h
  rwa [Subgroup.comap_map_eq, ker_barMk] at h'

theorem le_of_map_barMk_le_of_le_normalizer {P X : Subgroup G} (hP : Group.IsPerfect ↥P)
    (hPX : P ≤ normalizer (X : Set G)) (h : P.map (barMk G) ≤ X.map (barMk G)) : P ≤ X := by
  refine le_of_le_sup_of_odd (N := pPrimeCore 2 G ⊓ normalizer (X : Set G)) hP
    ((odd_card_pPrimeCore G).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)) inf_le_right ?_
  intro p hp
  obtain ⟨x, hx, hxp⟩ := h ⟨p, hp, rfl⟩
  have hk : x⁻¹ * p ∈ pPrimeCore 2 G := by
    rw [← ker_barMk, MonoidHom.mem_ker, map_mul, map_inv, hxp, inv_mul_cancel]
  have hn : x⁻¹ * p ∈ normalizer (X : Set G) := mul_mem (inv_mem (le_normalizer hx)) (hPX hp)
  have : p = x * (x⁻¹ * p) := by group
  rw [this]
  exact mul_mem (mem_sup_left hx) (mem_sup_right ⟨hk, hn⟩)

end Bar

end L219

end CFSG.ComponentClassification.HarrisLit
