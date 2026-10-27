module

public import CFSG.ClassicalInvolution.Balance.PassTwoLie
public import CFSG.ClassicalInvolution.Generic.Generation.Defs

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

@[expose] def memberImages {G : Type} [Group G] (Ω : Set (Subgroup G)) (a : G) :
    Set (Subgroup (OddQuot a)) :=
  (fun K => modOdd a K) '' centMembers Ω a

@[expose] def memberJoin {G : Type} [Group G] (Ω : Set (Subgroup G)) (a : G) :
    Subgroup (OddQuot a) :=
  ⨆ K ∈ centMembers Ω a, modOdd a K

section Embedding

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {a : G}

omit [Finite G] in
theorem centLayer_le_centralizer (Ω : Set (Subgroup G)) (a : G) :
    centLayer Ω a ≤ Subgroup.centralizer ({a} : Set G) :=
  centLayer_le fun _ hL => hL.2

omit [Finite G] in
theorem mem_normalizer_centLayer (hΩ : ConjInvariant Ω) {c : G}
    (hc : c ∈ Subgroup.centralizer ({a} : Set G)) : c ∈ Subgroup.normalizer
      ((centLayer Ω a : Subgroup G) : Set G) := by
  have hca : c * a * c⁻¹ = a := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    rw [this]
    group
  have h := conjSub_centLayer hΩ c a
  rw [hca] at h
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact h

@[expose] def layerToOddQuot (Ω : Set (Subgroup G)) (a : G) : ↥(centLayer Ω a) →* OddQuot a :=
  (oddQuotMk a).comp (Subgroup.inclusion (centLayer_le_centralizer Ω a))

omit [Finite G] in
theorem layerToOddQuot_apply (y : ↥(centLayer Ω a)) :
    layerToOddQuot Ω a y = oddQuotMk a ⟨y, centLayer_le_centralizer Ω a y.2⟩ := rfl

theorem map_inclusion_oddCore_le (hΩ : ConjInvariant Ω) :
    (componentClassificationOddCore ↥(centLayer Ω a)).map
        (Subgroup.inclusion (centLayer_le_centralizer Ω a)) ≤
      componentClassificationOddCore ↥(Subgroup.centralizer ({a} : Set G)) := by
  have hYC : centLayer Ω a ≤ Subgroup.centralizer ({a} : Set G) := centLayer_le_centralizer Ω a
  set φ : ↥(centLayer Ω a) →* ↥(Subgroup.centralizer ({a} : Set G)) :=
    Subgroup.inclusion hYC with hφ
  have hinj : Function.Injective φ := Subgroup.inclusion_injective hYC
  refine OddCore.maximal _ _ ?_ ?_
  · refine ⟨fun n hn c => ?_⟩
    obtain ⟨d', hd', rfl⟩ := hn
    have hc : (c : G) ∈ Subgroup.normalizer ((centLayer Ω a : Subgroup G) : Set G) :=
      mem_normalizer_centLayer hΩ c.2
    have hmem : conjOn (centLayer Ω a) c hc d' ∈ componentClassificationOddCore
        ↥(centLayer Ω a) := by
      have := OddCore.char_invariant (conjOn (centLayer Ω a) c hc)
      rw [← this]
      exact ⟨d', hd', rfl⟩
    refine ⟨conjOn (centLayer Ω a) c hc d', hmem, ?_⟩
    apply Subtype.ext
    simp [φ, conjOn_apply]
  · have hcard : Nat.card ((componentClassificationOddCore ↥(centLayer Ω a)).map φ) =
        Nat.card (componentClassificationOddCore ↥(centLayer Ω a)) :=
      Nat.card_congr
        ((componentClassificationOddCore ↥(centLayer Ω a)).equivMapOfInjective φ hinj).toEquiv.symm
    rw [hcard]
    exact OddCore.odd_card _

theorem ker_layerToOddQuot (hΩ : ConjInvariant Ω) :
    (layerToOddQuot Ω a).ker = classicalInvolutionOddCore ↥(centLayer Ω a) := by
  show (layerToOddQuot Ω a).ker = componentClassificationOddCore ↥(centLayer Ω a)
  have hYC : centLayer Ω a ≤ Subgroup.centralizer ({a} : Set G) := centLayer_le_centralizer Ω a
  set φ : ↥(centLayer Ω a) →* ↥(Subgroup.centralizer ({a} : Set G)) :=
    Subgroup.inclusion hYC with hφ
  have hinj : Function.Injective φ := Subgroup.inclusion_injective hYC
  apply le_antisymm
  · refine OddCore.maximal _ _ (MonoidHom.normal_ker _) ?_
    have hle : (layerToOddQuot Ω a).ker.map φ ≤
        componentClassificationOddCore ↥(Subgroup.centralizer ({a} : Set G)) := by
      rintro _ ⟨x, hx, rfl⟩
      exact oddQuotMk_eq_one_iff.mp hx
    have hcard : Nat.card (layerToOddQuot Ω a).ker = Nat.card ((layerToOddQuot Ω a).ker.map φ) :=
      Nat.card_congr ((layerToOddQuot Ω a).ker.equivMapOfInjective φ hinj).toEquiv
    rw [hcard]
    exact (OddCore.odd_card _).of_dvd_nat (Subgroup.card_dvd_of_le hle)
  · intro d hd
    rw [MonoidHom.mem_ker, layerToOddQuot_apply]
    exact oddQuotMk_eq_one_iff.mpr (map_inclusion_oddCore_le hΩ ⟨d, hd, rfl⟩)

omit [Finite G] in
theorem le_centLayer_of_mem {K : Subgroup G} (hK : K ∈ centMembers Ω a) : K ≤ centLayer Ω a :=
  le_centLayer hK

@[expose] noncomputable def layerQuotientHom (hΩ : ConjInvariant Ω) (a : G) :
    (↥(centLayer Ω a) ⧸ classicalInvolutionOddCore ↥(centLayer Ω a)) →* OddQuot a :=
  QuotientGroup.lift _ (layerToOddQuot Ω a) (ker_layerToOddQuot hΩ).ge

theorem layerQuotientHom_mk (hΩ : ConjInvariant Ω) (y : ↥(centLayer Ω a)) :
    layerQuotientHom hΩ a (QuotientGroup.mk' _ y) = layerToOddQuot Ω a y := rfl

theorem layerQuotientHom_injective (hΩ : ConjInvariant Ω) :
    Function.Injective (layerQuotientHom hΩ a) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ x
  rw [layerQuotientHom_mk] at hx
  have hy : y ∈ classicalInvolutionOddCore ↥(centLayer Ω a) := by
    rw [← ker_layerToOddQuot hΩ]
    exact hx
  exact (QuotientGroup.eq_one_iff y).mpr hy

omit [Finite G] in
theorem range_layerToOddQuot_eq (Ω : Set (Subgroup G)) (a : G) :
    (layerToOddQuot Ω a).range = memberJoin Ω a := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    have hle : centLayer Ω a ≤ ((memberJoin Ω a).comap (oddQuotMk a)).map
        (Subgroup.centralizer ({a} : Set G)).subtype := by
      refine centLayer_le fun L hL l hl => ?_
      refine ⟨⟨l, hL.2 hl⟩, ?_, rfl⟩
      exact le_iSup₂ (f := fun (K : Subgroup G) (_ : K ∈ centMembers Ω a) => modOdd a K) L hL
        (oddQuotMk_mem_modOdd hl (hL.2 hl))
    obtain ⟨c, hc, hcy⟩ := hle y.2
    have : (⟨y, centLayer_le_centralizer Ω a y.2⟩ : ↥(Subgroup.centralizer ({a} : Set G))) = c :=
      Subtype.ext hcy.symm
    rw [layerToOddQuot_apply, this]
    exact hc
  · refine iSup₂_le fun K hK => ?_
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨⟨k, le_centLayer hK hk⟩, rfl⟩

omit [Finite G] in
theorem memberJoin_normal (hΩ : ConjInvariant Ω) : (memberJoin Ω a).Normal := by
  rw [← range_layerToOddQuot_eq]
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨y, rfl⟩ := hn
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have hc : (c : G) ∈ Subgroup.normalizer ((centLayer Ω a : Subgroup G) : Set G) :=
    mem_normalizer_centLayer hΩ c.2
  refine ⟨conjOn (centLayer Ω a) c hc y, ?_⟩
  have : (⟨((conjOn (centLayer Ω a) c hc y : ↥(centLayer Ω a)) : G),
      centLayer_le_centralizer Ω a (conjOn (centLayer Ω a) c hc y).2⟩ :
        ↥(Subgroup.centralizer ({a} : Set G))) =
      c * ⟨y, centLayer_le_centralizer Ω a y.2⟩ * c⁻¹ :=
    Subtype.ext (conjOn_apply (centLayer Ω a) (c : G) hc y)
  rw [layerToOddQuot_apply, layerToOddQuot_apply, this]
  simp [oddQuotMk]

omit [Finite G] in
theorem map_layerToOddQuot_subgroupOf {K : Subgroup G} (hKY : K ≤ centLayer Ω a) :
    (K.subgroupOf (centLayer Ω a)).map (layerToOddQuot Ω a) = modOdd a K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, centLayer_le_centralizer Ω a y.2⟩, hy, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hKY hk⟩, hk, rfl⟩

theorem range_layerQuotientHom (hΩ : ConjInvariant Ω) :
    (layerQuotientHom hΩ a).range = memberJoin Ω a := by
  rw [← range_layerToOddQuot_eq]
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨QuotientGroup.mk' _ y, rfl⟩

end Embedding

section Family

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {a : G}

theorem map_layerQuotientHom_family (hΩ : ConjInvariant Ω) :
    (fun M => M.map (layerQuotientHom hΩ a)) ''
      oddQuotientFamily (restrictFamily (centMembers Ω a) (centLayer Ω a)) =
      memberImages Ω a := by
  ext M
  constructor
  · rintro ⟨_, ⟨_, ⟨K, hK, hKY, rfl⟩, rfl⟩, rfl⟩
    refine ⟨K, hK, ?_⟩
    show modOdd a K = ((K.subgroupOf (centLayer Ω a)).map _).map (layerQuotientHom hΩ a)
    rw [Subgroup.map_map]
    exact (map_layerToOddQuot_subgroupOf hKY).symm
  · rintro ⟨K, hK, rfl⟩
    refine ⟨_, ⟨K.subgroupOf (centLayer Ω a), ⟨K, hK, le_centLayer hK, rfl⟩, rfl⟩, ?_⟩
    show ((K.subgroupOf (centLayer Ω a)).map _).map (layerQuotientHom hΩ a) = modOdd a K
    rw [Subgroup.map_map]
    exact map_layerToOddQuot_subgroupOf (le_centLayer hK)

theorem not_le_center_of_mem (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ centMembers Ω a) :
    ¬ (K.subgroupOf (centLayer Ω a)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(centLayer Ω a))) ≤
      Subgroup.center (↥(centLayer Ω a) ⧸ classicalInvolutionOddCore ↥(centLayer Ω a)) := by
  intro hle
  obtain ⟨z, hz⟩ := hΩ.classical K hK.1
  set Y := centLayer Ω a with hY
  set O := classicalInvolutionOddCore ↥Y with hO
  have hKY : K ≤ Y := le_centLayer hK
  have hcomm : ⁅K.subgroupOf Y, K.subgroupOf Y⁆ ≤ O := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have h1 := hle ⟨x, hx, rfl⟩
    have h2 := Subgroup.mem_center_iff.mp h1 (QuotientGroup.mk' O y)
    have h3 : ⁅QuotientGroup.mk' O x, QuotientGroup.mk' O y⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr h2.symm
    rw [← map_commutatorElement] at h3
    exact (QuotientGroup.eq_one_iff _).mp h3
  have hperf : ⁅K.subgroupOf Y, K.subgroupOf Y⁆ = K.subgroupOf Y := by
    have := hz.perfect
    have : Group.IsPerfect ↥(K.subgroupOf Y) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKY).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hKY).symm.surjective
    exact Subgroup.commutator_eq_self
  have hK'O : K.subgroupOf Y ≤ O := hperf ▸ hcomm
  have hOodd : Odd (Nat.card O) := OddCore.odd_card ↥Y
  have hodd : Odd (Nat.card (K.subgroupOf Y)) :=
    hOodd.of_dvd_nat (Subgroup.card_dvd_of_le hK'O)
  have hzmem : (⟨z, hKY hz.mem⟩ : ↥Y) ∈ K.subgroupOf Y := hz.mem
  have hdvd : orderOf (⟨z, hKY hz.mem⟩ : ↥Y) ∣ Nat.card (K.subgroupOf Y) :=
    Subgroup.orderOf_dvd_natCard (K.subgroupOf Y) hzmem
  rw [Subgroup.orderOf_mk, hz.orderOf_eq_two] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

end Family

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem lieDecomposition_memberImages (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) {a : G}
    (ha : ¬ ({a} : Set G) ⊆ Subgroup.center G) :
    Nonempty (LieDecomposition (memberImages Ω a) (memberJoin Ω a)) := by
  obtain ⟨D⟩ := hIH {a} ha
  have hθ := layerQuotientHom_injective (a := a) hΩ.conjInvariant
  have h := lieDecomposition_of_lieSystemData hp2 h0 hA1 D (layerQuotientHom hΩ.conjInvariant a) hθ
    (by
      rintro _ ⟨_, ⟨K, hK, hKY, rfl⟩, rfl⟩
      exact not_le_center_of_mem hΩ hK)
  have hΨ : Subgroup.map (layerQuotientHom hΩ.conjInvariant a) ''
      oddQuotientFamily (restrictFamily (centralizingMembers Ω {a}) (centralizingLayer Ω {a})) =
      memberImages Ω a := map_layerQuotientHom_family hΩ.conjInvariant
  exact LieDecomposition.congr hΨ (range_layerQuotientHom hΩ.conjInvariant) h

end Main

end CFSG.ClassicalInvolution.Balance
