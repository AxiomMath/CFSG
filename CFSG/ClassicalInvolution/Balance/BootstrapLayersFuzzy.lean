module

public import CFSG.ClassicalInvolution.Balance.FuzzyAdjAxis
public import CFSG.ClassicalInvolution.LBalance.Main

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf finite_perfectResidualOf_isPerfect
  perfectResidualOf_normalizer_contains)
open scoped commutatorElement MatrixGroups

section SectionMember

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

structure IsSectionMember (p f : ℕ) [Fact p.Prime] (Y K : Subgroup G) (z : G) : Prop where
  le : K ≤ Y
  orderOf_eq_two : orderOf z = 2
  mem : z ∈ K
  perfect : Group.IsPerfect ↥K
  subnormal : IsSubnormal K (Subgroup.centralizer ({z} : Set G) ⊓ Y)
  nonempty_equiv : Nonempty (↥K ⧸ classicalInvolutionOddCore ↥K ≃* SL(2, GaloisField p f))

namespace IsSectionMember

variable {Y K : Subgroup G} {z : G}

theorem sq (h : IsSectionMember p f Y K z) : z * z = 1 := by
  rw [← pow_two, ← h.orderOf_eq_two]
  exact pow_orderOf_eq_one z

theorem central (h : IsSectionMember p f Y K z) {k : G} (hk : k ∈ K) : k * z = z * k :=
  Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le h.subnormal hk).1

theorem isCentralInvolution (h : IsSectionMember p f Y K z) : IsCentralInvolution K z where
  mem := h.mem
  ne_one := by
    intro h1
    have := h.orderOf_eq_two
    rw [h1, orderOf_one] at this
    omega
  sq := h.sq
  central := fun k hk => (h.central hk).symm

theorem restrict (h : IsSectionMember p f Y K z) {H : Subgroup G} (hHY : H ≤ Y) (hKH : K ≤ H) :
    IsSectionMember p f H K z :=
  { h with
    le := hKH
    subnormal := by
      have h1 := isSubnormal_inf h.subnormal H
      rwa [inf_eq_left.mpr hKH, inf_assoc, inf_eq_right.mpr hHY] at h1 }

theorem conj (h : IsSectionMember p f Y K z) {n : G} (hn : n ∈ Y) :
    IsSectionMember p f Y (conjSub n K) (n * z * n⁻¹) where
  le := by
    have := conjSub_mono (n := n) h.le
    rwa [conjSub_eq_self_of_mem hn] at this
  orderOf_eq_two := by
    have := orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective z
    simpa [h.orderOf_eq_two] using this
  mem := conj_mem_conjSub h.mem
  perfect := by
    have := h.perfect
    let ε : ↥K ≃* ↥(conjSub n K) :=
      Subgroup.equivMapOfInjective K (MulAut.conj n).toMonoidHom (MulAut.conj n).injective
    exact Group.IsPerfect.ofSurjective (f := ε.toMonoidHom) ε.surjective
  subnormal := by
    have h1 := isSubnormal_map_conj h.subnormal n
    have h2 : (Subgroup.centralizer ({z} : Set G) ⊓ Y).map (MulAut.conj n).toMonoidHom =
        Subgroup.centralizer ({n * z * n⁻¹} : Set G) ⊓ Y := by
      rw [Subgroup.map_inf_eq _ _ (MulAut.conj n).toMonoidHom (MulAut.conj n).injective]
      rw [← conjSub_centralizer_singleton n z]
      show conjSub n (Subgroup.centralizer ({z} : Set G)) ⊓ conjSub n Y = _
      rw [conjSub_eq_self_of_mem hn]
    exact h2 ▸ h1
  nonempty_equiv := by
    obtain ⟨e'⟩ := h.nonempty_equiv
    let ε : ↥K ≃* ↥(conjSub n K) :=
      Subgroup.equivMapOfInjective K (MulAut.conj n).toMonoidHom (MulAut.conj n).injective
    exact ⟨(QuotientGroup.congr _ _ ε.symm
      (CFSG.ComponentClassification.OddCore.equiv_invariant ε.symm)).trans e'⟩

theorem toIn (h : IsSectionMember p f Y K z) : IsClassicalMemberIn p f Y K z := by
  have hzY : z ∈ Y := h.le h.mem
  have e : K.subgroupOf Y ≃* K := Subgroup.subgroupOfEquivOfLe h.le
  refine ⟨hzY, ?_, Subgroup.mem_subgroupOf.mpr h.mem, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]
    exact h.orderOf_eq_two
  · have := h.perfect
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · have h2 : (Subgroup.centralizer ({z} : Set G) ⊓ Y).subgroupOf Y =
        Subgroup.centralizer ({(⟨z, hzY⟩ : Y)} : Set Y) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
        Set.mem_singleton_iff, forall_eq]
      exact ⟨fun hx => Subtype.ext hx.1, fun hx => ⟨congrArg Subtype.val hx, x.2⟩⟩
    rw [← h2]
    exact isSubnormal_subgroupOf h.subnormal Y
  · obtain ⟨e'⟩ := h.nonempty_equiv
    have hO : (classicalInvolutionOddCore (K.subgroupOf Y)).map e.toMonoidHom =
        classicalInvolutionOddCore K :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e
    exact ⟨(QuotientGroup.congr _ _ e hO).trans e'⟩

end IsSectionMember

theorem AxisResidual.isSectionMember {J A I : Subgroup G} {z : G}
    (hJ : IsClassicalMember p f J z) (h : AxisResidual J A I z) (hperf : Group.IsPerfect I) :
    IsSectionMember p f (Subgroup.centralizer (A : Set G)) I z where
  le := h.le_inf.trans inf_le_right
  orderOf_eq_two := hJ.orderOf_eq_two
  mem := h.mem
  perfect := hperf
  subnormal := h.subnormal
  nonempty_equiv := by
    obtain ⟨e'⟩ := hJ.nonempty_equiv
    obtain ⟨φ⟩ := h.nonempty_equiv
    exact ⟨φ.trans e'⟩

end SectionMember


section Embedding

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {a : G}

@[expose] def NormalizesLayer (Ω : Set (Subgroup G)) (a : G) : Prop :=
  ∀ c : G, c ∈ Subgroup.centralizer ({a} : Set G) →
    c ∈ Subgroup.normalizer ((centLayer Ω a : Subgroup G) : Set G)

theorem map_inclusion_oddCore_le_of_normalizes (hN : NormalizesLayer Ω a) :
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
      hN c c.2
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

theorem ker_layerToOddQuot_of_normalizes (hN : NormalizesLayer Ω a) :
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
    exact oddQuotMk_eq_one_iff.mpr (map_inclusion_oddCore_le_of_normalizes hN ⟨d, hd, rfl⟩)

@[expose] noncomputable def sectionQuotientHom (hN : NormalizesLayer Ω a) :
    (↥(centLayer Ω a) ⧸ classicalInvolutionOddCore ↥(centLayer Ω a)) →* OddQuot a :=
  QuotientGroup.lift _ (layerToOddQuot Ω a) (ker_layerToOddQuot_of_normalizes hN).ge

theorem sectionQuotientHom_mk (hN : NormalizesLayer Ω a) (y : ↥(centLayer Ω a)) :
    sectionQuotientHom hN (QuotientGroup.mk' _ y) = layerToOddQuot Ω a y := rfl

theorem sectionQuotientHom_injective (hN : NormalizesLayer Ω a) :
    Function.Injective (sectionQuotientHom hN) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ x
  rw [sectionQuotientHom_mk] at hx
  have hy : y ∈ classicalInvolutionOddCore ↥(centLayer Ω a) := by
    rw [← ker_layerToOddQuot_of_normalizes hN]
    exact hx
  exact (QuotientGroup.eq_one_iff y).mpr hy

omit [Finite G] in
theorem memberJoin_normal_of_normalizes (hN : NormalizesLayer Ω a) : (memberJoin Ω a).Normal := by
  rw [← range_layerToOddQuot_eq]
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨y, rfl⟩ := hn
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have hc : (c : G) ∈ Subgroup.normalizer ((centLayer Ω a : Subgroup G) : Set G) := hN c c.2
  refine ⟨conjOn (centLayer Ω a) c hc y, ?_⟩
  have : (⟨((conjOn (centLayer Ω a) c hc y : ↥(centLayer Ω a)) : G),
      centLayer_le_centralizer Ω a (conjOn (centLayer Ω a) c hc y).2⟩ :
        ↥(Subgroup.centralizer ({a} : Set G))) =
      c * ⟨y, centLayer_le_centralizer Ω a y.2⟩ * c⁻¹ :=
    Subtype.ext (conjOn_apply (centLayer Ω a) (c : G) hc y)
  rw [layerToOddQuot_apply, layerToOddQuot_apply, this]
  simp [oddQuotMk]

theorem range_sectionQuotientHom (hN : NormalizesLayer Ω a) :
    (sectionQuotientHom hN).range = memberJoin Ω a := by
  rw [← range_layerToOddQuot_eq]
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨QuotientGroup.mk' _ y, rfl⟩

theorem map_sectionQuotientHom_family (hN : NormalizesLayer Ω a) :
    (fun M => M.map (sectionQuotientHom hN)) ''
      oddQuotientFamily (restrictFamily (centMembers Ω a) (centLayer Ω a)) =
      memberImages Ω a := by
  ext M
  constructor
  · rintro ⟨_, ⟨_, ⟨K, hK, hKY, rfl⟩, rfl⟩, rfl⟩
    refine ⟨K, hK, ?_⟩
    show modOdd a K = ((K.subgroupOf (centLayer Ω a)).map _).map (sectionQuotientHom hN)
    rw [Subgroup.map_map]
    exact (map_layerToOddQuot_subgroupOf hKY).symm
  · rintro ⟨K, hK, rfl⟩
    refine ⟨_, ⟨K.subgroupOf (centLayer Ω a), ⟨K, hK, le_centLayer hK, rfl⟩, rfl⟩, ?_⟩
    show ((K.subgroupOf (centLayer Ω a)).map _).map (sectionQuotientHom hN) = modOdd a K
    rw [Subgroup.map_map]
    exact map_layerToOddQuot_subgroupOf (le_centLayer hK)

end Embedding


section SecData

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {a : G}

structure SecData (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (a : G) (Φ : Set (Subgroup G)) :
    Prop where
  nonempty : Φ.Nonempty
  le : ∀ K ∈ Φ, K ≤ Subgroup.centralizer ({a} : Set G)
  conj : ∀ n ∈ Subgroup.centralizer ({a} : Set G), ∀ K ∈ Φ, conjSub n K ∈ Φ
  member : ∀ K ∈ Φ, ∃ z, IsSectionMember p f (Subgroup.centralizer ({a} : Set G)) K z

namespace SecData

variable {Φ : Set (Subgroup G)} (h : SecData p f a Φ)
include h

omit [Finite G] in
theorem centMembers_eq : centMembers Φ a = Φ := by
  ext K
  exact ⟨fun hK => hK.1, fun hK => ⟨hK, h.le K hK⟩⟩

omit [Finite G] in
theorem normalizes : NormalizesLayer Φ a := by
  have key : ∀ c : G, c ∈ Subgroup.centralizer ({a} : Set G) →
      centLayer Φ a ≤ conjSub c⁻¹ (centLayer Φ a) := by
    intro c hc
    refine centLayer_le fun L hL => ?_
    have hLc : conjSub c L ∈ centMembers Φ a :=
      ⟨h.conj c hc L hL.1, h.le _ (h.conj c hc L hL.1)⟩
    have h1 := conjSub_mono (n := c⁻¹) (le_centLayer hLc)
    rwa [conjSub_inv_conjSub] at h1
  intro c hc
  have hc' : c⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := inv_mem hc
  have h1 := key c hc
  have h2 := key c⁻¹ hc'
  rw [inv_inv] at h2
  have h3 : conjSub c (centLayer Φ a) ≤ centLayer Φ a := by
    have := conjSub_mono (n := c) h1
    rwa [conjSub_conjSub_inv] at this
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (le_antisymm h3 h2)

omit [Finite G] in
theorem member_layer {K : Subgroup G} (hK : K ∈ Φ) :
    ∃ z, IsSectionMember p f (centLayer Φ a) K z := by
  obtain ⟨z, hz⟩ := h.member K hK
  exact ⟨z, hz.restrict (centLayer_le_centralizer Φ a) (le_centLayer ⟨hK, h.le K hK⟩)⟩

omit [Finite G] in
theorem inClass : InClass p f (restrictFamily (centMembers Φ a) (centLayer Φ a)) := by
  refine inClass_of_isClassicalMemberIn (p := p) (f := f) (H := centLayer Φ a)
    (𝒮 := centMembers Φ a) ?_ (fun L hL => le_centLayer hL) ?_ rfl ?_
  · obtain ⟨K, hK⟩ := h.nonempty
    exact ⟨K, ⟨hK, h.le K hK⟩⟩
  · intro n hn L hL
    have hnC : n ∈ Subgroup.centralizer ({a} : Set G) := centLayer_le_centralizer Φ a hn
    exact ⟨h.conj n hnC L hL.1, h.le _ (h.conj n hnC L hL.1)⟩
  · intro L hL
    obtain ⟨z, hz⟩ := h.member_layer hL.1
    exact ⟨z, hz.toIn⟩

theorem not_le_center {K : Subgroup G} (hK : K ∈ Φ) :
    ¬ (K.subgroupOf (centLayer Φ a)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(centLayer Φ a))) ≤
      Subgroup.center (↥(centLayer Φ a) ⧸ classicalInvolutionOddCore ↥(centLayer Φ a)) := by
  intro hle
  obtain ⟨z, hz⟩ := h.member_layer hK
  set Y := centLayer Φ a with hY
  set O := classicalInvolutionOddCore ↥Y with hO
  have hKY : K ≤ Y := hz.le
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

theorem nonempty_lieSystem (hBelow : CITBelowU p f (Nat.card G))
    (ha : ¬ ({a} : Set G) ⊆ Subgroup.center G) : Nonempty (LocalLieSystemAt p f Φ a) := by
  have hlt : Nat.card (centralizingLayer Φ {a}) < Nat.card G := card_centralizingLayer_lt Φ ha
  have hIC : InClass p f (restrictFamily (centralizingMembers Φ {a}) (centralizingLayer Φ {a})) :=
    h.inClass
  exact hBelow _ hlt _ hIC

theorem lieDecomposition_comp (hp2 : p ≠ 2) (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1)
    (hq : 5 ≤ p ^ f) (D : LocalLieSystemAt p f Φ a) :
    ∃ D' : LieDecomposition (memberImages Φ a) (memberJoin Φ a),
      (∀ i, D'.Q i ∈ Set.range fun j : Fin D.card =>
        ((sectionQuotientHom h.normalizes).comp (D.hom j)).range) ∧
      ((∀ i, p ^ D.exp i ≠ 3) → D'.Big) := by
  have hθ := sectionQuotientHom_injective h.normalizes
  have h1 := lieDecomposition_of_lieSystemData_comp hp2 h0 hA1 hq D
    (sectionQuotientHom h.normalizes) hθ
    (by
      rintro _ ⟨_, ⟨K, hK, hKY, rfl⟩, rfl⟩
      exact h.not_le_center hK.1)
  have hΨ : Subgroup.map (sectionQuotientHom h.normalizes) ''
      oddQuotientFamily (restrictFamily (centralizingMembers Φ {a}) (centralizingLayer Φ {a})) =
      memberImages Φ a := map_sectionQuotientHom_family h.normalizes
  exact LieDecomposition.exists_congr hΨ (range_sectionQuotientHom h.normalizes) _ _ h1

end SecData

end SecData


section Central

variable {G : Type} [Group G] [Finite G]

theorem oddQuotMk_centralizes_of_commutator_mem {b : G} {L : Subgroup G}
    (hLb : L ≤ Subgroup.centralizer ({b} : Set G)) {t : G}
    (htb : t ∈ Subgroup.centralizer ({b} : Set G)) (hq : CFSG.Open.IsQuasisimple ↥(modOdd b L))
    (hact : ∀ l ∈ L, ⁅t, l⁆ ∈ oddCoreIn L) :
    ∀ q ∈ modOdd b L, oddQuotMk b ⟨t, htb⟩ * q = q * oddQuotMk b ⟨t, htb⟩ := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({b} : Set G) with hC
  set Q : Subgroup (OddQuot b) := modOdd b L with hQ
  set t' : OddQuot b := oddQuotMk b ⟨t, htb⟩ with ht'
  set N : Subgroup (OddQuot b) := modOdd b (oddCoreIn L) with hN
  have hNQ : N ≤ Q := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, oddCoreIn_le L hx, rfl⟩
  have hnorm : (N.subgroupOf Q).Normal := by
    refine ⟨fun n hn q => ?_⟩
    obtain ⟨m, hm, hmn⟩ := Subgroup.mem_subgroupOf.mp hn
    obtain ⟨l, hl, hlq⟩ := q.2
    rw [Subgroup.mem_subgroupOf]
    show (q : OddQuot b) * (n : OddQuot b) * (q : OddQuot b)⁻¹ ∈ N
    rw [← hlq, ← hmn]
    refine ⟨l * m * l⁻¹, ?_, ?_⟩
    · exact conj_mem_oddCoreIn (Subgroup.mem_subgroupOf.mp hl) (Subgroup.mem_subgroupOf.mp hm)
    · simp [map_mul, map_inv]
  have hNodd : Odd (Nat.card (N.subgroupOf Q)) := by
    have e : N.subgroupOf Q ≃* N := Subgroup.subgroupOfEquivOfLe hNQ
    rw [Nat.card_congr e.toEquiv]
    have h1 : Nat.card N ∣ Nat.card ((oddCoreIn L).subgroupOf C) :=
      Subgroup.card_map_dvd ((oddCoreIn L).subgroupOf C) (oddQuotMk b)
    have h2 : Nat.card ((oddCoreIn L).subgroupOf C) = Nat.card (oddCoreIn L) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe ((oddCoreIn_le L).trans hLb)).toEquiv
    exact (odd_card_oddCoreIn L).of_dvd_nat (h2 ▸ h1)
  have hNZ : N.subgroupOf Q ≤ Subgroup.center ↥Q :=
    (CFSG.ComponentClassification.OddCore.maximal ↥Q _ hnorm hNodd).trans
      (oddCore_le_center_of_isQuasisimple hq)
  have hcN : ∀ q ∈ Q, ⁅t', q⁆ ∈ N := by
    intro q hq
    obtain ⟨l, hl, rfl⟩ := hq
    refine ⟨⁅(⟨t, htb⟩ : ↥C), l⁆, hact l hl, ?_⟩
    simp [ht', map_commutatorElement]
  have hcen : ∀ q : ↥Q, (⟨⁅t', (q : OddQuot b)⁆, hNQ (hcN q q.2)⟩ : ↥Q) ∈ Subgroup.center ↥Q :=
    fun q => hNZ (Subgroup.mem_subgroupOf.mpr (hcN q q.2))
  let φ : ↥Q →* ↥(Subgroup.center ↥Q) :=
    { toFun := fun q => ⟨⟨⁅t', (q : OddQuot b)⁆, hNQ (hcN q q.2)⟩, hcen q⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_mul' := fun q r => by
        apply Subtype.ext
        apply Subtype.ext
        have hr := Subgroup.mem_center_iff.mp (hcen r) q
        have hr' : (q : OddQuot b) * ⁅t', (r : OddQuot b)⁆ = ⁅t', (r : OddQuot b)⁆ * q :=
          congrArg Subtype.val hr
        show ⁅t', (q : OddQuot b) * (r : OddQuot b)⁆ =
          ⁅t', (q : OddQuot b)⁆ * ⁅t', (r : OddQuot b)⁆
        calc ⁅t', (q : OddQuot b) * (r : OddQuot b)⁆
            = ⁅t', (q : OddQuot b)⁆ *
                ((q : OddQuot b) * ⁅t', (r : OddQuot b)⁆ * (q : OddQuot b)⁻¹) := by
              simp only [commutatorElement_def]
              group
          _ = ⁅t', (q : OddQuot b)⁆ * ⁅t', (r : OddQuot b)⁆ := by rw [hr']; group }
  have hker : commutator ↥Q ≤ φ.ker := Abelianization.commutator_subset_ker φ
  intro q hqQ
  have hmem : (⟨q, hqQ⟩ : ↥Q) ∈ φ.ker := hker (by rw [hq.1]; exact Subgroup.mem_top _)
  have h1 : ⁅t', q⁆ = 1 := congrArg (fun x => ((x : ↥(Subgroup.center ↥Q)) : ↥Q).1)
    (MonoidHom.mem_ker.mp hmem)
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

end Central


section BProperty

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem modOdd_mono {b : G} {K K' : Subgroup G} (h : K ≤ K') : modOdd b K ≤ modOdd b K' := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

theorem hB_of_lieDecomposition {Φ : Set (Subgroup G)} {b : G}
    (D : LieDecomposition (memberImages Φ b) (memberJoin Φ b)) [(memberJoin Φ b).Normal]
    {L₁ : Subgroup G} (hL₁ : L₁ ∈ centMembers Φ b) {L₀ : Subgroup G} (hL₀₁ : L₀ ≤ L₁)
    (hperf : ⁅modOdd b L₀, modOdd b L₀⁆ = modOdd b L₀) (hne : modOdd b L₀ ≠ ⊥) {t : G}
    (ht2 : t * t = 1) (ht1 : t ≠ 1) (htL₀ : ∀ l ∈ L₀, t * l = l * t) (htb : t * b = b * t)
    (hact : ∀ l ∈ L₁, ⁅t, l⁆ ∈ oddCoreIn L₁)
    (M : Subgroup ↥(imageModOddCore b (Subgroup.centralizer {t} ⊓ Subgroup.centralizer {b})))
    (hM : TwoComponents.IsTwoComponent M) :
    CFSG.Open.IsQuasisimple M ∨
      ⁅M.map (imageModOddCore b
        (Subgroup.centralizer {t} ⊓ Subgroup.centralizer {b})).subtype,
        imageModOddCore b L₀⁆ = ⊥ := by
  have htC : t ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr htb
  set t' : OddQuot b := oddQuotMk b ⟨t, htC⟩ with ht'
  have hsq : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({b} : Set G))) * ⟨t, htC⟩ = 1 :=
    Subtype.ext ht2
  have ht'2 : t' * t' = 1 := by
    rw [ht', ← map_mul, hsq, map_one]
  have ht'1 : t' ≠ 1 := fun h => ht1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hsq h))
  have ht'L : ∀ l ∈ modOdd b L₀, t' * l = l * t' := by
    rintro _ ⟨l, hl, rfl⟩
    rw [ht', ← map_mul, ← map_mul]
    exact congrArg (oddQuotMk b) (Subtype.ext (htL₀ l hl))
  have hLb : modOdd b L₁ ∈ memberImages Φ b := ⟨L₁, hL₁, rfl⟩
  obtain ⟨i, hi₁⟩ := D.exists_le _ hLb
  have hi : modOdd b L₀ ≤ D.Q i := (modOdd_mono hL₀₁).trans hi₁
  have hQ : IsComponentOf (D.Q i) ⊤ := D.isComponentOf i
  have hQB : ∀ M₁ : Subgroup ↥(D.Q i ⊓ Subgroup.centralizer ({t'} : Set (OddQuot b))),
      TwoComponents.IsTwoComponent M₁ → CFSG.Open.IsQuasisimple M₁ := by
    intro M₁ hM₁
    rcases D.rankOne_or_lie i with ⟨-, hmin⟩ | hlie
    · have hQeq : modOdd b L₁ = D.Q i := hmin _ hLb hi₁
      have hq : CFSG.Open.IsQuasisimple ↥(modOdd b L₁) := by
        rw [hQeq]
        exact D.quasisimple i
      have hcent : D.Q i ≤ Subgroup.centralizer ({t'} : Set (OddQuot b)) := by
        intro q hq'
        rw [← hQeq] at hq'
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (oddQuotMk_centralizes_of_commutator_mem hL₁.2 htC hq hact q hq').symm
      have hRQ : CFSG.Open.IsQuasisimple
          ↥(D.Q i ⊓ Subgroup.centralizer ({t'} : Set (OddQuot b))) :=
        Components.quasisimple_of_equiv
          (MulEquiv.subgroupCongr (inf_eq_left.mpr hcent)) (D.quasisimple i)
      exact isQuasisimple_of_isTwoComponent_of_isQuasisimple hRQ hM₁
    · have hnorm : t' ∈ Subgroup.normalizer ((D.Q i : Subgroup (OddQuot b)) : Set (OddQuot b)) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr
          (map_conj_eq_of_centralizes hQ hi hperf hne ht'L)
      exact involutionCentralizerB_of_isOddLieComponent (D.quasisimple i) hlie t' ht'1 ht'2
        hnorm M₁ hM₁
  have hW := imageModOddCore_centralizer htC (isPGroup_zpowers_of_mul_self_eq_one ht2)
  exact isQuasisimple_or_commutator_eq_bot_of_centralizes l2PrimeBalance
    (OddCore.quotient_corefree _) hQ hi hperf hne ht'2 ht'L hQB hW M hM

end BProperty


section Residual

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_perfectResidualOf_of_perfect {H P : Subgroup G} (hPH : P ≤ H) (hP : Group.IsPerfect P) :
    P ≤ perfectResidualOf H := by
  have hP' : Group.IsPerfect ↥(P.subgroupOf H) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPH).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPH).symm.surjective
  have hcomm : ⁅P.subgroupOf H, P.subgroupOf H⁆ = P.subgroupOf H := Subgroup.commutator_eq_self
  have hder : ∀ n : ℕ, P.subgroupOf H ≤ derivedSeries ↥H n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [derivedSeries_succ]
      calc P.subgroupOf H = ⁅P.subgroupOf H, P.subgroupOf H⁆ := hcomm.symm
        _ ≤ ⁅derivedSeries ↥H n, derivedSeries ↥H n⁆ := Subgroup.commutator_mono ih ih
  intro x hx
  refine ⟨⟨x, hPH hx⟩, ?_, rfl⟩
  have : (⟨x, hPH hx⟩ : ↥H) ∈ P.subgroupOf H := hx
  exact Subgroup.mem_iInf.mpr fun n => hder n this

theorem perfectResidualOf_mono {H H' : Subgroup G} (hHH' : H ≤ H') :
    perfectResidualOf H ≤ perfectResidualOf H' :=
  le_perfectResidualOf_of_perfect ((Subgroup.map_subtype_le _).trans hHH')
    (finite_perfectResidualOf_isPerfect H)

end Residual


section Triangle

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem secData_of_members {b : G} {I₁ I₂ I₃ : Subgroup G} {z₁ z₂ z₃ : G}
    (h₁ : IsSectionMember p f (Subgroup.centralizer ({b} : Set G)) I₁ z₁)
    (h₂ : IsSectionMember p f (Subgroup.centralizer ({b} : Set G)) I₂ z₂)
    (h₃ : IsSectionMember p f (Subgroup.centralizer ({b} : Set G)) I₃ z₃) :
    SecData p f b {K | ∃ n ∈ Subgroup.centralizer ({b} : Set G),
      ∃ I ∈ ({I₁, I₂, I₃} : Set (Subgroup G)), K = conjSub n I} := by
  set Y := Subgroup.centralizer ({b} : Set G) with hY
  have hmem : ∀ I ∈ ({I₁, I₂, I₃} : Set (Subgroup G)), ∃ z, IsSectionMember p f Y I z := by
    intro I hI
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hI
    rcases hI with rfl | rfl | rfl
    exacts [⟨z₁, h₁⟩, ⟨z₂, h₂⟩, ⟨z₃, h₃⟩]
  refine ⟨⟨I₁, 1, one_mem _, I₁, by simp, (conjSub_one I₁).symm⟩, ?_, ?_, ?_⟩
  · rintro K ⟨n, hn, I, hI, rfl⟩
    obtain ⟨z, hz⟩ := hmem I hI
    have := conjSub_mono (n := n) hz.le
    rwa [conjSub_eq_self_of_mem hn] at this
  · rintro n' hn' K ⟨n, hn, I, hI, rfl⟩
    exact ⟨n' * n, mul_mem hn' hn, I, hI, by rw [conjSub_mul]⟩
  · rintro K ⟨n, hn, I, hI, rfl⟩
    obtain ⟨z, hz⟩ := hmem I hI
    exact ⟨n * z * n⁻¹, hz.conj hn⟩

structure AxisTriangle (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (J₁ J₂ J₃ : Subgroup G) (z₁ z₂ z₃ : G) : Prop where
  cls₁ : IsClassicalMember p f J₁ z₁
  cls₂ : IsClassicalMember p f J₂ z₂
  cls₃ : IsClassicalMember p f J₃ z₃
  comm₁₂ : z₁ * z₂ = z₂ * z₁
  comm₁₃ : z₁ * z₃ = z₃ * z₁
  comm₂₃ : z₂ * z₃ = z₃ * z₂
  tq₁₂ : z₂ ∈ trivialOnQuot J₁
  tq₁₃ : z₃ ∈ trivialOnQuot J₁
  tq₂₁ : z₁ ∈ trivialOnQuot J₂
  tq₂₃ : z₃ ∈ trivialOnQuot J₂
  tq₃₁ : z₁ ∈ trivialOnQuot J₃
  tq₃₂ : z₂ ∈ trivialOnQuot J₃

structure FuzzyTriangle (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (J₁ J₂ J₃ : Subgroup G)
    (z₁ z₂ z₃ : G) : Prop where
  cls₁ : IsClassicalMember p f J₁ z₁
  cls₂ : IsClassicalMember p f J₂ z₂
  cls₃ : IsClassicalMember p f J₃ z₃
  e₁₂ : FuzzyEdge J₁ J₂
  e₁₃ : FuzzyEdge J₁ J₃
  e₂₃ : FuzzyEdge J₂ J₃

@[expose] def triangleResidual (J : Subgroup G) (b : G) : Subgroup G :=
  perfectResidualOf (J ⊓ Subgroup.centralizer ({b} : Set G))

@[expose] def triangleSecFamily (J₁ J₂ J₃ : Subgroup G) (b : G) : Set (Subgroup G) :=
  {K | ∃ n ∈ Subgroup.centralizer ({b} : Set G),
    ∃ I ∈ ({triangleResidual J₁ b, triangleResidual J₂ b, triangleResidual J₃ b} :
      Set (Subgroup G)), K = conjSub n I}

theorem FuzzyTriangle.toAxisTriangle {J₁ J₂ J₃ : Subgroup G} {z₁ z₂ z₃ : G}
    (hT : FuzzyTriangle p f J₁ J₂ J₃ z₁ z₂ z₃) : AxisTriangle p f J₁ J₂ J₃ z₁ z₂ z₃ := by
  obtain ⟨hcomm, -, hA₁, hA₂, hA₃⟩ := triangleAxis_data
    (isCentralInvolution_of_isClassicalMember hT.cls₁)
    (isCentralInvolution_of_isClassicalMember hT.cls₂)
    (isCentralInvolution_of_isClassicalMember hT.cls₃) hT.e₁₂ hT.e₁₃ hT.e₂₃
  have hz₁ : z₁ ∈ triangleAxis z₁ z₂ z₃ := Subgroup.subset_closure (by simp)
  have hz₂ : z₂ ∈ triangleAxis z₁ z₂ z₃ := Subgroup.subset_closure (by simp)
  have hz₃ : z₃ ∈ triangleAxis z₁ z₂ z₃ := Subgroup.subset_closure (by simp)
  exact ⟨hT.cls₁, hT.cls₂, hT.cls₃, hcomm _ hz₁ _ hz₂, hcomm _ hz₁ _ hz₃, hcomm _ hz₂ _ hz₃,
    hA₁ hz₂, hA₁ hz₃, hA₂ hz₁, hA₂ hz₃, hA₃ hz₁, hA₃ hz₂⟩

namespace AxisTriangle

variable {J₁ J₂ J₃ : Subgroup G} {z₁ z₂ z₃ : G}

theorem axis_data (hT : AxisTriangle p f J₁ J₂ J₃ z₁ z₂ z₃) :
    (∀ a ∈ triangleAxis z₁ z₂ z₃, ∀ b ∈ triangleAxis z₁ z₂ z₃, a * b = b * a) ∧
    (∀ a ∈ triangleAxis z₁ z₂ z₃, a * a = 1) ∧
    triangleAxis z₁ z₂ z₃ ≤ trivialOnQuot J₁ ∧ triangleAxis z₁ z₂ z₃ ≤ trivialOnQuot J₂ ∧
    triangleAxis z₁ z₂ z₃ ≤ trivialOnQuot J₃ := by
  have c₁ := isCentralInvolution_of_isClassicalMember hT.cls₁
  have c₂ := isCentralInvolution_of_isClassicalMember hT.cls₂
  have c₃ := isCentralInvolution_of_isClassicalMember hT.cls₃
  have hcen : ∀ {J : Subgroup G} {z : G}, IsCentralInvolution J z → ∀ x ∈ J, x * z = z * x :=
    fun h x hx => (h.central x hx).symm
  have hSc : ∀ s ∈ ({z₁, z₂, z₃} : Set G), ∀ t ∈ ({z₁, z₂, z₃} : Set G), s * t = t * s := by
    intro s hs t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
      first | rfl | exact hT.comm₁₂ | exact hT.comm₁₃ | exact hT.comm₂₃ | exact hT.comm₁₂.symm |
        exact hT.comm₁₃.symm | exact hT.comm₂₃.symm
  have hS2 : ∀ s ∈ ({z₁, z₂, z₃} : Set G), s * s = 1 := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    exacts [c₁.sq, c₂.sq, c₃.sq]
  refine ⟨closure_commute_of_commute hSc, mul_self_of_mem_closure hS2 hSc, ?_, ?_, ?_⟩
  · refine (Subgroup.closure_le _).mpr fun s hs => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    exacts [mem_trivialOnQuot_self c₁.mem (hcen c₁), hT.tq₁₂, hT.tq₁₃]
  · refine (Subgroup.closure_le _).mpr fun s hs => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    exacts [hT.tq₂₁, mem_trivialOnQuot_self c₂.mem (hcen c₂), hT.tq₂₃]
  · refine (Subgroup.closure_le _).mpr fun s hs => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    exacts [hT.tq₃₁, hT.tq₃₂, mem_trivialOnQuot_self c₃.mem (hcen c₃)]

theorem isElemAbelian (hT : AxisTriangle p f J₁ J₂ J₃ z₁ z₂ z₃) :
    IsElemAbelian 2 (triangleAxis z₁ z₂ z₃) := by
  obtain ⟨hcomm, hsq, -⟩ := hT.axis_data
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2)⟩⟩, fun x hx => ?_⟩
  rw [pow_two]
  exact hsq x hx

theorem axisResidual (hT : AxisTriangle p f J₁ J₂ J₃ z₁ z₂ z₃) {A : Subgroup G}
    (hA : A ≤ triangleAxis z₁ z₂ z₃) :
    AxisResidual J₁ A (perfectResidualOf (J₁ ⊓ Subgroup.centralizer (A : Set G))) z₁ ∧
    AxisResidual J₂ A (perfectResidualOf (J₂ ⊓ Subgroup.centralizer (A : Set G))) z₂ ∧
    AxisResidual J₃ A (perfectResidualOf (J₃ ⊓ Subgroup.centralizer (A : Set G))) z₃ := by
  have c₁ := isCentralInvolution_of_isClassicalMember hT.cls₁
  have c₂ := isCentralInvolution_of_isClassicalMember hT.cls₂
  have c₃ := isCentralInvolution_of_isClassicalMember hT.cls₃
  obtain ⟨-, hsq, hA₁, hA₂, hA₃⟩ := hT.axis_data
  have hA2 : IsPGroup 2 A := isPGroup_two_of_sq_eq_one fun x hx => hsq x (hA hx)
  exact ⟨axisResidual_perfectResidual hT.cls₁.perfect hT.cls₁.mem c₁.sq
      (fun x hx => (c₁.central x hx).symm) hT.cls₁.subnormal hA2 (hA.trans hA₁),
    axisResidual_perfectResidual hT.cls₂.perfect hT.cls₂.mem c₂.sq
      (fun x hx => (c₂.central x hx).symm) hT.cls₂.subnormal hA2 (hA.trans hA₂),
    axisResidual_perfectResidual hT.cls₃.perfect hT.cls₃.mem c₃.sq
      (fun x hx => (c₃.central x hx).symm) hT.cls₃.subnormal hA2 (hA.trans hA₃)⟩

theorem axisResidual_at (hT : AxisTriangle p f J₁ J₂ J₃ z₁ z₂ z₃) {b : G}
    (hb : b ∈ triangleAxis z₁ z₂ z₃) :
    AxisResidual J₁ (Subgroup.zpowers b) (triangleResidual J₁ b) z₁ ∧
    AxisResidual J₂ (Subgroup.zpowers b) (triangleResidual J₂ b) z₂ ∧
    AxisResidual J₃ (Subgroup.zpowers b) (triangleResidual J₃ b) z₃ := by
  have h := hT.axisResidual (Subgroup.zpowers_le.mpr hb)
  simpa only [triangleResidual, centralizer_zpowers_eq_singleton'] using h

theorem isSectionMember_at (hT : AxisTriangle p f J₁ J₂ J₃ z₁ z₂ z₃) {b : G}
    (hb : b ∈ triangleAxis z₁ z₂ z₃) :
    IsSectionMember p f (Subgroup.centralizer ({b} : Set G)) (triangleResidual J₁ b) z₁ ∧
    IsSectionMember p f (Subgroup.centralizer ({b} : Set G)) (triangleResidual J₂ b) z₂ ∧
    IsSectionMember p f (Subgroup.centralizer ({b} : Set G)) (triangleResidual J₃ b) z₃ := by
  obtain ⟨r₁, r₂, r₃⟩ := hT.axisResidual_at hb
  have hperf : ∀ J : Subgroup G, Group.IsPerfect ↥(triangleResidual J b) := fun J =>
    finite_perfectResidualOf_isPerfect _
  have e1 := r₁.isSectionMember hT.cls₁ (hperf J₁)
  have e2 := r₂.isSectionMember hT.cls₂ (hperf J₂)
  have e3 := r₃.isSectionMember hT.cls₃ (hperf J₃)
  simp only [centralizer_zpowers_eq_singleton'] at e1 e2 e3
  exact ⟨e1, e2, e3⟩

theorem secData (hT : AxisTriangle p f J₁ J₂ J₃ z₁ z₂ z₃) {b : G}
    (hb : b ∈ triangleAxis z₁ z₂ z₃) : SecData p f b (triangleSecFamily J₁ J₂ J₃ b) := by
  obtain ⟨e1, e2, e3⟩ := hT.isSectionMember_at hb
  exact secData_of_members e1 e2 e3

end AxisTriangle

end Triangle


section Weak

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem modOdd_perfect_of_perfect {b : G} {I : Subgroup G}
    (hIb : I ≤ Subgroup.centralizer ({b} : Set G)) (hI : Group.IsPerfect ↥I) :
    ⁅modOdd b I, modOdd b I⁆ = modOdd b I := by
  have : Group.IsPerfect ↥(I.subgroupOf (Subgroup.centralizer ({b} : Set G))) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hIb).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hIb).symm.surjective
  have hKK := Subgroup.commutator_eq_self (H := I.subgroupOf (Subgroup.centralizer ({b} : Set G)))
  unfold modOdd
  rw [← Subgroup.map_commutator, hKK]

theorem modOdd_ne_bot_of_involution {b : G} {I : Subgroup G} {z : G} (hzI : z ∈ I)
    (hIb : I ≤ Subgroup.centralizer ({b} : Set G)) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    modOdd b I ≠ ⊥ := by
  intro hbot
  have hzC : z ∈ Subgroup.centralizer ({b} : Set G) := hIb hzI
  have hsq : (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({b} : Set G))) * ⟨z, hzC⟩ = 1 := Subtype.ext hz2
  have hmem : oddQuotMk b ⟨z, hzC⟩ ∈ modOdd b I := oddQuotMk_mem_modOdd hzI hzC
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hz1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hsq hmem))

theorem commutator_mem_oddCoreIn_triangleResidual {J : Subgroup G} {g b z : G}
    (hg : g ∈ trivialOnQuot J) (hgb : g ∈ Subgroup.centralizer ({b} : Set G))
    (rb : AxisResidual J (Subgroup.zpowers b) (triangleResidual J b) z) {l : G}
    (hl : l ∈ triangleResidual J b) : ⁅g, l⁆ ∈ oddCoreIn (triangleResidual J b) := by
  have hlJ : l ∈ J := ((Subgroup.map_subtype_le _ : triangleResidual J b ≤ J ⊓
    Subgroup.centralizer ({b} : Set G)) hl).1
  have hnorm : g ∈ Subgroup.normalizer ((J ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) :
      Set G) := mem_normalizer_inf hg.1 (Subgroup.le_normalizer hgb)
  have hnorm' := perfectResidualOf_normalizer_contains (J ⊓ Subgroup.centralizer ({b} : Set G))
    hnorm
  have hconj : g * l * g⁻¹ ∈ triangleResidual J b :=
    (Subgroup.mem_normalizer_iff.mp hnorm' l).mp hl
  have hcomm : ⁅g, l⁆ ∈ triangleResidual J b := by
    have e : ⁅g, l⁆ = (g * l * g⁻¹) * l⁻¹ := rfl
    rw [e]
    exact mul_mem hconj (inv_mem hl)
  rw [rb.oddCoreIn_eq]
  exact ⟨hcomm, hg.2 l hlJ⟩

theorem commutator_oddCoreIn_le_of_vertex [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hBelow : CITBelowU p f (Nat.card G)) {J : Subgroup G} {z : G}
    (hJ : IsClassicalMember p f J z) {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAJ : A ≤ trivialOnQuot J) (hz : z ∈ A) {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1) (hb : b ∈ A)
    (hb1 : b ≠ 1) {Φ : Set (Subgroup G)} (hs : SecData p f b Φ) (hΦ : triangleResidual J b ∈ Φ)
    (rb : AxisResidual J (Subgroup.zpowers b) (triangleResidual J b) z) {I : Subgroup G}
    (rA : AxisResidual J A I z) (hIperf : Group.IsPerfect ↥I) :
    ⁅oddCoreIn (Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b}), I⁆ ≤
      involutionOddCore b := by
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [GaloisField.card p f hf.ne']
    omega
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hAC : ∀ x : G, x ∈ A → A ≤ Subgroup.centralizer ({x} : Set G) := fun x hx y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc y hy x hx)
  have hIC : I ≤ Subgroup.centralizer (A : Set G) := rA.le_inf.trans inf_le_right
  have hCAa : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha)
  have hCAb : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb)
  have hCAz : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hz)
  have hc := isCentralInvolution_of_isClassicalMember hJ
  have hIb : I ≤ Subgroup.centralizer ({b} : Set G) := hIC.trans hCAb
  have hI₁ : I ≤ triangleResidual J b :=
    le_perfectResidualOf_of_perfect (le_inf (rA.le_inf.trans inf_le_left) hIb) hIperf
  have hL₁ : triangleResidual J b ∈ centMembers Φ b := ⟨hΦ, hs.le _ hΦ⟩
  have hperfimg : ⁅modOdd b I, modOdd b I⁆ = modOdd b I := modOdd_perfect_of_perfect hIb hIperf
  have hne : modOdd b I ≠ ⊥ := modOdd_ne_bot_of_involution rA.mem hIb hc.sq hc.ne_one
  have ha2 : a * a = 1 := by
    rw [← pow_two]
    exact hA.2 a ha
  have htb : a * b = b * a := hAc a ha b hb
  have htI : ∀ l ∈ I, a * l = l * a := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hCAa (hIC hl))).symm
  have hact : ∀ l ∈ triangleResidual J b, ⁅a, l⁆ ∈ oddCoreIn (triangleResidual J b) := fun l hl =>
    commutator_mem_oddCoreIn_triangleResidual (hAJ ha) (hAC b hb ha) rb hl
  obtain ⟨Dsys⟩ := hs.nonempty_lieSystem hBelow (not_subset_center_of_ne_one hnab hb1)
  obtain ⟨D', -, -⟩ := hs.lieDecomposition_comp hp2 h0 hA1 hq Dsys
  have : (memberJoin Φ b).Normal := memberJoin_normal_of_normalizes hs.normalizes
  obtain ⟨e'⟩ := hJ.nonempty_equiv
  obtain ⟨φ⟩ := rA.nonempty_equiv
  refine commutator_oddCoreIn_le_of_l2PrimeBalance l2PrimeBalance hA hb (hAC a ha)
    (le_inf (hIC.trans hCAa) hIC) ?_ hIperf.commutator_eq_top
    (Components.quasisimple_of_equiv (φ.trans e') (isQuasisimple_specialLinearGroup_two h4))
    fun M hM => hB_of_lieDecomposition D' hL₁ hI₁ hperfimg hne ha2 ha1 htI htb hact M hM
  rw [inf_eq_right.mpr hCAa]
  have h1 := rA.subnormal
  rwa [inf_eq_right.mpr hCAz] at h1

theorem AxisTriangle.weakBalanced [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1)
    (hBelow : CITBelowU p f (Nat.card G)) {J₁ J₂ J₃ : Subgroup G} {z₁ z₂ z₃ : G}
    (hT : AxisTriangle p f J₁ J₂ J₃ z₁ z₂ z₃) : WeakBalanced (triangleAxis z₁ z₂ z₃) := by
  intro a ha ha1 b hb hb1
  obtain ⟨hcomm, -, hA₁, hA₂, hA₃⟩ := hT.axis_data
  have hel := hT.isElemAbelian
  obtain ⟨rA₁, rA₂, rA₃⟩ := hT.axisResidual (le_refl _)
  obtain ⟨rb₁, rb₂, rb₃⟩ := hT.axisResidual_at hb
  have hs := hT.secData hb
  have hz₁ : z₁ ∈ triangleAxis z₁ z₂ z₃ := Subgroup.subset_closure (by simp)
  have hz₂ : z₂ ∈ triangleAxis z₁ z₂ z₃ := Subgroup.subset_closure (by simp)
  have hz₃ : z₃ ∈ triangleAxis z₁ z₂ z₃ := Subgroup.subset_closure (by simp)
  have hΦ : ∀ K ∈ ({triangleResidual J₁ b, triangleResidual J₂ b, triangleResidual J₃ b} :
      Set (Subgroup G)), K ∈ triangleSecFamily J₁ J₂ J₃ b := fun K hK =>
    ⟨1, one_mem _, K, hK, (conjSub_one K).symm⟩
  have k₁ := commutator_oddCoreIn_le_of_vertex hnab hp2 hq h0 hA1 hBelow hT.cls₁ hel hA₁ hz₁ ha
    ha1 hb hb1 hs (hΦ _ (by simp)) rb₁ rA₁ (finite_perfectResidualOf_isPerfect _)
  have k₂ := commutator_oddCoreIn_le_of_vertex hnab hp2 hq h0 hA1 hBelow hT.cls₂ hel hA₂ hz₂ ha
    ha1 hb hb1 hs (hΦ _ (by simp)) rb₂ rA₂ (finite_perfectResidualOf_isPerfect _)
  have k₃ := commutator_oddCoreIn_le_of_vertex hnab hp2 hq h0 hA1 hBelow hT.cls₃ hel hA₃ hz₃ ha
    ha1 hb hb1 hs (hΦ _ (by simp)) rb₃ rA₃ (finite_perfectResidualOf_isPerfect _)
  have hbC : ∀ x ∈ triangleAxis z₁ z₂ z₃, x ∈ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx b hb)
  rw [Subgroup.commutator_le]
  intro r hr g hg
  have hR : involutionOddCore a ⊓ Subgroup.centralizer {b} ≤
      oddCoreIn (Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b}) := by
    refine le_oddCoreIn_of_normalizes (inf_le_inf (involutionOddCore_le_centralizer a) le_rfl)
      (fun x hx => mem_normalizer_inf (normalizer_oddCoreIn _ hx.1)
        (Subgroup.le_normalizer hx.2)) ?_
    exact (odd_card_oddCoreIn (Subgroup.centralizer {a})).of_dvd_nat
      (Subgroup.card_dvd_of_le inf_le_left)
  have hrR : r ∈ oddCoreIn (Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b}) := hR hr
  have key : ∀ x ∈ Subgroup.closure ({z₁, z₂, z₃} : Set G), ⁅r, x⁆ ∈ involutionOddCore b := by
    intro x hx
    refine Subgroup.closure_induction
      (p := fun x _ => ⁅r, x⁆ ∈ involutionOddCore b) ?_ ?_ ?_ ?_ hx
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact k₁ (Subgroup.commutator_mem_commutator hrR rA₁.mem)
      · exact k₂ (Subgroup.commutator_mem_commutator hrR rA₂.mem)
      · exact k₃ (Subgroup.commutator_mem_commutator hrR rA₃.mem)
    · simp
    · intro x y hx hy hxM hyM
      have hxA : x ∈ triangleAxis z₁ z₂ z₃ := hx
      have : ⁅r, x * y⁆ = ⁅r, x⁆ * (x * ⁅r, y⁆ * x⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact (involutionOddCore b).mul_mem hxM (conj_mem_oddCoreIn (hbC x hxA) hyM)
    · intro x hx hxM
      have hxA : x ∈ triangleAxis z₁ z₂ z₃ := hx
      have : ⁅r, x⁻¹⁆ = x⁻¹ * ⁅r, x⁆⁻¹ * x⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact conj_mem_oddCoreIn (inv_mem (hbC x hxA)) ((involutionOddCore b).inv_mem hxM)
  exact key g hg

theorem FuzzyTriangle.weakBalanced [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1)
    (hBelow : CITBelowU p f (Nat.card G)) {J₁ J₂ J₃ : Subgroup G} {z₁ z₂ z₃ : G}
    (hT : FuzzyTriangle p f J₁ J₂ J₃ z₁ z₂ z₃) : WeakBalanced (triangleAxis z₁ z₂ z₃) :=
  hT.toAxisTriangle.weakBalanced hnab hp2 hq h0 hA1 hBelow

end Weak

end CFSG.ClassicalInvolution.Balance.Bootstrap
