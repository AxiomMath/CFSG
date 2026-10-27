module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.LocalOfData

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoFi22
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_centPair_iff {z t g : G} : g ∈ centPair z t ↔ z * g = g * z ∧ t * g = g * t := by
  constructor
  · intro hg
    have hg' := mem_centralizer_iff.1 hg
    exact ⟨hg' z (mem_sup_left (mem_zpowers z)), hg' t (mem_sup_right (mem_zpowers t))⟩
  · rintro ⟨hz, ht⟩
    rw [mem_centralizer_iff]
    intro h hh
    have hle : pair z t ≤ centralizer ({g} : Set G) := by
      refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
      · exact mem_centralizer_singleton_iff.2 hz
      · exact mem_centralizer_singleton_iff.2 ht
    exact mem_centralizer_singleton_iff.1 (hle hh)

theorem centPair_eq_inf (z t : G) : centPair z t = centZ z ⊓ centralizer ({t} : Set G) := by
  ext g
  rw [mem_centPair_iff, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1.symm, h2.symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1.symm, h2.symm⟩

theorem z_mem_pair (z t : G) : z ∈ pair z t := mem_sup_left (mem_zpowers z)

theorem t_mem_pair (z t : G) : t ∈ pair z t := mem_sup_right (mem_zpowers t)

structure Level55 (G : Type) [Group G] [Finite G] (t z : G) where
  R0 : Subgroup G
  z_ord : orderOf z = 2
  t_ord : orderOf t = 2
  zt_comm : z * t = t * z
  R0_le : R0 ≤ centPair z t
  R0_ext : CFSG.IsExtraspecialPGroup 2 ↥R0
  R0_card : Nat.card R0 = 2 ^ 23
  R0_center : (center ↥R0).map R0.subtype = zpowers z
  O2K : O2In (centPair z t) = R0 ⊔ zpowers t
  t_not_mem : t ∉ R0
  t_mem_comm : t ∈ ⁅R0, centPair z t⁆
  irred : ∀ W : Subgroup G, pair z t ≤ W → W ≤ O2In (centPair z t) →
    (∀ k ∈ centPair z t, ∀ w ∈ W, k * w * k⁻¹ ∈ W) → W = pair z t ∨ W = O2In (centPair z t)
  quot : Nonempty (↥(centPair z t) ⧸ CFSG.pCore 2 ↥(centPair z t) ≃* Carrier .Co2)
  not_constrained : ¬ IsTwoConstrained (centralizer ({t} : Set G))


theorem card_eq_two_of_isPGroup_two {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hp : IsPGroup 2 Q) : Nat.card Q = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial (center Q) := hp.center_nontrivial
  have hcen : center Q = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) with h | h
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (1 : center Q)
      apply hx
      have : (x : Q) ∈ (⊥ : Subgroup Q) := h ▸ x.2
      exact Subtype.ext (mem_bot.1 this)
    · exact h
  have hcomm : ∀ a b : Q, a * b = b * a := fun a b => by
    have := mem_center_iff.1 (hcen ▸ mem_top b) a
    exact this
  let _ : CommGroup Q := { ‹Group Q› with mul_comm := hcomm }
  have hprime := IsSimpleGroup.prime_card (α := Q)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hp
  rw [hn] at hprime ⊢
  rcases n with _ | n
  · rw [pow_zero] at hprime
    exact absurd hprime Nat.not_prime_one
  · have h2 : (2 : ℕ) ∣ 2 ^ (n + 1) := dvd_pow_self 2 (Nat.succ_ne_zero n)
    exact (Nat.prime_dvd_prime_iff_eq Nat.prime_two hprime).1 h2 |>.symm

theorem not_isTwoConstrained_of_simple_quotient {L : Subgroup G} [Finite G]
    (hs : IsSimpleGroup (↥L ⧸ center ↥L)) (hZ : Nat.card (center ↥L) = 2)
    (h4 : 4 < Nat.card L) : ¬ IsTwoConstrained L := by
  intro hcon
  have hn : ((CFSG.pCore 2 ↥L).map (QuotientGroup.mk' (center ↥L))).Normal :=
    Subgroup.Normal.map CFSG.pCore_normal _ (QuotientGroup.mk'_surjective _)
  have hQp : IsPGroup 2 (CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
  have hp : IsPGroup 2 (↥L ⧸ center ↥L) := by
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs
      ((CFSG.pCore 2 ↥L).map (QuotientGroup.mk' (center ↥L))) hn with hb | ht
    · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hb
      have hall : (⊤ : Subgroup ↥L) ≤ CFSG.pCore 2 ↥L := by
        intro x _
        have hxc : (x : G) ∈ L ⊓ centralizer ((O2In L : Subgroup G) : Set G) := by
          refine mem_inf.2 ⟨x.2, ?_⟩
          rw [mem_centralizer_iff]
          rintro _ ⟨q, hq', rfl⟩
          exact congrArg Subtype.val (mem_center_iff.1 (hb hq') x).symm
        obtain ⟨q, hq', hqx⟩ := hcon hxc
        have : q = x := Subtype.ext hqx
        exact this ▸ hq'
      have hall' : CFSG.pCore 2 ↥L = ⊤ := top_le_iff.1 hall
      have : IsPGroup 2 ↥L := by
        have := hQp
        rw [hall'] at this
        exact this.of_equiv Subgroup.topEquiv
      exact this.of_surjective (QuotientGroup.mk' (center ↥L)) (QuotientGroup.mk'_surjective _)
    · refine hQp.of_surjective ((QuotientGroup.mk' (center ↥L)).comp (CFSG.pCore 2 ↥L).subtype) ?_
      intro y
      have hy : y ∈ (CFSG.pCore 2 ↥L).map (QuotientGroup.mk' (center ↥L)) := by
        rw [ht]; exact mem_top y
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨⟨x, hx⟩, rfl⟩
  have := hs
  have hq2 : Nat.card (↥L ⧸ center ↥L) = 2 := card_eq_two_of_isPGroup_two hp
  have := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥L)
  rw [hq2, hZ] at this
  omega


section Constructor

variable [Finite G] {L : Subgroup G} {t z : G}


theorem Setting.exists_level55 (h : Setting G L t) (hc : CentralPair G L t z)
    (hCt : centralizer ({t} : Set G) = L) : Nonempty (Level55 G t z) := by
  have htL : t ∈ L := hc.ht
  have hzL : z ∈ L := hc.hz
  have hz2 : orderOf z = 2 := (Subgroup.orderOf_mk z hzL).symm.trans hc.loc.order_z
  have ht2 : orderOf t = 2 := (Subgroup.orderOf_mk t htL).symm.trans hc.loc.order_t
  have hzt : z * t = t * z := congrArg Subtype.val (mem_center_iff.1 hc.loc.central ⟨z, hzL⟩)
  have hK : centPair z t = L ⊓ centZ z := by
    ext g
    rw [mem_centPair_iff, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hgz, hgt⟩
      refine ⟨?_, hgz.symm⟩
      rw [← hCt]
      exact mem_centralizer_singleton_iff.2 hgt.symm
    · rintro ⟨hgL, hgz⟩
      refine ⟨hgz.symm, ?_⟩
      have : g ∈ centralizer ({t} : Set G) := hCt ▸ hgL
      exact (mem_centralizer_singleton_iff.1 this).symm
  obtain ⟨R₀, hR₀le, hR₀ext, hR₀card, hR₀cen, hR₀O2, hR₀disj, hR₀comm⟩ := hc.loc0.r0
  obtain ⟨S0, -, -, -, -, -, -, -, hquot⟩ := h.exists_kStructure hc
  have hO2map : (O2In (centralizer ({(⟨z, hzL⟩ : ↥L)} : Set ↥L))).map L.subtype =
      O2In (centPair z t) := by
    rw [hK]; exact map_O2In_centralizer_mk hzL
  have hCmap : (centralizer ({(⟨z, hzL⟩ : ↥L)} : Set ↥L)).map L.subtype = centPair z t := by
    rw [hK]; exact map_centralizer_mk_subtype hzL
  have hirr : ∀ W : Subgroup G, pair z t ≤ W → W ≤ O2In (centPair z t) →
      (∀ k ∈ centPair z t, ∀ w ∈ W, k * w * k⁻¹ ∈ W) →
        W = pair z t ∨ W = O2In (centPair z t) := by
    intro W hW1 hW2 hW3
    have hWL : W ≤ L := fun w hw => by
      have h1 := O2In_le _ (hW2 hw)
      rw [hK] at h1
      exact h1.1
    have hmc : (W.comap L.subtype).map L.subtype = W := by
      rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
      exact inf_eq_right.2 hWL
    have h1 : zpowers (⟨z, hzL⟩ : ↥L) ⊔ zpowers (⟨t, htL⟩ : ↥L) ≤ W.comap L.subtype := by
      refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
      · exact hW1 (z_mem_pair z t)
      · exact hW1 (t_mem_pair z t)
    have h2 : W.comap L.subtype ≤ O2In (centralizer ({(⟨z, hzL⟩ : ↥L)} : Set ↥L)) := by
      intro w hw
      have hw' : (w : G) ∈ O2In (centPair z t) := hW2 hw
      rw [← hO2map] at hw'
      obtain ⟨w', hw'1, hw'2⟩ := hw'
      have : w' = w := L.subtype_injective hw'2
      exact this ▸ hw'1
    have h3 : ∀ g ∈ centralizer ({(⟨z, hzL⟩ : ↥L)} : Set ↥L), ∀ w ∈ W.comap L.subtype,
        g * w * g⁻¹ ∈ W.comap L.subtype := by
      intro g hg w hw
      have hgK : (g : G) ∈ centPair z t := by
        rw [← hCmap]; exact ⟨g, hg, rfl⟩
      exact hW3 g hgK w hw
    rcases hc.loc0.irreducible _ h1 h2 h3 with h0 | h0
    · left
      rw [← hmc, h0, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      rfl
    · right
      rw [← hmc, h0, hO2map]
  have hcard : 4 < Nat.card L := by
    obtain ⟨e⟩ := hquot
    have hKL : centPair z t ≤ L := by rw [hK]; exact inf_le_left
    have h1 : Nat.card (centPair z t) ≤ Nat.card L := Subgroup.card_le_of_le hKL
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (CFSG.pCore 2 ↥(centPair z t))
    have hco : Nat.card (Carrier .Co2) = 42305421312000 := CFSG.Sporadic.Co2.card_Co2
    rw [Nat.card_congr e.toEquiv, hco] at h2
    have h3 : 0 < Nat.card (CFSG.pCore 2 ↥(centPair z t)) := Nat.card_pos
    omega
  refine ⟨{
    R0 := R₀.map L.subtype
    z_ord := hz2
    t_ord := ht2
    zt_comm := hzt
    R0_le := ?_
    R0_ext := ?_
    R0_card := ?_
    R0_center := ?_
    O2K := ?_
    t_not_mem := ?_
    t_mem_comm := ?_
    irred := hirr
    quot := hquot
    not_constrained := ?_ }⟩
  · rintro _ ⟨r, hr, rfl⟩
    rw [hK]
    refine ⟨r.2, mem_centralizer_singleton_iff.2 ?_⟩
    have := mem_centralizer_singleton_iff.1 (hR₀le hr)
    exact congrArg Subtype.val this
  · exact RankThree.PartOne.Torsion37.isExtraspecialPGroup_of_mulEquiv
      (R₀.equivMapOfInjective L.subtype L.subtype_injective) hR₀ext
  · rw [Subgroup.card_map_of_injective L.subtype_injective]; exact hR₀card
  · have := RankThree.PartOne.Torsion37.inSubgroup_center_map L.subtype L.subtype_injective R₀
    unfold inSubgroup at this
    rw [this, hR₀cen, MonoidHom.map_zpowers]
    rfl
  · rw [← hO2map, hR₀O2, Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  · rintro ⟨r, hr, hrt⟩
    have hrt' : r = ⟨t, htL⟩ := Subtype.ext hrt
    have h0 := Subgroup.disjoint_def.1 hR₀disj hr (hrt' ▸ mem_zpowers _)
    have : t = 1 := congrArg Subtype.val (hrt'.symm.trans h0)
    rw [this, orderOf_one] at ht2
    omega
  · have := Subgroup.mem_map_of_mem L.subtype hR₀comm
    rw [Subgroup.map_commutator, hCmap] at this
    exact this
  · rw [hCt]
    exact not_isTwoConstrained_of_simple_quotient h.std.standard.1.2 h.card_center hcard

end Constructor

end CFSG.EvenSporadicStandard.TwoB
