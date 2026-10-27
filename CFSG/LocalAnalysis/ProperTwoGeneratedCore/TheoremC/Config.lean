module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOneQuotient

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {X : Type} [Group X] [Finite X]

section TwoCore

variable (X) in
omit [Finite X] in
theorem twoCore_eq_sSup : CFSG.Open.pCore 2 X =
    sSup {N : Subgroup X | N.Normal ∧ IsPGroup 2 N} :=
  rfl

omit [Finite X] in
instance twoCore_normal : (CFSG.Open.pCore 2 X).Normal := by
  rw [twoCore_eq_sSup]
  exact Subgroup.sSup_normal _ fun _ hN => hN.1

variable (X) in
omit [Finite X] in
theorem twoCore_isPGroup : IsPGroup 2 (CFSG.Open.pCore 2 X) := by
  rw [twoCore_eq_sSup]
  exact Sylow.sSup_of_normal _ (fun _ hN => hN.2) (fun _ hN => hN.1)

omit [Finite X] in
theorem le_twoCore {N : Subgroup X} (hN : N.Normal) (hp : IsPGroup 2 N) :
    N ≤ CFSG.Open.pCore 2 X := by
  rw [twoCore_eq_sSup]
  exact le_sSup ⟨hN, hp⟩

end TwoCore

structure CoreConfig (Y : Subgroup X) (u z : X) : Prop where
  oddCore_eq_bot : pPrimeCore 2 X = ⊥
  center : u ∈ Subgroup.center X
  order : orderOf u = 2
  ne_top : Y ≠ ⊤
  sylow : ∃ P : Sylow 2 X, (P : Subgroup X) ≤ Y ∧
    properTwoGenCoreGamma (P : Subgroup X) 2 ≤ Y ∧ z ∈ (P : Subgroup X) ∧
      ∀ p ∈ (P : Subgroup X), Commute p z
  rank : 3 ≤ twoRank X
  lever_order : orderOf z = 2
  lever_ne : z ≠ u

namespace CoreConfig

variable {Y : Subgroup X} {u z : X}

theorem commute_center (hc : CoreConfig Y u z) (y : X) : Commute y u :=
  Subgroup.mem_center_iff.mp hc.center y

theorem lever_mem (hc : CoreConfig Y u z) : z ∈ Y := by
  obtain ⟨P, hPY, -, hzP, -⟩ := hc.sylow
  exact hPY hzP

theorem center_mem (hc : CoreConfig Y u z) : u ∈ Y := by
  obtain ⟨P, hPY, -, -, -⟩ := hc.sylow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : (Subgroup.zpowers u).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [((hc.commute_center g).zpow_right k).eq, mul_inv_cancel_right]
    exact hn
  have hp : IsPGroup 2 (Subgroup.zpowers u) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hc.order, pow_one]
  exact hPY (hp.le_sylow_of_normal P (Subgroup.mem_zpowers u))

theorem normalizer_le (hc : CoreConfig Y u z) (D : Subgroup X) (hDY : D ≤ Y)
    (hD : 2 ≤ CFSG.Open.pRank 2 D) : Subgroup.normalizer (D : Set X) ≤ Y := by
  obtain ⟨P, hPY, hcore, -, -⟩ := hc.sylow
  exact two_generated_core_subgroup_normalizer_le P Y hPY hcore D hDY hD

theorem centralizer_le (hc : CoreConfig Y u z) (D : Subgroup X) (hDY : D ≤ Y)
    (hD : 2 ≤ CFSG.Open.pRank 2 D) : Subgroup.centralizer (D : Set X) ≤ Y :=
  (Subgroup.centralizer_le_normalizer _).trans (hc.normalizer_le D hDY hD)

theorem involution_centralizer_le (hc : CoreConfig Y u z) {y : X} (hyY : y ∈ Y)
    (hy : orderOf y = 2) (hne : y ≠ u) : Subgroup.centralizer ({y} : Set X) ≤ Y := by
  set D := Subgroup.closure ({y, u} : Set X) with hD
  have hyD : y ∈ D := Subgroup.subset_closure (Set.mem_insert _ _)
  have huD : u ∈ D := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hDY : D ≤ Y := by
    rw [hD, Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact hyY
    · exact hc.center_mem
  have hrank : 2 ≤ CFSG.Open.pRank 2 D :=
    two_le_pRank_of_commuting_involutions hyD huD hy hc.order hne (hc.commute_center y)
  refine le_trans ?_ (hc.centralizer_le D hDY hrank)
  intro c hc'
  rw [hD, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro w (rfl | rfl)
  · exact (Subgroup.mem_centralizer_singleton_iff.mp hc').symm
  · exact (hc.commute_center c).eq.symm

theorem lever_centralizer_le (hc : CoreConfig Y u z) :
    Subgroup.centralizer ({z} : Set X) ≤ Y :=
  hc.involution_centralizer_le hc.lever_mem hc.lever_order hc.lever_ne

theorem eq_of_mem_inf_conj (hc : CoreConfig Y u z) {m y : X} (hm : m ∉ Y)
    (hy : y ∈ Y ⊓ Y.conjBy m⁻¹) (hy2 : orderOf y = 2) : y = u := by
  obtain ⟨P, hPY, hcore, -, -⟩ := hc.sylow
  by_contra hne
  have hlt := conjugate_intersection_rank_lt P Y (k := 2) (by decide) hPY hcore m hm
  have hu : u ∈ Y ⊓ Y.conjBy m⁻¹ := by
    refine ⟨hc.center_mem, Subgroup.mem_map.mpr ⟨u, hc.center_mem, ?_⟩⟩
    change m⁻¹ * u * m⁻¹⁻¹ = u
    rw [inv_inv, (hc.commute_center m⁻¹).eq, mul_assoc, inv_mul_cancel, mul_one]
  have h2 := two_le_pRank_of_commuting_involutions hy hu hy2 hc.order hne
    (hc.commute_center y)
  omega

theorem eq_of_conj_mem (hc : CoreConfig Y u z) {m y : X} (hm : m ∉ Y) (hy : y ∈ Y)
    (hym : m * y * m⁻¹ ∈ Y) (hy2 : orderOf y = 2) : y = u := by
  refine hc.eq_of_mem_inf_conj hm ⟨hy, Subgroup.mem_map.mpr ⟨_, hym, ?_⟩⟩ hy2
  change m⁻¹ * (m * y * m⁻¹) * m⁻¹⁻¹ = y
  group

theorem mem_of_conj_mem (hc : CoreConfig Y u z) {m y : X} (hy : y ∈ Y) (hy2 : orderOf y = 2)
    (hne : y ≠ u) (hym : m⁻¹ * y * m ∈ Y) : m ∈ Y := by
  by_contra hm
  have hm' : m⁻¹ ∉ Y := fun h => hm (by simpa using Y.inv_mem h)
  exact hne (hc.eq_of_conj_mem hm' hy (by simpa using hym) hy2)

end CoreConfig

section Escaping

variable {G : Type} [Group G] [Finite G] {H : Subgroup G} {x : G}

theorem coreConfig_escaping (hq : EscapingQuotientData H x) {zb : EscapingQuotient x}
    {U : Sylow 2 (EscapingQuotient x)} (hUH : (U : Subgroup (EscapingQuotient x)) ≤ escapingImage H x)
    (hcore : properTwoGenCoreGamma (U : Subgroup (EscapingQuotient x)) 2 ≤ escapingImage H x)
    (hzU : zb ∈ (U : Subgroup (EscapingQuotient x)))
    (hzc : ∀ p ∈ (U : Subgroup (EscapingQuotient x)), Commute p zb) (hz : orderOf zb = 2)
    (hne : zb ≠ escapingBar x) : CoreConfig (escapingImage H x) (escapingBar x) zb :=
  ⟨hq.oddCore_eq_bot, hq.bar_mem_center, hq.bar_order, hq.image_ne_top,
    ⟨U, hUH, hcore, hzU, hzc⟩, hq.rank, hz, hne⟩

end Escaping

end CFSG.ProperTwoGeneratedCore.TheoremC
