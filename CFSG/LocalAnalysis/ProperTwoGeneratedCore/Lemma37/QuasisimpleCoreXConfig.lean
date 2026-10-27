module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.Config

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {X : Type} [Group X] [Finite X]

structure BaseConfig (Y : Subgroup X) (e : X) : Prop where
  oddCore_eq_bot : pPrimeCore 2 X = ⊥
  center : e ∈ Subgroup.center X
  order : orderOf e = 2
  ne_top : Y ≠ ⊤
  sylow : ∃ P : Sylow 2 X, (P : Subgroup X) ≤ Y ∧ properTwoGenCoreGamma (P : Subgroup X) 2 ≤ Y

namespace BaseConfig

variable {Y : Subgroup X} {e : X}

theorem commute_center (hc : BaseConfig Y e) (y : X) : Commute y e :=
  Subgroup.mem_center_iff.mp hc.center y

theorem mul_self (hc : BaseConfig Y e) : e * e = 1 := by
  rw [← pow_two, ← hc.order, pow_orderOf_eq_one]

theorem zpowers_normal (hc : BaseConfig Y e) : (Subgroup.zpowers e).Normal :=
  Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hc.center)

theorem mem_sylow (hc : BaseConfig Y e) (P : Sylow 2 X) : e ∈ (P : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hc.zpowers_normal
  exact (isPGroup_zpowers_of_orderOf_eq_two hc.order).le_sylow_of_normal P
    (Subgroup.mem_zpowers e)

theorem center_mem (hc : BaseConfig Y e) : e ∈ Y := by
  obtain ⟨P, hPY, -⟩ := hc.sylow
  exact hPY (hc.mem_sylow P)

theorem normalizer_le (hc : BaseConfig Y e) (D : Subgroup X) (hDY : D ≤ Y)
    (hD : 2 ≤ CFSG.Open.pRank 2 D) : Subgroup.normalizer (D : Set X) ≤ Y := by
  obtain ⟨P, hPY, hcore⟩ := hc.sylow
  exact two_generated_core_subgroup_normalizer_le P Y hPY hcore D hDY hD

theorem centralizer_le (hc : BaseConfig Y e) (D : Subgroup X) (hDY : D ≤ Y)
    (hD : 2 ≤ CFSG.Open.pRank 2 D) : Subgroup.centralizer (D : Set X) ≤ Y :=
  (Subgroup.centralizer_le_normalizer _).trans (hc.normalizer_le D hDY hD)

theorem le_of_two_le_pRank_inf (hc : BaseConfig Y e) {D : Subgroup X} (hD : IsPGroup 2 D)
    (hrank : 2 ≤ CFSG.Open.pRank 2 (D ⊓ Y)) : D ≤ Y := by
  obtain ⟨P, hPY, hcore⟩ := hc.sylow
  exact pGroup_le_of_large_intersection P Y 2 hPY hcore D hD hrank

theorem involution_centralizer_le (hc : BaseConfig Y e) {t : X} (htY : t ∈ Y)
    (ht : orderOf t = 2) (hne : t ≠ e) : Subgroup.centralizer ({t} : Set X) ≤ Y := by
  set D := Subgroup.closure ({t, e} : Set X) with hD
  have htD : t ∈ D := Subgroup.subset_closure (Set.mem_insert _ _)
  have heD : e ∈ D := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hDY : D ≤ Y := by
    rw [hD, Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact htY
    · exact hc.center_mem
  have hrank : 2 ≤ CFSG.Open.pRank 2 D :=
    two_le_pRank_of_commuting_involutions htD heD ht hc.order hne (hc.commute_center t)
  refine le_trans ?_ (hc.centralizer_le D hDY hrank)
  intro c hc'
  rw [hD, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro w (rfl | rfl)
  · exact (Subgroup.mem_centralizer_singleton_iff.mp hc').symm
  · exact (hc.commute_center c).eq.symm

theorem eq_of_mem_inf_conj (hc : BaseConfig Y e) {m t : X} (hm : m ∉ Y)
    (ht : t ∈ Y ⊓ Y.conjBy m⁻¹) (ht2 : orderOf t = 2) : t = e := by
  obtain ⟨P, hPY, hcore⟩ := hc.sylow
  by_contra hne
  have hlt := conjugate_intersection_rank_lt P Y (k := 2) (by decide) hPY hcore m hm
  have he : e ∈ Y ⊓ Y.conjBy m⁻¹ := by
    refine ⟨hc.center_mem, Subgroup.mem_map.mpr ⟨e, hc.center_mem, ?_⟩⟩
    change m⁻¹ * e * m⁻¹⁻¹ = e
    rw [inv_inv, (hc.commute_center m⁻¹).eq, mul_assoc, inv_mul_cancel, mul_one]
  have h2 := two_le_pRank_of_commuting_involutions ht he ht2 hc.order hne
    (hc.commute_center t)
  omega

theorem eq_of_conj_mem (hc : BaseConfig Y e) {m t : X} (hm : m ∉ Y) (ht : t ∈ Y)
    (htm : m * t * m⁻¹ ∈ Y) (ht2 : orderOf t = 2) : t = e := by
  refine hc.eq_of_mem_inf_conj hm ⟨ht, Subgroup.mem_map.mpr ⟨_, htm, ?_⟩⟩ ht2
  change m⁻¹ * (m * t * m⁻¹) * m⁻¹⁻¹ = t
  group

theorem mem_of_conj_mem (hc : BaseConfig Y e) {m t : X} (ht : t ∈ Y) (ht2 : orderOf t = 2)
    (hne : t ≠ e) (htm : m⁻¹ * t * m ∈ Y) : m ∈ Y := by
  by_contra hm
  have hm' : m⁻¹ ∉ Y := fun h => hm (by simpa using Y.inv_mem h)
  exact hne (hc.eq_of_conj_mem hm' ht (by simpa using htm) ht2)

theorem exists_conj_mem (hc : BaseConfig Y e) {t : X} (ht : orderOf t = 2) :
    ∃ g : X, g⁻¹ * t * g ∈ Y := by
  obtain ⟨P, hPY, -⟩ := hc.sylow
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow P (isPGroup_zpowers_of_orderOf_eq_two ht)
  exact ⟨g, hPY (hg t (Subgroup.mem_zpowers t))⟩

theorem mem_twoCore (hc : BaseConfig Y e) : e ∈ CFSG.Open.pCore 2 X := by
  have := hc.zpowers_normal
  exact TheoremC.le_twoCore hc.zpowers_normal (isPGroup_zpowers_of_orderOf_eq_two hc.order)
    (Subgroup.mem_zpowers e)

omit [Finite X] in
theorem twoCore_le_sylow (P : Sylow 2 X) : CFSG.Open.pCore 2 X ≤ (P : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (TheoremC.twoCore_isPGroup X).le_sylow_of_normal P

theorem twoCore_le (hc : BaseConfig Y e) : CFSG.Open.pCore 2 X ≤ Y := by
  obtain ⟨P, hPY, -⟩ := hc.sylow
  exact (twoCore_le_sylow P).trans hPY

theorem twoCore_pRank (hc : BaseConfig Y e) :
    CFSG.Open.pRank 2 (CFSG.Open.pCore 2 X) = 1 := by
  have hle : CFSG.Open.pRank 2 (CFSG.Open.pCore 2 X) ≤ 1 := by
    by_contra h
    have hN := hc.normalizer_le _ hc.twoCore_le (by omega)
    rw [Subgroup.normalizer_eq_top] at hN
    exact hc.ne_top (top_le_iff.mp hN)
  have hge : 1 ≤ CFSG.Open.pRank 2 (CFSG.Open.pCore 2 X) :=
    CFSG.SectionRank.le_pRank (by decide) (Subgroup.zpowers_le.mpr hc.mem_twoCore)
      (involution_zpowers_elementary e hc.order) (by rw [Nat.card_zpowers, hc.order, pow_one])
  omega

theorem eq_of_mem_twoCore (hc : BaseConfig Y e) {w : X} (hw : w ∈ CFSG.Open.pCore 2 X)
    (hw2 : orderOf w = 2) : w = e := by
  by_contra hne
  have h := two_le_pRank_of_commuting_involutions hw hc.mem_twoCore hw2 hc.order hne
    (hc.commute_center w)
  have := hc.twoCore_pRank
  omega

theorem mem_pCore (hc : BaseConfig Y e) : e ∈ CFSG.pCore 2 X := by
  exact hc.mem_twoCore

theorem pCore_pRank (hc : BaseConfig Y e) : CFSG.Open.pRank 2 (CFSG.pCore 2 X) = 1 := by
  exact hc.twoCore_pRank

theorem twoCore_le_inf_conj (hc : BaseConfig Y e) (m : X) :
    CFSG.Open.pCore 2 X ≤ Y ⊓ Y.conjBy m⁻¹ := by
  refine le_inf hc.twoCore_le fun w hw => Subgroup.mem_map.mpr ⟨m * w * m⁻¹, ?_, ?_⟩
  · exact hc.twoCore_le ((TheoremC.twoCore_normal (X := X)).conj_mem w hw m)
  · change m⁻¹ * (m * w * m⁻¹) * m⁻¹⁻¹ = w
    group

end BaseConfig

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
