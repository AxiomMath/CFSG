module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionStructure
import CFSG.RankThree.PartOne.S9.Planes.SecondCenter
import CFSG.GroupTheory.SteinbergBKOddNoncyclicRankTwo
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.RankThree.PartOne.Planes Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_not_mem_commutator_mem {p : ℕ} [Fact p.Prime] {P D Z : Subgroup G}
    (hP : IsPGroup p P) (hDP : D ≤ P) (hZD : Z ≤ D) (hZne : Z ≠ D)
    (hPD : P ≤ normalizer (D : Set G)) (hPZ : P ≤ normalizer (Z : Set G)) :
    ∃ u ∈ D, u ∉ Z ∧ ∀ g ∈ P, g * u * g⁻¹ * u⁻¹ ∈ Z := by
  classical
  have hZP : Z ≤ P := hZD.trans hDP
  have hZt : (Z.subgroupOf P).Normal := (normal_subgroupOf_iff_le_normalizer hZP).2 hPZ
  have hDt : (D.subgroupOf P).Normal := (normal_subgroupOf_iff_le_normalizer hDP).2 hPD
  have hQ : IsPGroup p (P ⧸ Z.subgroupOf P) := hP.to_quotient _
  have : Group.IsNilpotent (P ⧸ Z.subgroupOf P) := hQ.isNilpotent
  set π := QuotientGroup.mk' (Z.subgroupOf P) with hπ
  have hHn : ((D.subgroupOf P).map π).Normal := hDt.map π (QuotientGroup.mk'_surjective _)
  have hHne : (D.subgroupOf P).map π ≠ ⊥ := by
    obtain ⟨d, hdD, hdZ⟩ : ∃ d ∈ D, d ∉ Z := by
      by_contra h
      push Not at h
      exact hZne (le_antisymm hZD h)
    intro hH
    have hmem : π ⟨d, hDP hdD⟩ ∈ (D.subgroupOf P).map π :=
      mem_map_of_mem π (show (⟨d, hDP hdD⟩ : P) ∈ D.subgroupOf P from hdD)
    rw [hH, mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact hdZ hmem
  obtain ⟨⟨q, hq⟩, hq1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hHne)
  obtain ⟨hqH, hqZ⟩ := mem_inf.mp hq
  obtain ⟨n, hnD, rfl⟩ := mem_map.mp hqH
  refine ⟨(n : G), hnD, ?_, ?_⟩
  · intro hnZ
    apply hq1
    apply Subtype.ext
    change π n = 1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hnZ
  · intro g hg
    have hc := mem_center_iff.mp hqZ (π ⟨g, hg⟩)
    have h1 : π (⟨g, hg⟩ * n * ⟨g, hg⟩⁻¹ * n⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    simpa [mem_subgroupOf] using h1

theorem ExtremalObstruction.pow_eq_one_and_commutator_mem {p : ℕ} {P : Sylow p G}
    {M D : Subgroup G} (hext : ExtremalObstruction p P M D) (hp : p.Prime) (hp2 : p ≠ 2) :
    (∀ x ∈ D, x ^ p = 1) ∧
      ∀ x ∈ D, ∀ y ∈ D, x * y * x⁻¹ * y⁻¹ ∈ centralizer (D : Set G) := by
  classical
  have hfact : Fact p.Prime := ⟨hp⟩
  have hDP : D ≤ P := hext.obstruction.2.1
  have hDp : IsPGroup p D := P.isPGroup'.to_le hDP
  obtain ⟨hchar, hmem, hcomm, hnc⟩ :=
    CFSG.RankThree.PartOne.pgOddSecondCenterPrimeTorsion D p hp hp2 hDp
  set W : Subgroup D :=
    closure {x : D | x ∈ Subgroup.upperCentralSeries D 2 ∧ x ^ p = 1} with hW
  have hDnc : ¬ IsCyclic D := by
    intro hcyc
    obtain ⟨E, hED, hE, hEc⟩ := pRank_attained p D (by rw [hext.rank_eq]; norm_num)
    rw [hext.rank_eq] at hEc
    have : CFSG.IsElementaryAbelian p E :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).2 hE
    apply CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hEc
    exact isCyclic_of_surjective (subgroupOfEquivOfLe hED).toMonoidHom
      (subgroupOfEquivOfLe hED).surjective
  set W' : Subgroup G := W.map D.subtype with hW'
  have hW'D : W' ≤ D := map_subtype_le W
  have hN : normalizer (D : Set G) ≤ normalizer (W' : Set G) :=
    normalizer_le_normalizer_characteristic_map D W hchar
  have h2 : 2 ≤ CFSG.Open.pRank p W' := by
    have hW'p : IsPGroup p W' := hDp.to_le hW'D
    have hW'nc : ¬ IsCyclic W' := by
      intro hcyc
      apply hnc hDnc
      let e := W.equivMapOfInjective D.subtype D.subtype_injective
      exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
    obtain ⟨B, hB, hBc⟩ := CFSG.GroupTheory.SteinbergBK.odd_noncyclic_pgroup_rank_two
      (hp.odd_of_ne_two hp2) hW'p hW'nc
    have hBe : CFSG.IsElementaryAbelian p (B.map W'.subtype) :=
      CFSG.IsElementaryAbelian.map_subtype
    unfold CFSG.Open.pRank
    refine le_csSup (pRank_set_bddAbove p hp.one_lt _) ⟨B.map W'.subtype, map_subtype_le B,
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1 hBe, ?_⟩
    rw [card_map_of_injective W'.subtype_injective, hBc]
  have heq : W' = D := hext.minimal W' hW'D h2 hN
  have hmemW : ∀ x (hx : x ∈ D), (⟨x, hx⟩ : D) ∈ W := by
    intro x hx
    have hxW' : x ∈ W' := heq.symm ▸ hx
    obtain ⟨w, hw, hwx⟩ := mem_map.mp hxW'
    have hwe : w = ⟨x, hx⟩ := Subtype.ext hwx
    exact hwe ▸ hw
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · have h := congrArg Subtype.val ((hmem _).1 (hmemW x hx)).2
    simpa using h
  · obtain ⟨hc, -⟩ := hcomm _ (hmemW x hx) ⟨y, hy⟩
    rw [mem_centralizer_iff]
    intro d hd
    have h := congrArg Subtype.val (mem_center_iff.mp hc ⟨d, hd⟩)
    simpa [commutatorElement_def, mul_assoc] using h

omit [Finite G] in
theorem mul_comm_of_mem_center_map {D : Subgroup G} {z : G}
    (hz : z ∈ (center D).map D.subtype) {d : G} (hd : d ∈ D) : d * z = z * d := by
  obtain ⟨c, hc, rfl⟩ := mem_map.mp hz
  exact congrArg Subtype.val (mem_center_iff.mp hc ⟨d, hd⟩)

theorem ExtremalObstruction.card_center_eq {p : ℕ} {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hp : p.Prime) (hp2 : p ≠ 2)
    (hD : ¬ IsMulCommutative D) : Nat.card ((center D).map D.subtype) = p := by
  classical
  have hfact : Fact p.Prime := ⟨hp⟩
  have hpow := (hext.pow_eq_one_and_commutator_mem hp hp2).1
  set Z : Subgroup G := (center D).map D.subtype with hZ
  have hZD : Z ≤ D := map_subtype_le _
  have hZe : IsElemAbelian p Z := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun z hz => hpow z (hZD hz)⟩
    exact mul_comm_of_mem_center_map b.2 (hZD a.2)
  have hrank : CFSG.Open.pRank p Z ≤ 1 := by
    by_contra h
    push Not at h
    have hZeq := hext.minimal Z hZD h
      (normalizer_le_normalizer_characteristic_map D (center D) inferInstance)
    apply hD
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have hb : (b : G) ∈ Z := hZeq.symm ▸ b.2
    exact mul_comm_of_mem_center_map hb a.2
  obtain ⟨k, hk⟩ := (elementary_isPGroup p Z hZe).exists_card_eq
  have hkle : k ≤ CFSG.Open.pRank p Z := by
    unfold CFSG.Open.pRank
    exact le_csSup (pRank_set_bddAbove p hp.one_lt _) ⟨Z, le_rfl, hZe, hk⟩
  have hDnt : Nontrivial D := by
    obtain ⟨E, hED, -, hEc⟩ := pRank_attained p D (by rw [hext.rank_eq]; norm_num)
    have hE1 : 1 < Nat.card E := by
      rw [hEc]
      exact Nat.one_lt_pow (by rw [hext.rank_eq]; norm_num) hp.one_lt
    have hEbot : E ≠ ⊥ := (one_lt_card_iff_ne_bot E).1 hE1
    exact (nontrivial_iff_ne_bot D).2 fun h => hEbot (le_bot_iff.1 (h ▸ hED))
  have hZnt : Nontrivial (center D) := (P.isPGroup'.to_le hext.obstruction.2.1).center_nontrivial
  have hcardZ : Nat.card Z = Nat.card (center D) := card_map_of_injective D.subtype_injective
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, hcardZ] at hk
    exact (Finite.one_lt_card_iff_nontrivial.mpr hZnt).ne' hk
  rw [hk, show k = 1 by omega, pow_one]

theorem ExtremalObstruction.exists_normal_plane (hS : Setting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : (P : Subgroup G) ≤ normalizer (D : Set G)) :
    ¬ IsMulCommutative D ∧ ∃ U : Subgroup G, U < D ∧
      (P : Subgroup G) ≤ normalizer (U : Set G) ∧ IsElemAbelian p U ∧ Nat.card U = p ^ 2 ∧
      3 ≤ CFSG.Open.pRank p ((P : Subgroup G) ⊓ centralizer (U : Set G)) ∧
      normalizer (U : Set G) ≤ M := by
  classical
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hM, hDP, -, -⟩ := hext.obstruction
  have hPp : IsPGroup p (P : Subgroup G) := P.isPGroup'
  have hP3 := (sylow_le_of_isCoreMaxLocal hS hp hM).2
  obtain ⟨A, hAP, hA, hAc⟩ := pRank_attained p (P : Subgroup G) (by rw [hP3]; norm_num)
  rw [hP3] at hAc
  have hA' : CFSG.IsElementaryAbelian p A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).2 hA
  have hDna : ¬ IsMulCommutative D := fun hD =>
    (isolatedPlane_structure hprime hPp (hext.isIsolatedPlane_of_isMulCommutative hprime hD) hAP
      hA' hAc).1 hPD
  refine ⟨hDna, ?_⟩
  have hpow := (hext.pow_eq_one_and_commutator_mem hprime hodd).1
  set Z : Subgroup G := (center D).map D.subtype with hZ
  have hZD : Z ≤ D := map_subtype_le _
  have hZc : Nat.card Z = p := hext.card_center_eq hprime hodd hDna
  have hZne : Z ≠ D := by
    intro h
    apply hDna
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have hb : (b : G) ∈ Z := h.symm ▸ b.2
    exact mul_comm_of_mem_center_map hb a.2
  have hPZ : (P : Subgroup G) ≤ normalizer (Z : Set G) :=
    hPD.trans (normalizer_le_normalizer_characteristic_map D (center D) inferInstance)
  obtain ⟨u, huD, huZ, hu⟩ := exists_mem_not_mem_commutator_mem hPp hDP hZD hZne hPD hPZ
  set U : Subgroup G := Z ⊔ zpowers u with hU
  have hup : u ^ p = 1 := hpow u huD
  have hcommu : ∀ z ∈ Z, z * u = u * z := fun z hz => (mul_comm_of_mem_center_map hz huD).symm
  have hUc : Nat.card U = p ^ 2 := by
    rw [hU, card_sup_zpowers hprime Z hup huZ hcommu, hZc, pow_two]
  have hUD : U ≤ D := sup_le hZD (zpowers_le.mpr huD)
  have hUP : U ≤ P := hUD.trans hDP
  have hZe' : CFSG.IsElementaryAbelian p Z := by
    refine (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p Z).2
      ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun z hz => hpow z (hZD hz)⟩
    exact mul_comm_of_mem_center_map b.2 (hZD a.2)
  have hue : CFSG.IsElementaryAbelian p (zpowers u) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hup
  have hUe' : CFSG.IsElementaryAbelian p U :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer
      (zpowers_le.mpr (mem_centralizer_iff.mpr fun z hz => hcommu z hz))
  have hUe : IsElemAbelian p U :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p U).1 hUe'
  have hUlt : U < D := lt_of_le_of_ne hUD fun h => hDna (h ▸ hUe.1)
  have hPU : (P : Subgroup G) ≤ normalizer (U : Set G) := by
    intro g hg
    have hle : U.map (MulAut.conj g).toMonoidHom ≤ U := by
      rw [map_le_iff_le_comap]
      refine sup_le (fun z hz => mem_sup_left ((mem_normalizer_iff.mp (hPZ hg) z).mp hz)) ?_
      rw [zpowers_le]
      change g * u * g⁻¹ ∈ U
      have h1 : g * u * g⁻¹ = (g * u * g⁻¹ * u⁻¹) * u := by group
      rw [h1]
      exact mul_mem (mem_sup_left (hu g hg)) (mem_sup_right (mem_zpowers u))
    exact mem_normalizer_iff_map_conj_eq.mpr
      (Subgroup.eq_of_le_of_card_ge hle (card_map_of_injective (MulAut.conj g).injective).ge)
  obtain ⟨-, hbig⟩ := normalPlane_concrete hprime hPp hUP hPU hUe' hUc hAP hA' hAc
  have hFe' : CFSG.IsElementaryAbelian p ↥((A ⊓ centralizer (U : Set G)) ⊔ U) := by
    have : CFSG.IsElementaryAbelian p ↥(A ⊓ centralizer (U : Set G)) :=
      isElementaryAbelian_of_le inf_le_left hA'
    have hle : U ≤ centralizer ((A ⊓ centralizer (U : Set G) : Subgroup G) : Set G) := by
      intro v hv
      exact mem_centralizer_iff.2 fun x hx => (mem_centralizer_iff.1 hx.2 v hv).symm
    exact CFSG.IsElementaryAbelian.sup_of_le_centralizer hle
  have hFle : (A ⊓ centralizer (U : Set G)) ⊔ U ≤ (P : Subgroup G) ⊓ centralizer (U : Set G) :=
    sup_le (inf_le_inf_right _ hAP) (le_inf hUP (le_centralizer_iff_isMulCommutative.mpr hUe.1))
  have h3 : 3 ≤ CFSG.Open.pRank p ((P : Subgroup G) ⊓ centralizer (U : Set G)) := by
    obtain ⟨k, hk⟩ :=
      (CFSG.IsElementaryAbelian.isPGroup p ↥((A ⊓ centralizer (U : Set G)) ⊔ U)).exists_card_eq
    have hk3 : 3 ≤ k := by
      rw [hk] at hbig
      exact (Nat.pow_le_pow_iff_right hprime.one_lt).1 hbig
    unfold CFSG.Open.pRank
    exact hk3.trans (le_csSup (pRank_set_bddAbove p hprime.one_lt _) ⟨_, hFle,
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1 hFe', hk⟩)
  refine ⟨U, hUlt, hPU, hUe, hUc, h3, ?_⟩
  have hU2 : 2 ≤ CFSG.Open.pRank p U := by
    unfold CFSG.Open.pRank
    exact le_csSup (pRank_set_bddAbove p hprime.one_lt _) ⟨U, le_rfl, hUe, hUc⟩
  exact (aschCore_normalizer_le 2 p (P : Subgroup G) U hUP hU2
    (h3.trans (pRank_mono p hprime.one_lt le_sup_right))).trans hM.2

theorem ExtremalObstruction.normalizer_le_of_normal {p : ℕ} {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    {R : Subgroup G} (hRP : R ≤ P) (hPR : (P : Subgroup G) ≤ normalizer (R : Set G))
    (hR : 2 ≤ CFSG.Open.pRank p R) : normalizer (R : Set G) ≤ M := by
  by_contra hRM
  have hle := hext.maximal P M R ⟨hext.obstruction.1, hRP, hR, hRM⟩
  rw [inf_eq_left.mpr hPR] at hle
  have hlt : (P : Subgroup G) ⊓ normalizer (D : Set G) < P :=
    lt_of_le_of_ne inf_le_left fun h => hPD (h ▸ inf_le_right)
  exact absurd hle (not_le.mpr (Subgroup.card_lt_of_lt hlt))

end CFSG.LocalAnalysis.RankThreeTheoremC
