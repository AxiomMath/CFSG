module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Plane
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627ClauseB
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankCase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem largerPrimesUnique_three (hS : Setting G) (h3 : 3 ∈ rankThreeSigmaA G) :
    LargerPrimesUnique G 3 :=
  fun _ hf hlt => absurd (eq_three_of_three_mem_sigmaA hS.rank h3 hf) (by omega)

theorem clauseC_of_uniquenessAt (hS : Setting G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (hΓ : ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M)
    (hempty : ∀ y : G, ¬ IsLargeObstruction p M y) (hU : UniquenessAt G p P M) :
    p = 3 ∧ rankThreeClauseC M (P : Subgroup G) := by
  rcases hU.1 with h | h | h
  · exact absurd h hΓ
  · obtain ⟨y, hy⟩ := exists_isLargeObstruction_of_clauseB hS hp hM h
    exact absurd hy (hempty y)
  · exact h

theorem smallPrimeThree_of_prop627 (hS : Setting G) (hU0 : FullCoreLocal G)
    (h627 : GL83SmallRankProp627 G) : GL83SmallRankPrimeThree G := by
  intro p hp P M hM hΓ hempty hIH
  by_cases hU : UniquenessAt G p P M
  · exact (clauseC_of_uniquenessAt hS hp hM hΓ hempty hU).1
  · exact h627.eq_three ⟨hp, hM, hU0 p hp P M hM, hΓ, hempty, hIH, hU⟩

theorem smallStructure_of_prop632 (hS : Setting G) (hU0 : FullCoreLocal G)
    (h632 : GL83SmallRankProp632 G) : GL83SmallRankStructure G := by
  intro h3 P M hM hΓ hempty
  by_cases hU : UniquenessAt G 3 P M
  · obtain ⟨-, hC⟩ := clauseC_of_uniquenessAt hS h3 hM hΓ hempty hU
    exact ⟨hC.1, hC.2.1⟩
  · exact h632 P M ⟨h3, hM, hU0 3 h3 P M hM, hΓ, hempty, largerPrimesUnique_three hS h3, hU⟩

omit [Finite G] in
theorem one_le_of_rankThreeIsQ8CentralCyclic {H : Subgroup G} {m : ℕ}
    (h : rankThreeIsQ8CentralCyclic H m) : 1 ≤ m := by
  obtain ⟨A, B, -, -, hB, -, -, hAB⟩ := h
  by_contra hm
  have hm0 : m = 0 := by omega
  rw [hm0, pow_zero] at hB
  have hbot : B = ⊥ := Subgroup.card_eq_one.mp hB
  rw [hbot, inf_bot_eq, Subgroup.card_bot] at hAB
  omega

omit [Finite G] in
theorem map_inf_centralizer_zpowers {T : Subgroup G} {g : G} (hgT : g ∈ normalizer (T : Set G))
    (x : G) :
    (T ⊓ centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
      T ⊓ centralizer (((zpowers x).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  ext w
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [Subgroup.mem_inf] at hv
    obtain ⟨hvT, hvx⟩ := hv
    refine ⟨?_, ?_⟩
    · exact (mem_normalizer_iff.mp hgT v).mp hvT
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨a, ha, rfl⟩
      have hva : v * a = a * v := by
        have hc : Commute v x := mem_centralizer_singleton_iff.mp hvx
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
        exact (hc.zpow_right k).eq
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * a * g⁻¹ * (g * v * g⁻¹) = g * (a * v) * g⁻¹ := by group
        _ = g * (v * a) * g⁻¹ := by rw [hva]
        _ = g * v * g⁻¹ * (g * a * g⁻¹) := by group
  · rintro ⟨hwT, hwC⟩
    refine ⟨g⁻¹ * w * g, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · exact (mem_normalizer_iff.mp hgT (g⁻¹ * w * g)).mpr (by simpa [mul_assoc] using hwT)
    · rw [mem_centralizer_singleton_iff]
      have hx : g * x * g⁻¹ ∈ ((zpowers x).map (MulAut.conj g).toMonoidHom : Subgroup G) :=
        ⟨x, mem_zpowers x, by simp [MulAut.conj_apply]⟩
      have := Subgroup.mem_centralizer_iff.mp hwC _ hx
      calc g⁻¹ * w * g * x = g⁻¹ * (w * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * w) * g := by rw [this]
        _ = x * (g⁻¹ * w * g) := by group

theorem exists_zpowers_eq_of_card_eq_three {Y : Subgroup G} (hY : Nat.card Y = 3) :
    ∃ y : G, y ∈ Y ∧ y ≠ 1 ∧ y ^ 3 = 1 ∧ zpowers y = Y := by
  have hnt : ∃ y ∈ Y, y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : Y = ⊥ := eq_bot_iff.mpr fun a ha => by simpa using hcon a ha
    rw [hbot, Subgroup.card_bot] at hY
    omega
  obtain ⟨y, hyY, hy1⟩ := hnt
  have hdvd : orderOf y ∣ 3 := by
    rw [← hY]
    simpa [Subgroup.orderOf_coe] using orderOf_dvd_natCard (⟨y, hyY⟩ : Y)
  have hord : orderOf y = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy1
    · exact h
  refine ⟨y, hyY, hy1, by rw [← hord]; exact pow_orderOf_eq_one y, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hyY) ?_
  rw [Nat.card_zpowers, hord, hY]

theorem smallQ8_of_prop627 (hS : Setting G) (hU0 : FullCoreLocal G) (hD2 : TheoremD2 G)
    (h627 : GL83SmallRankProp627 G) (h614 : GL83SmallRankProp614 G) : GL83SmallRankQ8 G := by
  intro h3 P M hM hΓ hempty hsolv he Y hYP hY3 hYJ
  by_cases hU : UniquenessAt G 3 P M
  · obtain ⟨-, hC⟩ := clauseC_of_uniquenessAt hS h3 hM hΓ hempty hU
    exact hC.2.2.2 Y hYP hY3 hYJ
  · obtain ⟨e⟩ := he
    have hsit : SmallRankSituation G 3 P M :=
      ⟨h3, hM, hU0 3 h3 P M hM, hΓ, hempty, largerPrimesUnique_three hS h3, hU⟩
    obtain ⟨T, hT⟩ := exists_smallRankSylowTwo hS h3 hM
    obtain ⟨x, hx⟩ := exists_smallRankPoint hS hU0 h3 hM hΓ hempty
    obtain ⟨⟨n, hn⟩, -, -⟩ := smallRankCaseTwo_of_prop627 hS hU0 hD2 h627 h614 hsit hsolv e hx hT
    obtain ⟨y, hyY, hy1, hy3, hyY'⟩ := exists_zpowers_eq_of_card_eq_three hY3
    have hyJ : y ∉ thompsonSubgroup (P : Subgroup G) := fun hy =>
      hYJ (hyY' ▸ zpowers_le.mpr hy)
    have hxJ := not_mem_thompsonSubgroup_of_not_centralizer_le h3 hS hM hempty e hx.mem
      hx.ne_one hx.pow_eq_one hx.not_centralizer_le
    obtain ⟨g, hgP, hg⟩ := exists_conj_zpowers_of_not_mem_thompsonSubgroup e hx.mem hx.ne_one
      hx.pow_eq_one hxJ (hYP hyY) hy1 hy3 hyJ
    have hY' : Y = (zpowers x).map (MulAut.conj g).toMonoidHom := hyY'.symm.trans hg
    subst hY'
    refine ⟨T, hT.le_core, hT.isPGroup, hT.index_odd, hT.normalized, n,
      one_le_of_rankThreeIsQ8CentralCyclic hn, ?_⟩
    rw [← map_inf_centralizer_zpowers (hT.normalized hgP) x]
    exact rankThreeIsQ8CentralCyclic_map hn (MulAut.conj g)

theorem two_le_pRank_inf_of_plane (hS : Setting G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (hempty : ∀ y : G, ¬ IsLargeObstruction p M y) {x z : G} (hxP : x ∈ (P : Subgroup G))
    (hx1 : x ≠ 1) (hxp : x ^ p = 1) (hxM : ¬ centralizer ({x} : Set G) ≤ M)
    (hz : SmallRankCentral P z) {H : Subgroup G} (hBH : zpowers x ⊔ zpowers z ≤ H) :
    2 ≤ CFSG.Open.pRank p (H ⊓ M) := by
  have hprime := sigmaA_prime p hp
  have hB := smallRankPlane_of_largeObstruction_empty hS hp hM hempty hxP hx1 hxp hxM hz.mem
    hz.centralizes hz.ne_one hz.pow_eq_one
  have hPM := (sylow_le_of_isCoreMaxLocal hS hp hM).1
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) :=
    sup_le (zpowers_le.mpr hxP) (zpowers_le.mpr hz.mem)
  unfold CFSG.Open.pRank
  exact le_csSup (pRank_set_bddAbove p hprime.one_lt _)
    ⟨_, le_inf hBH (hBP.trans hPM), hB.isElemAbelian, hB.card_eq⟩

theorem smallUniquePlane_of_prop627 (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD2 : TheoremD2 G) (h627 : GL83SmallRankProp627 G) (h614 : GL83SmallRankProp614 G) :
    GL83SmallRankUniquePlane G := by
  intro h3 P M hM hΓ hempty hsolv he x z hxP hx1 hx3 hxM hzP hzc hz1 hz3 H hH hBH
  have hz : SmallRankCentral P z := ⟨hzP, hzc, hz1, hz3⟩
  by_cases hU : UniquenessAt G 3 P M
  · exact hU.2 H hH (two_le_pRank_inf_of_plane hS h3 hM hempty hxP hx1 hx3 hxM hz hBH)
  · obtain ⟨e⟩ := he
    have hsit : SmallRankSituation G 3 P M :=
      ⟨h3, hM, hU0 3 h3 P M hM, hΓ, hempty, largerPrimesUnique_three hS h3, hU⟩
    exact le_of_plane_of_prop627 hS hU0 hD2 h627 h614 hsit hsolv e hxP hx1 hx3 hxM hz hH hBH

end CFSG.LocalAnalysis.RankThreeTheoremC
