module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Basic
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.GroupTheory.SteinbergBKOddNoncyclicRankTwo
import CFSG.RankThree.PartOne.S9.Planes.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_sup_normalizer_of_isSylowOf {p : ℕ} [Fact p.Prime] {H Y S : Subgroup G}
    (hn : H ≤ normalizer (Y : Set G)) (hS : CFSG.ABGLocalTools.IsSylowOf p S Y) :
    H ≤ Y ⊔ normalizer (S : Set G) := by
  intro x hx
  have hxY : x ∈ normalizer (Y : Set G) := hn hx
  have hS' : CFSG.ABGLocalTools.IsSylowOf p (S.map (MulAut.conj x).toMonoidHom) Y := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      exact (mem_normalizer_iff.1 hxY s).1 (hS.le hs)
    · rw [card_map_of_injective (MulAut.conj x).injective, hS.card_eq]
  obtain ⟨k, hk, hconj⟩ := hS.exists_mem_conj hS'
  have hkx : k⁻¹ * x ∈ normalizer (S : Set G) := by
    rw [mem_normalizer_iff]
    intro s
    have e1 : x * s * x⁻¹ ∈ S.map (MulAut.conj x).toMonoidHom ↔ s ∈ S := by
      constructor
      · rintro ⟨t, ht, hts⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hts
        exact mul_left_cancel (mul_right_cancel hts) ▸ ht
      · exact fun hs => ⟨s, hs, rfl⟩
    have e2 := hconj (x * s * x⁻¹)
    rw [e1, show k⁻¹ * (x * s * x⁻¹) * k = (k⁻¹ * x) * s * (k⁻¹ * x)⁻¹ by group] at e2
    exact e2
  rw [show x = k * (k⁻¹ * x) by group]
  exact mul_mem_sup hk hkx

theorem normalizer_le_of_le_of_two_le_pRank (hS : Setting G) (hU0 : FullCoreLocal G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {S : Subgroup G} (hSp : IsPGroup p S) (hSM : S ≤ M) (hS2 : 2 ≤ CFSG.Open.pRank p S) :
    normalizer (S : Set G) ≤ M := by
  have hprime := sigmaA_prime p hp
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨m, hm⟩ := pGroup_conjugate_into_sylow_within_overgroup p hprime P M hPM S hSp hSM
  have hN : normalizer ((S.map (MulAut.conj (m : G)).toMonoidHom : Subgroup G) : Set G) ≤ M :=
    (gamma_normalizer_le 2 p (P : Subgroup G) _ hm
      (by rwa [pRank_map_automorphism p hprime.one_lt])).trans (hU0 p hp P M hM)
  intro g hg
  have himage : MulAut.conj (m : G) g ∈ M := by
    apply hN
    rw [← map_equiv_normalizer_eq S (MulAut.conj (m : G))]
    exact mem_map_of_mem _ hg
  have hproduct := M.mul_mem (M.mul_mem (M.inv_mem m.property) himage) m.property
  simpa [MulAut.conj_apply, mul_assoc] using hproduct

theorem exists_mem_centralizer_orderOf_eq {p : ℕ} [hfact : Fact p.Prime] {P : Subgroup G}
    (hPp : IsPGroup p P) (hP : P ≠ ⊥) :
    ∃ z ∈ P, z ∈ centralizer (P : Set G) ∧ orderOf z = p := by
  have hPnt : Nontrivial P := (nontrivial_iff_ne_bot P).mpr hP
  have hZnt : Nontrivial (center P) := hPp.center_nontrivial
  obtain ⟨n, hn, hcard⟩ := (hPp.to_subgroup (center P)).nontrivial_iff_card.1 hZnt
  have hdvd : p ∣ Nat.card (center P) := by
    rw [hcard]
    exact dvd_pow_self p (Nat.pos_iff_ne_zero.1 hn)
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := center P) p hdvd
  refine ⟨((w : P) : G), (w : P).2, mem_centralizer_iff.mpr fun g hg =>
    congrArg Subtype.val (mem_center_iff.1 w.2 ⟨g, hg⟩), ?_⟩
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
  exact hw

theorem two_le_pRank_inf_centralizer {p : ℕ} [hfact : Fact p.Prime] {P : Subgroup G}
    (hPp : IsPGroup p P) (hP2 : 2 ≤ CFSG.Open.pRank p P) {x : G} (hxP : x ∈ P) (hx1 : x ≠ 1)
    (hxp : x ^ p = 1) : 2 ≤ CFSG.Open.pRank p (P ⊓ centralizer ({x} : Set G)) := by
  have hprime := hfact.out
  obtain ⟨z, hzP, hzc', hzord⟩ := exists_mem_centralizer_orderOf_eq hPp
    (fun h => hx1 ((mem_bot.mp (h ▸ hxP))))
  have hzc : ∀ g ∈ P, g * z = z * g := mem_centralizer_iff.mp hzc'
  have hzp : z ^ p = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
  by_cases hzx : z ∈ zpowers x
  ·
    have hxz : x ∈ zpowers z := by
      have hle : zpowers z ≤ zpowers x := zpowers_le.mpr hzx
      have hcz : Nat.card (zpowers z) = p := by rw [Nat.card_zpowers, hzord]
      have hcx : Nat.card (zpowers x) = p := by
        rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
      have heq : zpowers z = zpowers x := Subgroup.eq_of_le_of_card_ge hle (by omega)
      rw [heq]
      exact mem_zpowers x
    have hPC : P ≤ centralizer ({x} : Set G) := by
      intro g hg
      rw [mem_centralizer_singleton_iff]
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hxz
      rw [← hj]
      exact (Commute.zpow_right (hzc g hg) j).eq
    rwa [inf_of_le_left hPC]
  ·
    have hcomm : ∀ e ∈ zpowers x, e * z = z * e := fun e he =>
      hzc e (zpowers_le.mpr hxP he)
    have hcard := CFSG.RankThree.PartOne.Planes.card_sup_zpowers hprime (zpowers x) hzp hzx
      hcomm
    have hxe : CFSG.IsElementaryAbelian p (zpowers x) :=
      CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hxp
    have hze : CFSG.IsElementaryAbelian p (zpowers z) :=
      CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hzp
    have hEe : CFSG.IsElementaryAbelian p ↥(zpowers x ⊔ zpowers z) :=
      CFSG.IsElementaryAbelian.sup_of_le_centralizer
        (zpowers_le.mpr (mem_centralizer_iff.mpr fun e he => hcomm e he))
    have hEle : zpowers x ⊔ zpowers z ≤ P ⊓ centralizer ({x} : Set G) := by
      refine sup_le (le_inf (zpowers_le.mpr hxP) (zpowers_le.mpr ?_))
        (le_inf (zpowers_le.mpr hzP) (zpowers_le.mpr ?_))
      · exact mem_centralizer_singleton_iff.mpr rfl
      · exact mem_centralizer_singleton_iff.mpr (hzc x hxP).symm
    unfold CFSG.Open.pRank
    refine le_csSup (pRank_set_bddAbove p hprime.one_lt _) ⟨_, hEle,
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1 hEe, ?_⟩
    rw [hcard, Nat.card_zpowers, orderOf_eq_prime hxp hx1, pow_two]

theorem two_le_pRank_of_not_isCyclic {p : ℕ} (hprime : p.Prime) (hodd : p ≠ 2) {Q : Subgroup G}
    (hQp : IsPGroup p Q) (hnc : ¬ IsCyclic Q) : 2 ≤ CFSG.Open.pRank p Q := by
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨B, hB, hBc⟩ := CFSG.GroupTheory.SteinbergBK.odd_noncyclic_pgroup_rank_two
    (hprime.odd_of_ne_two hodd) hQp hnc
  have hBe : CFSG.IsElementaryAbelian p (B.map Q.subtype) :=
    CFSG.IsElementaryAbelian.map_subtype
  unfold CFSG.Open.pRank
  exact le_csSup (pRank_set_bddAbove p hprime.one_lt _) ⟨B.map Q.subtype, map_subtype_le B,
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1 hBe,
    by rw [card_map_of_injective Q.subtype_injective, hBc]⟩

theorem exists_pow_eq_one_normalizer_le_of_isCyclic {p : ℕ} (hprime : p.Prime) {Q : Subgroup G}
    (hQp : IsPGroup p Q) (hQc : IsCyclic Q) (hQ1 : 1 ≤ CFSG.Open.pRank p Q) :
    ∃ x ∈ Q, x ≠ 1 ∧ x ^ p = 1 ∧
      normalizer (Q : Set G) ≤ normalizer ((zpowers x : Subgroup G) : Set G) := by
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨g₀, hg₀⟩ := hQc.exists_generator
  obtain ⟨E, hEQ, -, hEc⟩ := pRank_attained p Q (by omega)
  have hQcard : 1 < Nat.card Q := by
    have h1 : 1 < Nat.card E := by
      rw [hEc]
      exact Nat.one_lt_pow (by omega) hprime.one_lt
    exact h1.trans_le (card_le_of_le hEQ)
  obtain ⟨a, ha⟩ := hQp.exists_card_eq
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [pow_zero] at ha
    omega
  have hord : orderOf (g₀ : G) = p ^ a := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg₀, ha]
  set x : G := (g₀ : G) ^ p ^ (a - 1) with hx
  have hpa : p ^ (a - 1) * p = p ^ a := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr ha0)]
  refine ⟨x, pow_mem g₀.2 _, ?_, by rw [hx, ← pow_mul, hpa, ← hord, pow_orderOf_eq_one], ?_⟩
  · refine pow_ne_one_of_lt_orderOf (pow_ne_zero _ hprime.ne_zero) ?_
    rw [hord]
    exact Nat.pow_lt_pow_right hprime.one_lt (by omega)
  intro g hg
  have hgg₀ : g * (g₀ : G) * g⁻¹ ∈ Q := (mem_normalizer_iff.mp hg (g₀ : G)).mp g₀.2
  obtain ⟨k, hk⟩ := hg₀ ⟨_, hgg₀⟩
  have hk' : (g₀ : G) ^ k = g * (g₀ : G) * g⁻¹ := congrArg Subtype.val hk
  have hconj : (MulAut.conj g).toMonoidHom x = x ^ k := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← conj_pow, ← hk', ← zpow_natCast, ← zpow_mul, hx, ← zpow_natCast, ← zpow_mul,
      mul_comm]
  have hle : (zpowers x).map (MulAut.conj g).toMonoidHom ≤ zpowers x := by
    rw [MonoidHom.map_zpowers, hconj, zpowers_le]
    exact zpow_mem (mem_zpowers x) k
  exact mem_normalizer_iff_map_conj_eq.mpr
    (Subgroup.eq_of_le_of_card_ge hle (card_map_of_injective (MulAut.conj g).injective).ge)

omit [Finite G] in
theorem normalizer_zpowers_le_normalizer_centralizer (x : G) :
    normalizer ((zpowers x : Subgroup G) : Set G) ≤
      normalizer ((centralizer ({x} : Set G) : Subgroup G) : Set G) := by
  have hCeq : centralizer ({x} : Set G) = centralizer ((zpowers x : Subgroup G) : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  intro n hn
  have hn' : (zpowers x).map (MulAut.conj n).toMonoidHom = zpowers x :=
    mem_normalizer_iff_map_conj_eq.mp hn
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (centralizer ({x} : Set G)).map (MulAut.conj n).toMonoidHom = centralizer ({x} : Set G)
  rw [hCeq, centralizer_map_automorphism, hn']

theorem normalizer_zpowers_le_of_centralizer_le (hS : Setting G) (hU0 : FullCoreLocal G)
    {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G}
    (hM : IsCoreMaxLocal p P M) {x : G}
    (h2 : 2 ≤ CFSG.Open.pRank p ((P : Subgroup G) ⊓ centralizer ({x} : Set G)))
    (hCM : centralizer ({x} : Set G) ≤ M) :
    normalizer ((zpowers x : Subgroup G) : Set G) ≤ M := by
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨T, hT⟩ := ((P.isPGroup'.to_inf_left (K := centralizer ({x} : Set G))).comap_subtype
    (K := centralizer ({x} : Set G))).exists_le_sylow
  set S : Subgroup G := (T : Subgroup (centralizer ({x} : Set G))).map
    (centralizer ({x} : Set G)).subtype with hSdef
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf p S (centralizer ({x} : Set G)) := ⟨T, rfl⟩
  have hPCS : (P : Subgroup G) ⊓ centralizer ({x} : Set G) ≤ S := fun y hy =>
    ⟨⟨y, hy.2⟩, hT hy, rfl⟩
  have hSM : normalizer (S : Set G) ≤ M :=
    normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM hSsyl.isPGroup (hSsyl.le.trans hCM)
      (h2.trans (pRank_mono p hprime.one_lt hPCS))
  exact (le_sup_normalizer_of_isSylowOf (normalizer_zpowers_le_normalizer_centralizer x)
    hSsyl).trans (sup_le hCM hSM)

theorem exists_centralizer_not_le_of_not_gamma_one_le (hS : Setting G) (hU0 : FullCoreLocal G)
    {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G}
    (hM : IsCoreMaxLocal p P M) (hfail : ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M) :
    ∃ x ∈ (P : Subgroup G), x ≠ 1 ∧ x ^ p = 1 ∧ ¬ centralizer ({x} : Set G) ≤ M := by
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨-, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨Q, hQP, hQ1, hQM⟩ : ∃ Q : Subgroup G, Q ≤ P ∧ 1 ≤ CFSG.Open.pRank p Q ∧
      ¬ normalizer (Q : Set G) ≤ M := by
    by_contra h
    push Not at h
    exact hfail ((gamma_le_iff 1 p (P : Subgroup G) M).mpr fun Q hQP hQ1 => h Q hQP hQ1)
  have hQp : IsPGroup p Q := P.isPGroup'.to_le hQP
  have hQc : IsCyclic Q := by
    by_contra hnc
    exact hQM ((gamma_normalizer_le 2 p (P : Subgroup G) Q hQP
      (two_le_pRank_of_not_isCyclic hprime (sigmaA_odd p hp) hQp hnc)).trans (hU0 p hp P M hM))
  obtain ⟨x, hxQ, hx1, hxp, hNQx⟩ :=
    exists_pow_eq_one_normalizer_le_of_isCyclic hprime hQp hQc hQ1
  exact ⟨x, hQP hxQ, hx1, hxp, fun hCM => hQM (hNQx.trans
    (normalizer_zpowers_le_of_centralizer_le hS hU0 hp hM
      (two_le_pRank_inf_centralizer P.isPGroup' (by omega) (hQP hxQ) hx1 hxp) hCM))⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
