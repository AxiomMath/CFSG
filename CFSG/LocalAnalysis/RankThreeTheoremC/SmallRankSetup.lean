module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements
public import CFSG.LocalAnalysis.RankThreeTheoremC.IsolatedPlanes

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def IsLargeObstruction (p : ℕ) (M : Subgroup G) (x : G) : Prop :=
  x ∈ M ∧ x ≠ 1 ∧ x ^ p = 1 ∧ 3 ≤ CFSG.Open.pRank p (centralizer ({x} : Set G)) ∧
    ¬ centralizer ({x} : Set G) ≤ M

theorem normalizer_sylow_le (hS : Setting G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M) :
    normalizer ((P : Subgroup G) : Set G) ≤ M := by
  have hP3 := (sylow_le_of_isCoreMaxLocal hS hp hM).2
  refine (aschCore_normalizer_le 2 p (P : Subgroup G) (P : Subgroup G) le_rfl (by omega) ?_).trans
    hM.2
  rw [sup_eq_left.mpr inf_le_left, hP3]

theorem normalizer_zpowers_le_of_largeObstruction_empty (hS : Setting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (hempty : ∀ y : G, ¬ IsLargeObstruction p M y) {z : G} (hzP : z ∈ (P : Subgroup G))
    (hzc : z ∈ centralizer ((P : Subgroup G) : Set G)) (hz1 : z ≠ 1) (hzp : z ^ p = 1) :
    normalizer ((zpowers z : Subgroup G) : Set G) ≤ M := by
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hPC : (P : Subgroup G) ≤ centralizer ({z} : Set G) := fun g hg =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzc g hg)
  have hCM : centralizer ({z} : Set G) ≤ M := by
    by_contra hCM
    exact hempty z ⟨hPM hzP, hz1, hzp, hP3.ge.trans (pRank_mono p hprime.one_lt hPC), hCM⟩
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf p (P : Subgroup G) (centralizer ({z} : Set G)) :=
    ⟨P.subtype hPC, by rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hPC]⟩
  exact (le_sup_normalizer_of_isSylowOf (normalizer_zpowers_le_normalizer_centralizer z)
    hPsyl).trans (sup_le hCM (normalizer_sylow_le hS hp hM))

structure SmallRankPlane (p : ℕ) (P : Subgroup G) (x z : G) : Prop where
  isElemAbelian : IsElemAbelian p (zpowers x ⊔ zpowers z)
  card_eq : Nat.card ↥(zpowers x ⊔ zpowers z) = p ^ 2
  mem_of_mem_centralizer : ∀ y ∈ centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G),
    y ^ p = 1 → y ∈ zpowers x ⊔ zpowers z
  isIsolatedPlane : IsIsolatedPlane p P (zpowers x ⊔ zpowers z)
  center : ∀ w ∈ P, w ∈ centralizer (P : Set G) → w ^ p = 1 → w ∈ zpowers z

theorem smallRankPlane_of_largeObstruction_empty (hS : Setting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (hempty : ∀ y : G, ¬ IsLargeObstruction p M y) {x z : G} (hxP : x ∈ (P : Subgroup G))
    (hx1 : x ≠ 1) (hxp : x ^ p = 1) (hxM : ¬ centralizer ({x} : Set G) ≤ M)
    (hzP : z ∈ (P : Subgroup G)) (hzc : z ∈ centralizer ((P : Subgroup G) : Set G))
    (hz1 : z ≠ 1) (hzp : z ^ p = 1) : SmallRankPlane p (P : Subgroup G) x z := by
  classical
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hCx : CFSG.Open.pRank p (centralizer ({x} : Set G)) ≤ 2 := by
    by_contra h
    push Not at h
    exact hempty x ⟨hPM hxP, hx1, hxp, by omega, hxM⟩
  have hzx : ∀ g ∈ (P : Subgroup G), g * z = z * g := fun g hg => mem_centralizer_iff.mp hzc g hg
  have hxz : x * z = z * x := hzx x hxP
  have hzxpow : z ∉ zpowers x := by
    intro hz
    have hcz : Nat.card (zpowers z) = p := by rw [Nat.card_zpowers, orderOf_eq_prime hzp hz1]
    have hcx : Nat.card (zpowers x) = p := by rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
    have heq : zpowers z = zpowers x :=
      Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hz) (by omega)
    have hxzp : x ∈ zpowers z := heq ▸ mem_zpowers x
    have hPC : (P : Subgroup G) ≤ centralizer ({x} : Set G) := by
      intro g hg
      rw [mem_centralizer_singleton_iff]
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hxzp
      rw [← hj]
      exact (Commute.zpow_right (hzx g hg) j).eq
    have := pRank_mono p hprime.one_lt hPC
    omega
  set B : Subgroup G := zpowers x ⊔ zpowers z with hB
  have hcomm : ∀ e ∈ zpowers x, e * z = z * e := fun e he => hzx e (zpowers_le.mpr hxP he)
  have hBc : Nat.card B = p ^ 2 := by
    rw [hB, CFSG.RankThree.PartOne.Planes.card_sup_zpowers hprime (zpowers x) hzp hzxpow hcomm,
      Nat.card_zpowers, orderOf_eq_prime hxp hx1, pow_two]
  have hxe : CFSG.IsElementaryAbelian p (zpowers x) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hxp
  have hze : CFSG.IsElementaryAbelian p (zpowers z) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hzp
  have hBe' : CFSG.IsElementaryAbelian p B :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer
      (zpowers_le.mpr (mem_centralizer_iff.mpr fun e he => hcomm e he))
  have hBe : IsElemAbelian p B :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p B).1 hBe'
  have hBP : B ≤ P := sup_le (zpowers_le.mpr hxP) (zpowers_le.mpr hzP)
  have hBCx : B ≤ centralizer ({x} : Set G) :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxz.symm))
  have hmem : ∀ y ∈ centralizer (B : Set G), y ^ p = 1 → y ∈ B := by
    intro y hyC hyp
    by_contra hyB
    have hcommy : ∀ e ∈ B, e * y = y * e := fun e he => mem_centralizer_iff.mp hyC e he
    have hcard3 := CFSG.RankThree.PartOne.Planes.card_sup_zpowers hprime B hyp hyB hcommy
    rw [hBc] at hcard3
    have hye : CFSG.IsElementaryAbelian p (zpowers y) :=
      CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hyp
    have hF : CFSG.IsElementaryAbelian p ↥(B ⊔ zpowers y) :=
      CFSG.IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hyC)
    have hyx : y ∈ centralizer ({x} : Set G) :=
      mem_centralizer_singleton_iff.mpr (hcommy x (mem_sup_left (mem_zpowers x))).symm
    have h3 : 3 ≤ CFSG.Open.pRank p (centralizer ({x} : Set G)) := by
      unfold CFSG.Open.pRank
      exact le_csSup (pRank_set_bddAbove p hprime.one_lt _) ⟨_, sup_le hBCx (zpowers_le.mpr hyx),
        (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1 hF,
        by rw [hcard3, ← pow_succ]⟩
    omega
  have hiso : IsIsolatedPlane p (P : Subgroup G) B := by
    refine ⟨hBP, hBe', hBc, fun E hEP hE hBE => ?_⟩
    have hE' : IsElemAbelian p E :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).1 hE
    have hEB : E ≤ B := fun e he => hmem e (mem_centralizer_iff.mpr fun b hb =>
      congrArg Subtype.val (hE'.1.is_comm.comm ⟨b, hBE hb⟩ ⟨e, he⟩)) (hE'.2 e he)
    rw [← hBc]
    exact card_le_of_le hEB
  have hcenter : ∀ w ∈ (P : Subgroup G), w ∈ centralizer ((P : Subgroup G) : Set G) →
      w ^ p = 1 → w ∈ zpowers z := by
    intro w hwP hwc hwp
    have hwB : w ∈ B :=
      hmem w (mem_centralizer_iff.mpr fun b hb => mem_centralizer_iff.mp hwc b (hBP hb)) hwp
    by_contra hwz
    have hcard2 := CFSG.RankThree.PartOne.Planes.card_sup_zpowers hprime (zpowers z) hwp hwz
      (fun e he => mem_centralizer_iff.mp hwc e (zpowers_le.mpr hzP he))
    have heq : zpowers z ⊔ zpowers w = B := by
      refine Subgroup.eq_of_le_of_card_ge (sup_le le_sup_right (zpowers_le.mpr hwB)) ?_
      rw [hcard2, hBc, Nat.card_zpowers, orderOf_eq_prime hzp hz1, pow_two]
    have hBcent : B ≤ centralizer ((P : Subgroup G) : Set G) := by
      rw [← heq]
      exact sup_le (zpowers_le.mpr hzc) (zpowers_le.mpr hwc)
    have hxc : x ∈ centralizer ((P : Subgroup G) : Set G) :=
      hBcent (mem_sup_left (mem_zpowers x))
    have hPC : (P : Subgroup G) ≤ centralizer ({x} : Set G) := fun g hg =>
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxc g hg)
    have := pRank_mono p hprime.one_lt hPC
    omega
  exact ⟨hBe, hBc, hmem, hiso, hcenter⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
