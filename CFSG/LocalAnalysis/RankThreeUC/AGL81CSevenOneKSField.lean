module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenOne
import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient
import CFSG.RankThree.PartTwo.KFacts.K72List

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

namespace SevenOneKS

open Subgroup

theorem exists_not_mem_pow_eq_one {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {I : Subgroup G} [I.Normal] [hIs : IsSimpleGroup I] (hindex : I.index = p)
    (hInab : ∃ a b : I, a * b ≠ b * a) (hrank : CFSG.Open.pRank p I ≤ 1) :
    ∃ y : G, y ∉ I ∧ y ^ p = 1 := by
  by_contra hcon
  have hin : ∀ y : G, y ^ p = 1 → y ∈ I := fun y hy => by
    by_contra h
    exact hcon ⟨y, h, hy⟩
  have hpG : p ∣ Nat.card G := by
    rw [← hindex]
    exact I.index_dvd_card
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  have hPrank : CFSG.Open.pRank p (P : Subgroup G) ≤ 1 := by
    obtain ⟨E, hEP, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.out.one_lt (P : Subgroup G)
    have hEI : E ≤ I := fun e he => hin e (hE.2 e he)
    exact (CFSG.SectionRank.le_pRank hp.out.one_lt hEI hE hcard).trans hrank
  haveI : IsCyclic (P : Subgroup G) := by
    refine OddRankOneQuotient.isCyclic_of_pRank_le_one hp.out hp2 P.isPGroup' ?_
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact hPrank
  rcases P.normalizer_le_centralizer_or_le_commutator with hN | hC
  ·
    obtain ⟨K, hKn, hcomp, hKp⟩ : ∃ K : Subgroup G, K.Normal ∧ K.IsComplement' P ∧
        ¬ p ∣ Nat.card K :=
      ⟨(MonoidHom.transferSylow P hN).ker, inferInstance,
        MonoidHom.ker_transferSylow_isComplement' P hN,
        MonoidHom.not_dvd_card_ker_transferSylow P hN⟩
    haveI := hKn
    rcases hIs.eq_bot_or_eq_top_of_normal (K.subgroupOf I) with h | h
    ·
      have hdisj : Disjoint K I := Subgroup.subgroupOf_eq_bot.mp h
      have hinj : Function.Injective ((QuotientGroup.mk' I).comp K.subtype) := by
        rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
        intro k hk
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff] at hk
        exact (Subgroup.mem_bot).mpr (Subtype.ext (Subgroup.disjoint_def.mp hdisj k.2 hk))
      have hdvd : Nat.card K ∣ p := by
        have := Subgroup.card_dvd_of_injective _ hinj
        rwa [← Subgroup.index_eq_card, hindex] at this
      have h1 : Nat.card K = 1 := by
        rcases (Nat.dvd_prime hp.out).mp hdvd with h1 | h1
        · exact h1
        · exact (hKp ⟨1, by rw [h1, mul_one]⟩).elim
      have hPtop : (P : Subgroup G) = ⊤ := by
        have hcm := hcomp.card_mul_card
        rw [h1, one_mul] at hcm
        exact Subgroup.eq_top_of_card_eq _ hcm
      have hGp : IsPGroup p G := fun g => by
        have hg : g ∈ (P : Subgroup G) := by
          rw [hPtop]
          exact Subgroup.mem_top g
        obtain ⟨k, hk⟩ := P.isPGroup' ⟨g, hg⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
      obtain ⟨a, b, hab⟩ := hInab
      haveI : Nontrivial I := ⟨⟨a * b, b * a, hab⟩⟩
      have hZ : ⊥ < Subgroup.center I := (hGp.to_subgroup I).bot_lt_center
      rcases hIs.eq_bot_or_eq_top_of_normal (Subgroup.center I) with hz | hz
      · exact hZ.ne' hz
      · have hb : b ∈ Subgroup.center I := by
          rw [hz]
          exact Subgroup.mem_top b
        exact hab (Subgroup.mem_center_iff.mp hb a)
    ·
      have hIK : I ≤ K := Subgroup.subgroupOf_eq_top.mp h
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p (P.dvd_card_of_dvd_card hpG)
      have hyp' : y ^ p = 1 := by
        have := pow_orderOf_eq_one y
        rwa [hy] at this
      have hyp : (y : G) ^ p = 1 := by rw [← Subgroup.coe_pow, hyp', Subgroup.coe_one]
      have hy1 : (y : G) = 1 :=
        Subgroup.disjoint_def.mp hcomp.disjoint (hIK (hin _ hyp)) y.2
      have : orderOf y = 1 := orderOf_eq_one_iff.mpr (Subtype.ext hy1)
      rw [hy] at this
      exact hp.out.one_lt.ne' this
  ·
    have hcard : Nat.card (G ⧸ I) = p := by rw [← Subgroup.index_eq_card, hindex]
    haveI : IsCyclic (G ⧸ I) := isCyclic_of_prime_card hcard
    have hcomm : commutator G ≤ I :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
    have hPI : (P : Subgroup G) ≤ I := hC.trans hcomm
    apply P.not_dvd_index
    rw [← Subgroup.relIndex_mul_index hPI, hindex]
    exact dvd_mul_left p _

theorem exists_mul_pow_eq_one {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {I : Subgroup G} [I.Normal] [IsSimpleGroup I]
    (hInab : ∃ a b : I, a * b ≠ b * a) (hrank : CFSG.Open.pRank p I ≤ 1) {g : G} (hg : g ∉ I)
    (hgp : g ^ p ∈ I) : ∃ i ∈ I, (g * i) ^ p = 1 := by
  obtain ⟨H, hH⟩ : ∃ H : Subgroup G, H = I ⊔ Subgroup.zpowers g := ⟨_, rfl⟩
  have hIH : I ≤ H := hH ▸ le_sup_left
  let eI : I.subgroupOf H ≃* I := Subgroup.subgroupOfEquivOfLe hIH
  haveI : IsSimpleGroup (I.subgroupOf H) := eI.isSimpleGroup
  have hInab' : ∃ a b : I.subgroupOf H, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hInab
    refine ⟨eI.symm a, eI.symm b, fun h => hab (eI.symm.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  have hrank' : CFSG.Open.pRank p (I.subgroupOf H) ≤ 1 := by
    have := CFSG.SectionRank.pRank_le_map hp.out.one_lt H.subtype H.subtype_injective
      (I.subgroupOf H)
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hIH] at this
    exact this.trans hrank
  have hmap : H.map (QuotientGroup.mk' I) = Subgroup.zpowers (g : G ⧸ I) := by
    rw [hH, Subgroup.map_sup, MonoidHom.map_zpowers, QuotientGroup.map_mk'_self, bot_sup_eq,
      QuotientGroup.mk'_apply]
  have hord : orderOf (g : G ⧸ I) = p := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hgp
    · rwa [Ne, QuotientGroup.eq_one_iff]
  have hindex : (I.subgroupOf H).index = p := by
    change I.relIndex H = p
    rw [← QuotientGroup.ker_mk' I, Subgroup.relIndex_ker, hmap, Nat.card_zpowers, hord]
  obtain ⟨y, hyI, hyp⟩ := exists_not_mem_pow_eq_one hp2 hindex hInab' hrank'
  have hyI' : (y : G) ∉ I := fun h => hyI (Subgroup.mem_subgroupOf.mpr h)
  have hyp' : (y : G) ^ p = 1 := by rw [← Subgroup.coe_pow, hyp, Subgroup.coe_one]
  have hyord : orderOf (y : G ⧸ I) = p := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← QuotientGroup.mk_pow, hyp', QuotientGroup.mk_one]
    · rwa [Ne, QuotientGroup.eq_one_iff]
  have hyH : ((y : G) : G ⧸ I) ∈ Subgroup.zpowers (g : G ⧸ I) := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ y.2
  have hzeq : Subgroup.zpowers ((y : G) : G ⧸ I) = Subgroup.zpowers (g : G ⧸ I) := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hyH) (le_of_eq ?_)
    rw [Nat.card_zpowers, Nat.card_zpowers, hord, hyord]
  have hgy : (g : G ⧸ I) ∈ Subgroup.zpowers ((y : G) : G ⧸ I) := by
    rw [hzeq]
    exact Subgroup.mem_zpowers _
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hgy
  refine ⟨g⁻¹ * (y : G) ^ j, ?_, ?_⟩
  · rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_zpow, hj, inv_mul_cancel]
  · rw [mul_inv_cancel_left, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyp',
      one_zpow]

theorem exists_orderOf_eq_commute_of_pow_mem {X : Type*} [Group X] [Finite X] {p : ℕ}
    [hp : Fact p.Prime] {L : Subgroup X} [hLn : L.Normal] (hpL : p ∣ Nat.card L) {w : X}
    (hw : w ^ p ∈ Subgroup.centralizer (L : Set X)) :
    ∃ z ∈ L, orderOf z = p ∧ w * z = z * w := by
  have ho : orderOf w ≠ 0 := (orderOf_pos w).ne'
  set m := ordCompl[p] (orderOf w) with hm
  have hm0 : m ≠ 0 := (Nat.ordCompl_pos p ho).ne'
  have hmo : p ^ (orderOf w).factorization p * m = orderOf w :=
    Nat.ordProj_mul_ordCompl_eq_self (orderOf w) p
  have hcop : Nat.Coprime p m := Nat.coprime_ordCompl hp.out ho
  have hw1 : IsPGroup p (Subgroup.zpowers (w ^ m)) := by
    refine IsPGroup.of_card (n := (orderOf w).factorization p) ?_
    rw [Nat.card_zpowers, orderOf_pow_of_dvd hm0 (Dvd.intro_left _ hmo)]
    exact Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hm0) hmo.symm
  have hN : Subgroup.zpowers (w ^ m) ≤ Subgroup.normalizer (L : Set X) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨z, hz, hzo⟩ :=
    CFSG.RankThree.PartTwo.KFacts.exists_mem_centralizer_orderOf_eq hw1 hN hpL
  refine ⟨z, hz.1, hzo, ?_⟩
  have h1 : Commute (w ^ m) z :=
    Subgroup.mem_centralizer_iff.mp hz.2 (w ^ m) (Subgroup.mem_zpowers _)
  have h2 : Commute (w ^ p) z := (Subgroup.mem_centralizer_iff.mp hw z hz.1).symm
  have hbez : ((Nat.gcd p m : ℕ) : ℤ) = p * Nat.gcdA p m + m * Nat.gcdB p m := Nat.gcd_eq_gcd_ab p m
  rw [Nat.Coprime.gcd_eq_one hcop, Nat.cast_one] at hbez
  have hweq : w = (w ^ p) ^ Nat.gcdA p m * (w ^ m) ^ Nat.gcdB p m := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hbez, zpow_one]
  have : Commute w z := by
    rw [hweq]
    exact (h2.zpow_left _).mul_left (h1.zpow_left _)
  exact this

end SevenOneKS

theorem sevenOneFourField_holds : SevenOneFourField := by
  intro X _ _ _ p hp hp2 L hL hLn hr x hx hxp
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hLn
  set C : Subgroup X := Subgroup.centralizer (L : Set X) with hC
  set π : X →* X ⧸ C := QuotientGroup.mk' C with hπ
  set I : Subgroup (X ⧸ C) := L.map π with hI
  haveI : I.Normal := Subgroup.Normal.map hLn π (QuotientGroup.mk'_surjective C)
  set f : L →* I := π.subgroupMap L with hf
  have hfs : Function.Surjective f := π.subgroupMap_surjective L
  have hker : f.ker = Subgroup.center L := by
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    have h1 : f l = 1 ↔ (l : X) ∈ C := by
      rw [← QuotientGroup.eq_one_iff (N := C) (l : X)]
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [h1, hC, Subgroup.mem_centralizer_iff]
    constructor
    · intro h g
      exact Subtype.ext (h g g.2)
    · intro h m hm
      exact congrArg Subtype.val (h ⟨m, hm⟩)
  let e : (L ⧸ Subgroup.center L) ≃* I :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfs)
  haveI : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.1.2.1
  haveI : IsSimpleGroup I := e.symm.isSimpleGroup
  have hInab : ∃ a b : I, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hL.1.2.2
    refine ⟨e a, e b, fun h => hab (e.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  have hrank : CFSG.Open.pRank p I ≤ 1 := by
    have h1 : CFSG.pRank p L ≤ 1 := by
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
      exact hr.le
    have h2 := OddRankOneQuotient.pRank_le_one_of_surjective hp hp2 h1 f hfs
    rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at h2
  have hxI : π x ∉ I := by
    intro h
    obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.mp h
    apply hx
    have hlx' : (l : X ⧸ C) = (x : X ⧸ C) := hlx
    have hc : l⁻¹ * x ∈ C := QuotientGroup.eq.mp hlx'
    have := Subgroup.mul_mem_sup hl hc
    rwa [mul_inv_cancel_left] at this
  have hxpI : π x ^ p ∈ I := by
    rw [← map_pow]
    obtain ⟨l, hl, c, hc, hlc⟩ := Subgroup.mem_sup_of_normal_right.mp hxp
    refine Subgroup.mem_map.mpr ⟨l, hl, ?_⟩
    have hc1 : π c = 1 := (QuotientGroup.eq_one_iff c).mpr hc
    rw [← hlc, map_mul, hc1, mul_one]
  obtain ⟨i, hiI, hi⟩ := SevenOneKS.exists_mul_pow_eq_one hp2 hInab hrank hxI hxpI
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hiI
  have hwC : (x * l) ^ p ∈ C := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul]
    exact hi
  refine ⟨l, hl, hwC, ?_⟩
  have hpL : p ∣ Nat.card L := by
    obtain ⟨E, hEL, -, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt L
    rw [hr, pow_one] at hcard
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hEL
  exact SevenOneKS.exists_orderOf_eq_commute_of_pow_mem hpL hwC

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
