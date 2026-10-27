module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Setting
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankSetup

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup
open CFSG.Yardstones.Md8ed6d263d89 (sixPlane)
open CFSG.LocalAnalysis.RankFourTheoremC.PPointP (omegaCenter mem_omegaCenter)
open CFSG.LocalAnalysis.RankThreeTheoremC (SmallRankPlane IsIsolatedPlane
  le_normalizer_zpowers_of_le_centralizer centralizer_singleton_le_normalizer_zpowers)

structure Central {G : Type} [Group G] {p : ℕ} (P : Sylow p G) (z : G) : Prop where
  mem : z ∈ (P : Subgroup G)
  centralizes : z ∈ centralizer ((P : Subgroup G) : Set G)
  ne_one : z ≠ 1
  pow_eq_one : z ^ p = 1

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}

theorem exists_central [Fact p.Prime] (hP : (P : Subgroup G) ≠ ⊥) : ∃ z : G, Central P z := by
  have hnt : Nontrivial (P : Subgroup G) := (Subgroup.nontrivial_iff_ne_bot _).mpr hP
  have hZ : Nontrivial (center (P : Subgroup G)) := P.isPGroup'.center_nontrivial
  have hdvd : p ∣ Nat.card (center (P : Subgroup G)) :=
    (P.isPGroup'.to_subgroup _).card_eq_or_dvd.resolve_left fun h =>
      (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne' h
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hc' : orderOf ((c : P) : G) = p := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  refine ⟨((c : P) : G), (c : P).2, ?_, ?_, ?_⟩
  · rw [mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2 ⟨h, hh⟩)
  · intro h1
    rw [h1, orderOf_one] at hc'
    exact (Fact.out : p.Prime).one_lt.ne hc'
  · have h := pow_orderOf_eq_one ((c : P) : G)
    rwa [hc'] at h

theorem plane_of_central (hS : Situation G p P M) (hx : Point P M x) (hz : Central P z) :
    SmallRankPlane p (P : Subgroup G) x z := by
  classical
  have hprime := hS.prime
  have hfact : Fact p.Prime := ⟨hprime⟩
  have hPM := hS.sylow_le
  have hP4 := hS.four_le_pRank
  have hxp : x ^ p = 1 := hx.pow_eq_one
  have hx1 : x ≠ 1 := hx.ne_one hprime
  have hzp : z ^ p = 1 := hz.pow_eq_one
  have hz1 : z ≠ 1 := hz.ne_one
  have hCx : Open.pRank p (centralizer ({x} : Set G)) ≤ 2 := hx.pRank_centralizer_le hS
  have hzx : ∀ g ∈ (P : Subgroup G), g * z = z * g := fun g hg =>
    mem_centralizer_iff.mp hz.centralizes g hg
  have hxz : x * z = z * x := hzx x hx.mem
  have hzxpow : z ∉ zpowers x := by
    intro hzx'
    have hcz : Nat.card (zpowers z) = p := by rw [Nat.card_zpowers, orderOf_eq_prime hzp hz1]
    have hcx : Nat.card (zpowers x) = p := by rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
    have heq : zpowers z = zpowers x :=
      Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hzx') (by omega)
    have hxzp : x ∈ zpowers z := heq ▸ mem_zpowers x
    have hPC : (P : Subgroup G) ≤ centralizer ({x} : Set G) := by
      intro g hg
      rw [mem_centralizer_singleton_iff]
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hxzp
      rw [← hj]
      exact (Commute.zpow_right (hzx g hg) j).eq
    have := CFSG.SectionRank.pRank_mono hprime.one_lt hPC
    omega
  set B : Subgroup G := zpowers x ⊔ zpowers z with hB
  have hcomm : ∀ e ∈ zpowers x, e * z = z * e := fun e he => hzx e (zpowers_le.mpr hx.mem he)
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
  have hBP : B ≤ P := sup_le (zpowers_le.mpr hx.mem) (zpowers_le.mpr hz.mem)
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
    have h3 : 3 ≤ Open.pRank p (centralizer ({x} : Set G)) :=
      CFSG.SectionRank.le_pRank hprime.one_lt (sup_le hBCx (zpowers_le.mpr hyx))
        ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1 hF)
        (by rw [hcard3, ← pow_succ])
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
      (fun e he => mem_centralizer_iff.mp hwc e (zpowers_le.mpr hz.mem he))
    have heq : zpowers z ⊔ zpowers w = B := by
      refine Subgroup.eq_of_le_of_card_ge (sup_le le_sup_right (zpowers_le.mpr hwB)) ?_
      rw [hcard2, hBc, Nat.card_zpowers, orderOf_eq_prime hzp hz1, pow_two]
    have hBcent : B ≤ centralizer ((P : Subgroup G) : Set G) := by
      rw [← heq]
      exact sup_le (zpowers_le.mpr hz.centralizes) (zpowers_le.mpr hwc)
    have hxc : x ∈ centralizer ((P : Subgroup G) : Set G) :=
      hBcent (mem_sup_left (mem_zpowers x))
    have hPC : (P : Subgroup G) ≤ centralizer ({x} : Set G) := fun g hg =>
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxc g hg)
    have := CFSG.SectionRank.pRank_mono hprime.one_lt hPC
    omega
  exact ⟨hBe, hBc, hmem, hiso, hcenter⟩

theorem exists_central_generator (hS : Situation G p P M) (hx : Point P M x) :
    ∃ z : G, Central P z ∧ omegaCenter p (P : Subgroup G) = zpowers z ∧ x ∉ zpowers z ∧
      SmallRankPlane p (P : Subgroup G) x z ∧
      sixPlane p (P : Subgroup G) x = zpowers x ⊔ zpowers z := by
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  obtain ⟨z, hz⟩ := exists_central (P := P) (fun h => hx.ne_one hprime
    (mem_bot.mp (h ▸ hx.mem)))
  have hpl := plane_of_central hS hx hz
  have hZ : omegaCenter p (P : Subgroup G) = zpowers z := by
    refine le_antisymm (fun w hw => hpl.center w hw.1 (mem_centralizer_iff.mpr hw.2.1) hw.2.2)
      (zpowers_le.mpr ⟨hz.mem, fun q hq => (mem_centralizer_iff.mp hz.centralizes q hq),
        hz.pow_eq_one⟩)
  refine ⟨z, hz, hZ, ?_, hpl, by rw [← hZ]; rfl⟩
  intro hxz
  have hcz : Nat.card (zpowers z) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hz.pow_eq_one hz.ne_one]
  have hcx : Nat.card (zpowers x) = p := by
    rw [Nat.card_zpowers, hx.order]
  have hBc := hpl.card_eq
  have hsup : zpowers x ⊔ zpowers z = zpowers z := sup_eq_right.mpr (zpowers_le.mpr hxz)
  rw [hsup, hcz] at hBc
  have hp2 := hprime.two_le
  nlinarith [pow_two p]

theorem normalizer_zpowers_le (hS : Situation G p P M) (hz : Central P z) :
    normalizer ((zpowers z : Subgroup G) : Set G) ≤ M := by
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  have hzord : orderOf z = p := orderOf_eq_prime hz.pow_eq_one hz.ne_one
  have hPC : (P : Subgroup G) ≤ centralizer ({z} : Set G) := fun g hg =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hz.centralizes g hg)
  refine hS.normalizer_zpowers_le hz.mem hzord ?_
  rw [inf_eq_left.mpr hPC]
  have := hS.four_le_pRank
  omega

theorem centralizer_singleton_le (hS : Situation G p P M) (hz : Central P z) :
    centralizer ({z} : Set G) ≤ M := by
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  have hzord : orderOf z = p := orderOf_eq_prime hz.pow_eq_one hz.ne_one
  have hPC : (P : Subgroup G) ≤ centralizer ({z} : Set G) := fun g hg =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hz.centralizes g hg)
  refine hS.centralizer_le_of_pRank (hS.sylow_le hz.mem) hzord ?_
  have h4 := hS.four_le_pRank
  have := CFSG.SectionRank.pRank_mono hprime.one_lt (le_inf hS.sylow_le hPC)
  omega

theorem normalizer_plane_le (hS : Situation G p P M) (hx : Point P M x) (hz : Central P z) :
    normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) ≤ M := by
  have hprime := hS.prime
  have hpl := plane_of_central hS hx hz
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) := hpl.isIsolatedPlane.1
  refine hS.normalizer_le (P.isPGroup'.to_le hBP) (hBP.trans hS.sylow_le) ?_
  exact CFSG.SectionRank.le_pRank hprime.one_lt (le_refl (zpowers x ⊔ zpowers z))
    hpl.isElemAbelian hpl.card_eq

theorem centralizer_plane_le (hS : Situation G p P M) (hz : Central P z) :
    centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) ≤ M := by
  have hzB : ({z} : Set G) ⊆ ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) :=
    Set.singleton_subset_iff.mpr (mem_sup_right (mem_zpowers z))
  exact (centralizer_le hzB).trans (centralizer_singleton_le hS hz)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
