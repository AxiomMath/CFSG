module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5LowExc
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

theorem exists_lift_pow_eq_one {A K : Type} [CommGroup A] [Finite A] [Group K] (F : A →* K)
    {p : ℕ} (hp : p.Prime) {w : A} {z : K} (hw : F w = z) {k : ℕ} (hz : z ^ (p ^ k) = 1) :
    ∃ v : A, F v = z ∧ ∃ j : ℕ, v ^ (p ^ j) = 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero, pow_one] at hz
    refine ⟨1, by rw [map_one, hz], 0, by simp⟩
  have hm0 : orderOf w ≠ 0 := (orderOf_pos w).ne'
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 p hp.ne_one
  have hcop : Nat.Coprime b (p ^ k) :=
    Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp).2 hb).symm
  obtain ⟨c, -, hc⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop
    (Nat.one_lt_pow hk.ne' hp.one_lt)
  refine ⟨w ^ (b * c), ?_, a, ?_⟩
  · rw [map_pow, hw, pow_eq_pow_mod (b * c) hz, hc, pow_one]
  · rw [← pow_mul]
    have h : b * c * p ^ a = orderOf w * c := by rw [hab]; ring
    rw [h, pow_mul, pow_orderOf_eq_one, one_pow]

theorem card_le_of_pow_eq_one_of_le_zpowers {K : Type} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (g : K) {E : Subgroup K} (hE : E ≤ Subgroup.zpowers g)
    (hexp : ∀ x ∈ E, x ^ p = 1) : Nat.card E ≤ p := by
  let E' : Subgroup (Subgroup.zpowers g) := E.subgroupOf (Subgroup.zpowers g)
  have hcard : Nat.card E' = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv
  have hdvd : Monoid.exponent E' ∣ p := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro y
    have hyE : ((y : Subgroup.zpowers g) : K) ∈ E := (Subgroup.mem_subgroupOf).1 y.2
    have := hexp _ hyE
    apply Subtype.ext
    apply Subtype.ext
    simpa using this
  rw [IsCyclic.exponent_eq_card] at hdvd
  rw [← hcard]
  exact Nat.le_of_dvd hp.pos hdvd

theorem pRank_le_one_of_pElem {A K : Type} [CommGroup A] [Finite A] [Group K] [Finite K]
    {p : ℕ} (hp : p.Prime) (F : A →* K) (Z : Subgroup K)
    (hrange : ∀ v, F v ∈ Z) (hsurj : ∀ z ∈ Z, ∃ v, F v = z)
    (g0 : A) (hg0 : ∀ v : A, (∃ j : ℕ, v ^ (p ^ j) = 1) → v ∈ Subgroup.zpowers g0) :
    CFSG.Open.pRank p Z ≤ 1 := by
  refine CFSG.SectionRank.pRank_le hp.one_lt (k := 1) fun E hEZ hE => ?_
  have hEle : E ≤ Subgroup.zpowers (F g0) := by
    intro x hx
    have hxZ : x ∈ Z := hEZ hx
    have hxp : x ^ (p ^ 1) = 1 := by rw [pow_one]; exact hE.2 x hx
    obtain ⟨w, hw⟩ := hsurj x hxZ
    obtain ⟨v, hv, j, hj⟩ := exists_lift_pow_eq_one F hp hw hxp
    have hvz : v ∈ Subgroup.zpowers g0 := hg0 v ⟨j, hj⟩
    rw [← hv, ← MonoidHom.map_zpowers]
    exact Subgroup.mem_map_of_mem F hvz
  have := card_le_of_pow_eq_one_of_le_zpowers hp (F g0) hEle (fun x hx => hE.2 x hx)
  rw [pow_one]
  exact this


theorem pow_components {M N : Type} [Group M] [Group N] (x : M × N) (m : ℕ)
    (hx : x ^ m = 1) : x.1 ^ m = 1 ∧ x.2 ^ m = 1 := by
  constructor
  · have h := map_pow (MonoidHom.fst M N) x m
    rw [hx, map_one] at h
    exact h.symm
  · have h := map_pow (MonoidHom.snd M N) x m
    rw [hx, map_one] at h
    exact h.symm

theorem eq_one_of_pow_eq_one_of_coprime {c : ℕ} (hc : 0 < c) (x : Multiplicative (ZMod c))
    {k : ℕ} (hk : Nat.Coprime k c) (hx : x ^ k = 1) : x = 1 := by
  haveI : NeZero c := ⟨hc.ne'⟩
  have hcard : Nat.card (Multiplicative (ZMod c)) = c := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod c) ≃ ZMod c)]
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have h1 : orderOf x ∣ k := orderOf_dvd_of_pow_eq_one hx
  have h2 : orderOf x ∣ c := by
    have := orderOf_dvd_natCard x
    rwa [hcard] at this
  have h3 : orderOf x ∣ Nat.gcd k c := Nat.dvd_gcd h1 h2
  rw [hk.gcd_eq_one] at h3
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem pElem_mem_zpowers {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {t : StatedLieTag}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .E6 ∨ t = .twistedE6) {n p' f : ℕ} (hne : p ≠ p')
    (hadm : StatedLieAdmissible t n p' f)
    (v : (generic t n p' f × exceptional t n p' f)) {j : ℕ} (hj : v ^ (p ^ j) = 1) :
    v ∈ Subgroup.zpowers
      ((Multiplicative.ofAdd (1 : ZMod (genericOrders t n p' f).1),
        (1 : Multiplicative (ZMod (genericOrders t n p' f).2))),
        (1 : exceptional t n p' f)) := by
  haveI : NeZero (genericOrders t n p' f).1 :=
    ⟨(CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.genericOrders_fst_pos hadm).ne'⟩
  obtain ⟨⟨g1, g2⟩, ⟨h1, h2⟩⟩ := v
  obtain ⟨hu, hw⟩ := pow_components _ _ hj
  obtain ⟨hg1, hg2⟩ := pow_components _ _ hu
  obtain ⟨hh1, hh2⟩ := pow_components _ _ hw
  obtain ⟨hc0, -⟩ := (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.exceptionalOrders_le
    t n p' f).1
  obtain ⟨hd0, -⟩ := (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.exceptionalOrders_le
    t n p' f).2
  obtain ⟨hnc, hnd⟩ := not_dvd_exceptional hp hp2 ht hne (n := n) (f := f)
  have he1 : h1 = 1 := eq_one_of_pow_eq_one_of_coprime hc0 h1
    (Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hp).2 hnc)) hh1
  have he2 : h2 = 1 := eq_one_of_pow_eq_one_of_coprime hd0 h2
    (Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)) hh2
  have hb := genericOrders_snd_eq_one ht n p' f
  have hb0 := (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.genericOrders_snd_le
    t n p' f).1
  have he3 : g2 = 1 := eq_one_of_pow_eq_one_of_coprime hb0 g2
    (by rw [hb]; exact Nat.coprime_one_right _) hg2
  subst he1 he2 he3
  have hval : g1.toAdd = g1.toAdd.val • (1 : ZMod (genericOrders t n p' f).1) := by
    rw [nsmul_one, ZMod.natCast_zmod_val]
  have hgk : g1 = (Multiplicative.ofAdd (1 : ZMod (genericOrders t n p' f).1)) ^ g1.toAdd.val := by
    rw [← ofAdd_nsmul, ← hval, ofAdd_toAdd]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, g1 = (Multiplicative.ofAdd (1 : ZMod (genericOrders t n p' f).1)) ^ k :=
    ⟨_, hgk⟩
  subst hk
  have hmem := pow_mem (Subgroup.mem_zpowers
    ((Multiplicative.ofAdd (1 : ZMod (genericOrders t n p' f).1),
      (1 : Multiplicative (ZMod (genericOrders t n p' f).2))),
      (1 : exceptional t n p' f))) k
  convert hmem using 1
  simp

theorem pRank_center_le_one {K X : Type} [Group K] [Finite K] [Group X]
    (hGA : CFSG.Open.GriessAllModelsStatement) (hK : CFSG.Open.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* X) {t : StatedLieTag} {n p' f : ℕ}
    (hm : CFSG.Models.LieModel X t n p' f)
    (ht : t = .PSL ∨ t = .PSU ∨ t = .E6 ∨ t = .twistedE6)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hne : p ≠ p') :
    CFSG.Open.pRank p (Subgroup.center K) ≤ 1 := by
  have hperf : Group.IsPerfect K := ⟨hK.1⟩
  have hqs := CFSG.RankThree.PerfectCover.centralQuotientMap_surjective e
  have hker := CFSG.RankThree.PerfectCover.centralQuotientMap_ker e
  obtain ⟨-, ⟨eg⟩⟩ := hGA X t n p' f hm
  let φ := CFSG.RankThree.PerfectCover.hopfMultiplierToKer
    (CFSG.RankThree.PerfectCover.centralQuotientMap e) hqs hker.le
  let ψ : CFSG.RankThree.PerfectCover.hopfMultiplier X ≃*
      (generic t n p' f × exceptional t n p' f) :=
    (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).symm.trans eg
  let F : (generic t n p' f × exceptional t n p' f) →* K :=
    (CFSG.RankThree.PerfectCover.centralQuotientMap e).ker.subtype.comp
      (φ.comp ψ.symm.toMonoidHom)
  have hrange : ∀ v, F v ∈ Subgroup.center K := by
    intro v
    rw [← hker]
    exact (φ _).2
  have hsurj : ∀ z ∈ Subgroup.center K, ∃ v, F v = z := by
    intro z hz
    have hzk : z ∈ (CFSG.RankThree.PerfectCover.centralQuotientMap e).ker := by
      rw [hker]
      exact hz
    obtain ⟨m, hm'⟩ := CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective
      (CFSG.RankThree.PerfectCover.centralQuotientMap e) hqs hker.le ⟨z, hzk⟩
    refine ⟨ψ m, ?_⟩
    change ((φ (ψ.symm (ψ m)) : (CFSG.RankThree.PerfectCover.centralQuotientMap e).ker) : K) = z
    rw [MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val hm'
  have hadm := hm.1
  haveI : NeZero (genericOrders t n p' f).1 :=
    ⟨(CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.genericOrders_fst_pos hadm).ne'⟩
  haveI : NeZero (genericOrders t n p' f).2 :=
    ⟨(CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.genericOrders_snd_le t n p' f).1.ne'⟩
  haveI : NeZero (exceptionalOrders t n p' f).1 :=
    ⟨(CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.exceptionalOrders_le t n p' f).1.1.ne'⟩
  haveI : NeZero (exceptionalOrders t n p' f).2 :=
    ⟨(CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.exceptionalOrders_le t n p' f).2.1.ne'⟩
  refine pRank_le_one_of_pElem hp F (Subgroup.center K) hrange hsurj
    (((Multiplicative.ofAdd (1 : ZMod (genericOrders t n p' f).1),
      (1 : Multiplicative (ZMod (genericOrders t n p' f).2))),
      (1 : exceptional t n p' f))) ?_
  intro v hv
  obtain ⟨j, hj⟩ := hv
  exact pElem_mem_zpowers hp hp2 ht hne hadm v hj

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
