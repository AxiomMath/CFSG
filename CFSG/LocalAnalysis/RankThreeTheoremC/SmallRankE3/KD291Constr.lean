module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KD291Group
public import CFSG.HardMathSupport.Solomon.Proving.LBBalanceUp
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Reduced
public import CFSG.RankThree.PartTwo.Sec4.T444.Coprime
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Sec
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291SCField

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt KDInndiagP5)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613 (IsSecOf)

theorem kd291_hcon_of_layer_core {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (H : Subgroup Y) (hL : GLAPLayer p H = ⊥) (hO : GLAPPrimeCoreOf p H = ⊥) :
    H ⊓ centralizer (pCoreOf p H : Set Y) ≤ pCoreOf p H := by
  have htop : GLAPLayer p (⊤ : Subgroup ↥H) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 := CFSG.HardMathSupport.Solomon.Proving.lbUp_layer_top_le_comap hp H hx
    rw [hL, Subgroup.mem_comap, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact Subtype.ext h1
  have hc := GL83.hasPrimeConstraint_of_glaPLayer_eq_bot (X := ↥H) hp htop
  have hK : CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) p = ⊥ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_bot]
    exact hO
  have hcent : centralizer (CFSG.pCore p ↥H : Set ↥H) ≤ CFSG.pCore p ↥H :=
    CFSG.LocalAnalysis.RankFourTheoremC.exists_normal_isPGroup_centralizer_le_iff.1
      ((CFSG.LocalAnalysis.RankFourTheoremC.hasPrimeConstraint_iff_of_primeComplementCore_eq_bot
        hK).1 hc)
  intro x hx
  obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.1 hx
  have hxC' := Subgroup.mem_centralizer_iff.1 hxC
  have hcC : (⟨x, hxH⟩ : ↥H) ∈ centralizer (CFSG.pCore p ↥H : Set ↥H) := by
    refine Subgroup.mem_centralizer_iff.2 fun r hr => ?_
    apply Subtype.ext
    show (r : Y) * x = x * (r : Y)
    exact hxC' (r : Y) (Subgroup.mem_map_of_mem H.subtype hr)
  exact Subgroup.mem_map_of_mem H.subtype (hcent hcC)

section Transfer
variable {X : Type} [Group X] [Finite X]

theorem kd291_orderOf_mk {p : ℕ} (hp : p.Prime) {x : X} (hx : orderOf x = p) :
    orderOf (QuotientGroup.mk x : X ⧸ primeComplementCore (G := X) p) = p := by
  have hdvd : orderOf (QuotientGroup.mk x : X ⧸ primeComplementCore (G := X) p) ∣ p :=
    (orderOf_map_dvd (QuotientGroup.mk' (primeComplementCore (G := X) p)) x).trans (dvd_of_eq hx)
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | hpx
  · exfalso
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
    have hord : orderOf (⟨x, h1⟩ : primeComplementCore (G := X) p) = p := by
      rw [← orderOf_coe]
      exact hx
    have hdvdN := orderOf_dvd_natCard (⟨x, h1⟩ : primeComplementCore (G := X) p)
    rw [hord] at hdvdN
    have hcop := CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore_coprime (G := X) p
    have hpone := Nat.eq_one_of_dvd_coprimes hcop (dvd_refl p) hdvdN
    exact hp.ne_one hpone
  · exact hpx

theorem kd291_perf_quot {p : ℕ}
    (hperf : ∀ (N : Subgroup X) [N.Normal], IsPGroup p (X ⧸ N) → N = ⊤) :
    ∀ (N : Subgroup (X ⧸ primeComplementCore (G := X) p)) [N.Normal],
      IsPGroup p ((X ⧸ primeComplementCore (G := X) p) ⧸ N) → N = ⊤ := by
  intro N' _ hquot
  let φ : X →* (X ⧸ primeComplementCore (G := X) p) ⧸ N' :=
    (QuotientGroup.mk' N').comp (QuotientGroup.mk' (primeComplementCore (G := X) p))
  have hφsurj : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective N').comp (QuotientGroup.mk'_surjective _)
  have hquot' : IsPGroup p (X ⧸ φ.ker) :=
    hquot.of_equiv (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).symm
  have hker : φ.ker = ⊤ := hperf φ.ker hquot'
  refine eq_top_iff.2 ?_
  intro z _
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (primeComplementCore (G := X) p) z
  have hx : x ∈ φ.ker := by
    rw [hker]
    exact Subgroup.mem_top x
  rw [MonoidHom.mem_ker] at hx
  have hx' : QuotientGroup.mk (QuotientGroup.mk' (primeComplementCore (G := X) p) x :
      X ⧸ primeComplementCore (G := X) p) = (1 : (X ⧸ primeComplementCore (G := X) p) ⧸ N') := hx
  exact (QuotientGroup.eq_one_iff _).1 hx'

theorem kd291_exists_sylow_map {p : ℕ} (hp : p.Prime) (P : Sylow p X) :
    ∃ Q : Sylow p (X ⧸ primeComplementCore (G := X) p),
      (Q : Subgroup (X ⧸ primeComplementCore (G := X) p)) =
        (P : Subgroup X).map (QuotientGroup.mk' (primeComplementCore (G := X) p)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact ⟨Sylow.mapSurjective (QuotientGroup.mk'_surjective (primeComplementCore (G := X) p)) P,
    rfl⟩

theorem kd291_aux_T2_not_dvd {p : ℕ} (hp : p.Prime) :
    ¬ p ∣ Nat.card (QuotientGroup.mk' (primeComplementCore (G := X) p)).ker := by
  rw [QuotientGroup.ker_mk']
  exact (Nat.Prime.coprime_iff_not_dvd hp).1
    (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore_coprime (G := X) p)

theorem kd291_aux_T2_centralizer_zpowers {G : Type*} [Group G] (g : G) :
    Subgroup.centralizer ((Subgroup.zpowers g : Subgroup G) : Set G) =
      Subgroup.centralizer ({g} : Set G) := by
  ext k
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hk
    exact (hk g (Subgroup.mem_zpowers g)).symm
  · intro hk h hh
    have hh' : h ∈ Subgroup.zpowers g := hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh'
    exact Commute.zpow_left (show Commute g k from hk.symm) n

theorem kd291_aux_T2_cent_map {p : ℕ} (hp : p.Prime) {x : X} (hx : orderOf x = p) :
    (Subgroup.centralizer ({x} : Set X)).map
        (QuotientGroup.mk' (primeComplementCore (G := X) p)) =
      Subgroup.centralizer ({(QuotientGroup.mk x : X ⧸ primeComplementCore (G := X) p)} :
        Set (X ⧸ primeComplementCore (G := X) p)) := by
  have hZ : IsPGroup p (Subgroup.zpowers x : Subgroup X) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hC :=
    CFSG.RankThreeEvenClassification.Helpers.centralizer_map_eq_of_pGroup_prime_complement_kernel
    (G := X) (H := X ⧸ primeComplementCore (G := X) p) p hp
    (QuotientGroup.mk' (primeComplementCore (G := X) p))
    (QuotientGroup.mk'_surjective _) (kd291_aux_T2_not_dvd (X := X) hp) (Subgroup.zpowers x) hZ
  rw [MonoidHom.map_zpowers, kd291_aux_T2_centralizer_zpowers,
    kd291_aux_T2_centralizer_zpowers] at hC
  exact hC

theorem kd291_pRank_quot {p : ℕ} (hp : p.Prime) (P : Sylow p X) {n : ℕ}
    (hP : Open.pRank p (P : Subgroup X) = n) :
    Open.pRank p (⊤ : Subgroup (X ⧸ primeComplementCore (G := X) p)) = n := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore_quotient_pRank_eq (G := X) p hp,
    ← (CFSG.SectionRank.pRank_sylow P).1, hP]

theorem kd291_pRank_cent_quot {p : ℕ} (hp : p.Prime) {x : X} (hx : orderOf x = p) {k : ℕ}
    (hC : Open.pRank p (centralizer ({x} : Set X)) ≤ k) :
    Open.pRank p (centralizer ({(QuotientGroup.mk x : X ⧸ primeComplementCore (G := X) p)} :
      Set (X ⧸ primeComplementCore (G := X) p))) ≤ k := by
  rw [← kd291_aux_T2_cent_map hp hx]
  exact (CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd hp
    (QuotientGroup.mk' (primeComplementCore (G := X) p)) (kd291_aux_T2_not_dvd (X := X) hp)
    (centralizer ({x} : Set X))).trans hC

theorem kd291_isSecOf_quot {p : ℕ} (hp : p.Prime) {x : X} (hx : orderOf x = p) (S : Type)
    [Group S] [IsSimpleGroup S] (hnab : ¬ ∀ a b : S, a * b = b * a) (h5 : p ∣ Nat.card S)
    (h : IsSecOf (centralizer ({x} : Set X)) S) :
    IsSecOf (centralizer ({(QuotientGroup.mk x : X ⧸ primeComplementCore (G := X) p)} :
      Set (X ⧸ primeComplementCore (G := X) p))) S := by
  rw [← kd291_aux_T2_cent_map hp hx]
  refine CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613.IsSecOf.map_hom
    (QuotientGroup.mk' (primeComplementCore (G := X) p)) h5 ?_ hnab h
  intro hd
  exact kd291_aux_T2_not_dvd (X := X) hp (dvd_trans hd (Subgroup.card_dvd_of_le inf_le_left))

end Transfer

theorem kd291_step0a {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y] [Finite Y] (Q : Sylow p Y)
    {x : Y} (hxQ : x ∈ (Q : Subgroup Y)) (hx : orderOf x = p)
    (hQ : 3 ≤ Open.pRank p (Q : Subgroup Y))
    (hC : Open.pRank p (centralizer ({x} : Set Y)) ≤ 2) :
    ∃ w ∈ (Q : Subgroup Y), orderOf w = p ∧ (∀ y ∈ (Q : Subgroup Y), y * w = w * y) ∧
      (∀ z ∈ (Q : Subgroup Y), (∀ y ∈ (Q : Subgroup Y), y * z = z * y) → z ^ p = 1 →
        z ∈ zpowers w) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hxnc : ¬ ∀ y ∈ (Q : Subgroup Y), y * x = x * y := by
    intro h
    have hle : (Q : Subgroup Y) ≤ centralizer ({x} : Set Y) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact (h y hy).symm
    have hmono := CFSG.SectionRank.pRank_mono hp.one_lt hle
    omega
  obtain ⟨w, hwQ, hw5, hwc⟩ : ∃ w ∈ (Q : Subgroup Y), orderOf w = p ∧
      (∀ y ∈ (Q : Subgroup Y), y * w = w * y) := by
    haveI : Nontrivial ↥(Q : Subgroup Y) :=
      ⟨⟨⟨x, hxQ⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩⟩
    have hQp : IsPGroup p ↥(Q : Subgroup Y) := Q.isPGroup'
    haveI : Nontrivial ↥(Subgroup.center ↥(Q : Subgroup Y)) := hQp.center_nontrivial
    have hZp : IsPGroup p ↥(Subgroup.center ↥(Q : Subgroup Y)) := hQp.to_subgroup _
    have hZ1 : 1 < Nat.card ↥(Subgroup.center ↥(Q : Subgroup Y)) := Finite.one_lt_card
    have hZdvd : p ∣ Nat.card ↥(Subgroup.center ↥(Q : Subgroup Y)) := by
      rcases hZp.card_eq_or_dvd with h1 | h1
      · exfalso
        omega
      · exact h1
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hZdvd
    refine ⟨g.1.1, g.1.2, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hg]
    · intro y hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 g.2 ⟨y, hy⟩)
  refine ⟨w, hwQ, hw5, hwc, ?_⟩
  intro z hzQ hzc hz5
  by_contra hzw
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact hzw (Subgroup.one_mem _)
  have hz5' : orderOf z = p := orderOf_eq_prime hz5 hz1
  have hcomm : Commute w z := (hwc z hzQ).symm
  obtain ⟨hBel, hBcard⟩ := kd291_pair_data hcomm hw5 hz5' hzw
  have hBQ : zpowers w ⊔ zpowers z ≤ centralizer ((Q : Subgroup Y) : Set Y) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      exact fun h hh => hwc h hh
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      exact fun h hh => hzc h hh
  have hBcx : zpowers w ⊔ zpowers z ≤ centralizer ({x} : Set Y) := by
    intro b hb
    have hbC := Subgroup.mem_centralizer_iff.1 (hBQ hb)
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact hbC x hxQ
  have hxB : x ∉ zpowers w ⊔ zpowers z := by
    intro hxB
    apply hxnc
    intro y hy
    exact Subgroup.mem_centralizer_iff.1 (hBQ hxB) y hy
  have hBx : (zpowers w ⊔ zpowers z) ⊓ zpowers x = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgB, hgx⟩ := hg
    rw [Subgroup.mem_bot]
    by_contra hg1
    have hgo : orderOf g = p := by
      have hd : orderOf g ∣ p := by
        rw [← hx]
        exact orderOf_dvd_of_mem_zpowers hgx
      rcases (Nat.dvd_prime hp).1 hd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.1 h1) hg1
      · exact h1
    have hle : zpowers g ≤ zpowers x := Subgroup.zpowers_le.2 hgx
    have hcard : Nat.card (zpowers x) ≤ Nat.card (zpowers g) :=
      le_of_eq (by rw [Nat.card_zpowers, Nat.card_zpowers, hx, hgo])
    have heq : zpowers g = zpowers x := Subgroup.eq_of_le_of_card_ge hle hcard
    have hxg : x ∈ zpowers g := by
      rw [heq]
      exact Subgroup.mem_zpowers x
    exact hxB ((Subgroup.zpowers_le.2 hgB) hxg)
  have hxel : IsElemAbelian p (zpowers x) := by
    rw [Subgroup.zpowers_eq_closure]
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · intro a ha b hb
      rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb]
    · intro a ha
      rw [Set.mem_singleton_iff] at ha
      rw [ha, ← hx]
      exact pow_orderOf_eq_one x
  have hc : ∀ a ∈ zpowers w ⊔ zpowers z, ∀ b ∈ zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hax : Commute a x :=
      (Subgroup.mem_centralizer_iff.1 (hBcx ha) x (Set.mem_singleton x)).symm
    exact hax.zpow_right k
  have hEel : IsElemAbelian p ((zpowers w ⊔ zpowers z) ⊔ zpowers x) :=
    IsElemAbelian.sup_of_commute hBel hxel hc
  have hEcard : Nat.card ↥((zpowers w ⊔ zpowers z) ⊔ zpowers x) = p ^ 3 := by
    rw [kd291_card_sup_of_commute hBx hc, hBcard, Nat.card_zpowers, hx]
    ring
  have hEx : (zpowers w ⊔ zpowers z) ⊔ zpowers x ≤ centralizer ({x} : Set Y) := by
    refine sup_le hBcx ?_
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
  have h3 : 3 ≤ CFSG.Open.pRank p (centralizer ({x} : Set Y)) :=
    CFSG.SectionRank.le_pRank hp.one_lt hEx hEel hEcard
  omega

theorem kd291_aux_S0B_pow_prime {G : Type} [Group G] (p : ℕ) (k : ℕ) :
    ∀ x : G, x ≠ 1 → x ^ p ^ k = 1 → ∃ j : ℕ, x ^ j ≠ 1 ∧ (x ^ j) ^ p = 1 := by
  induction k with
  | zero =>
    intro x hx h
    rw [pow_zero, pow_one] at h
    exact absurd h hx
  | succ k ih =>
    intro x hx h
    by_cases hk : x ^ p ^ k = 1
    · exact ih x hx hk
    · refine ⟨p ^ k, hk, ?_⟩
      rw [← pow_mul, ← pow_succ]
      exact h

theorem kd291_step0b {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y] [Finite Y]
    (hY : primeComplementCore (G := Y) p = ⊥) (Q : Sylow p Y) {w : Y}
    (hwQ : w ∈ (Q : Subgroup Y)) (hwo : orderOf w = p)
    (hwc : ∀ y ∈ (Q : Subgroup Y), y * w = w * y)
    (hu : ∀ z ∈ (Q : Subgroup Y), (∀ y ∈ (Q : Subgroup Y), y * z = z * y) → z ^ p = 1 →
      z ∈ zpowers w)
    (N : Subgroup Y) [N.Normal] (hN : N ≠ ⊥) : w ∈ N := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpN : p ∣ Nat.card N := by
    by_contra h
    have hcop : Nat.Coprime p (Nat.card N) :=
      (Nat.Prime.coprime_iff_not_dvd hp).2 h
    have hle : N ≤ primeComplementCore p := le_sSup ⟨inferInstance, hcop⟩
    rw [hY, le_bot_iff] at hle
    exact hN hle
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p hpN
  have hxN : (x : Y) ∈ N := x.2
  have hxp : orderOf (x : Y) = p := (Subgroup.orderOf_coe x).trans hx
  have hx1 : (x : Y) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxp
    exact absurd hxp hp.one_lt.ne
  have hcyc : IsPGroup p (zpowers (x : Y)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxp, pow_one])
  obtain ⟨Q', hQ'⟩ := IsPGroup.exists_le_sylow hcyc
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y Q' Q
  have hxQ' : (x : Y) ∈ (Q' : Subgroup Y) := hQ' (Subgroup.mem_zpowers _)
  have hmQ : g * (x : Y) * g⁻¹ ∈ (Q : Subgroup Y) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul (x : Y) (MulAut.conj g) (Q' : Subgroup Y) hxQ'
  have hNn : N.Normal := inferInstance
  have hmN : g * (x : Y) * g⁻¹ ∈ N := hNn.conj_mem _ hxN g
  have hm1 : g * (x : Y) * g⁻¹ ≠ 1 := by
    intro h
    apply hx1
    simpa using h
  haveI : Group.IsNilpotent (Q : Subgroup Y) := IsPGroup.isNilpotent Q.isPGroup'
  have hM : N.subgroupOf (Q : Subgroup Y) ≠ ⊥ := by
    refine Subgroup.ne_bot_iff_exists_ne_one.2
      ⟨⟨⟨g * (x : Y) * g⁻¹, hmQ⟩, Subgroup.mem_subgroupOf.2 hmN⟩, fun h => hm1 ?_⟩
    exact congrArg (fun t : ↥(N.subgroupOf (Q : Subgroup Y)) => (t : Y)) h
  obtain ⟨z, hzN, hzQ, hzc, hz1, k, hzk⟩ :
      ∃ z : Y, z ∈ N ∧ z ∈ (Q : Subgroup Y) ∧ (∀ y ∈ (Q : Subgroup Y), y * z = z * y) ∧
        z ≠ 1 ∧ ∃ k : ℕ, z ^ p ^ k = 1 := by
    obtain ⟨⟨z', hz'⟩, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hM)
    obtain ⟨hz'M, hz'c⟩ := Subgroup.mem_inf.1 hz'
    have hz'1 : z' ≠ 1 := fun h => ha (Subtype.ext h)
    obtain ⟨k, hk⟩ := Q.isPGroup' z'
    refine ⟨(z' : Y), Subgroup.mem_subgroupOf.1 hz'M, z'.2, ?_,
      fun h => hz'1 (Subtype.ext h), k, ?_⟩
    · intro y hy
      have h := Subgroup.mem_center_iff.1 hz'c ⟨y, hy⟩
      exact congrArg Subtype.val h
    · have h := congrArg Subtype.val hk
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
  obtain ⟨j, hj1, hjp⟩ := kd291_aux_S0B_pow_prime p k z hz1 hzk
  have huN : z ^ j ∈ N := pow_mem hzN j
  have huQ : z ^ j ∈ (Q : Subgroup Y) := pow_mem hzQ j
  have huc : ∀ y ∈ (Q : Subgroup Y), y * z ^ j = z ^ j * y := fun y hy =>
    (show Commute y z from hzc y hy).pow_right j
  have hord : orderOf (z ^ j) = p := orderOf_eq_prime hjp hj1
  have huw : z ^ j ∈ zpowers w := hu (z ^ j) huQ huc hjp
  have heq : zpowers (z ^ j) = zpowers w :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 huw)
      (le_of_eq (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hwo]))
  have hwu : w ∈ zpowers (z ^ j) := by
    rw [heq]
    exact Subgroup.mem_zpowers w
  exact (Subgroup.zpowers_le.2 huN) hwu

theorem kd291_mem_of_perf {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hΔ : KDInndiagP5) {Y : Type}
    [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal] (hs : IsSimpleGroup L)
    (hn : ∃ a b : L, a * b ≠ b * a) (hc : IsCatalogGroup L)
    (hlu : ¬ IsLinearOrUnitaryAt p L) (hC : centralizer (L : Set Y) = ⊥)
    (hperf : ∀ (N : Subgroup Y) [N.Normal], IsPGroup p (Y ⧸ N) → N = ⊤) {x : Y}
    (hx : orderOf x = p) : x ∈ L := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  by_contra hxL
  have hxp : IsPGroup p (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨P, hP⟩ := hxp.exists_le_sylow
  obtain ⟨H, hHn, hHi⟩ := exists_index_prime_of_focal_ne P fun hF => hxL (by
    have hle := focalSubgroup_le_of_kdInndiag hΔ hp hp5 L hs hn hc hlu hC P
    rw [hF] at hle
    exact hle (hP (mem_zpowers x)))
  haveI := hHn
  have hpg : IsPGroup p (Y ⧸ H) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [← Subgroup.index_eq_card, hHi, pow_one]
  have htop := hperf H hpg
  rw [htop, Subgroup.index_top] at hHi
  exact hp.one_lt.ne hHi

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
