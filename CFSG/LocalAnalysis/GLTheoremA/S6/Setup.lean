module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Common
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_8
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ}


theorem kLevel_eq_one_iff (p : ℕ) (S : Type) [Group S] : kLevel p S = 1 ↔ IsChevSimple p S := by
  classical
  unfold kLevel
  split_ifs with h1 h2 h3 <;> simp [h1]

theorem fullCoverLevel_eq_one_iff (p : ℕ) (Q : Type) [Group Q] :
    fullCoverLevel p Q = 1 ↔ K1Cover p Q := by
  classical
  unfold fullCoverLevel
  split_ifs with h1 h2 h3 <;> simp [h1]

theorem one_le_fullCoverLevel (p : ℕ) (Q : Type) [Group Q] : 1 ≤ fullCoverLevel p Q := by
  classical
  unfold fullCoverLevel
  split_ifs <;> omega

theorem k1Cover_pQuot_iff (hp : p.Prime) {X L : Subgroup G} (hL : GLAPComponent p X L) :
    K1Cover p (PQuot p L) ↔ IsChevSimple p (PSimple p L) :=
  ⟨fun h => h.2, fun h => ⟨isQuasisimple_pQuot_of_glaPComponent hp hL, h⟩⟩

theorem tripleLevel_eq_one_iff (hp : p.Prime) {X : Subgroup G} (B : Subgroup G) {L : Subgroup G}
    (hL : GLAPComponent p X L) :
    tripleLevel p B L = 1 ↔ ¬ IsGStar p B L ∧ IsChevSimple p (PSimple p L) := by
  classical
  unfold tripleLevel
  split_ifs with h
  · simp [h]
  · have : min 4 (fullCoverLevel p (PQuot p L)) = 1 ↔ fullCoverLevel p (PQuot p L) = 1 := by omega
    rw [this, fullCoverLevel_eq_one_iff, k1Cover_pQuot_iff hp hL]
    simp [h]

theorem triple_of_dLevel_eq_one (hp : p.Prime) (hd : dLevel G p = 1) {B : Subgroup G} {x : G}
    {L : Subgroup G} (h : IsSTriple p B x L) : ¬ IsGStar p B L ∧ IsChevSimple p (PSimple p L) := by
  have h1 := tripleLevel_le_dLevel h
  rw [hd] at h1
  have hpos : 1 ≤ tripleLevel p B L := by
    classical
    unfold tripleLevel
    split_ifs
    · omega
    · have := one_le_fullCoverLevel p (PQuot p L)
      omega
  exact (tripleLevel_eq_one_iff hp B h.2.2).1 (le_antisymm h1 hpos)

theorem kGroup_centralizer (hc : S6Ctx G p) {x : G} (hx : x ≠ 1) :
    CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) :=
  isKGroup_of_isKProper hc.kProper (centralizer_ne_top_of_ne_one hc.simple hc.nonabelian hx)

theorem commutator_commutator_eq_of_isPGroup (hp : p.Prime) {B T : Subgroup G}
    (hB : IsPGroup p B) (hT : IsPGroup 2 T) (hp2 : p ≠ 2) (hBT : B ≤ Subgroup.normalizer (T : Set G)) :
    (⁅(⁅T, B⁆ : Subgroup G), B⁆ : Subgroup G) = ⁅T, B⁆ := by
  refine i321UsedAt_holds p hp T B ?_ hBT ?_
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hT
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  · intro N hNB hNn hNidx
    haveI : Fact p.Prime := ⟨hp⟩
    have hidx : (N.subgroupOf B).index ∣ Nat.card B := Subgroup.index_dvd_card _
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hB
    rw [hn] at hidx
    have h1 : (N.subgroupOf B).index = 1 := by
      by_contra hne
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hidx
      have hk0 : k ≠ 0 := fun h0 => hne (by rw [hk, h0, pow_zero])
      exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one (by
        have := Nat.Coprime.coprime_dvd_right (show p ∣ (N.subgroupOf B).index from
          hk ▸ dvd_pow_self p hk0) hNidx
        simpa using this))
    have : N.subgroupOf B = ⊤ := Subgroup.index_eq_one.1 h1
    exact le_antisymm (le_trans hNB (le_refl _)) (by
      intro b hb
      have : (⟨b, hb⟩ : B) ∈ N.subgroupOf B := by rw [‹N.subgroupOf B = ⊤›]; exact Subgroup.mem_top _
      exact this)

theorem exists_two_group_comm_eq (hp : p.Prime) (hp2 : p ≠ 2) {B : Subgroup G} {x : G}
    (hB : IsPGroup p B) (hx : IsEssential p B x) :
    ∃ T : Subgroup G, T ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 2 T ∧
      B ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, B⁆ : Subgroup G) = T ∧ T ≠ ⊥ := by
  obtain ⟨-, -, T, hTC, hT2, hBT, hne, -⟩ := hx
  have hle : (⁅T, B⁆ : Subgroup G) ≤ T := commutator_le_left_of_normalizes hBT
  refine ⟨⁅T, B⁆, hle.trans hTC, IsPGroup.to_le hT2 hle, le_normalizer_commutator hBT Subgroup.le_normalizer,
    commutator_commutator_eq_of_isPGroup hp hB hT2 hp2 hBT, hne⟩

theorem pow_four_le_card_of_bmax (hc : S6Ctx G p) {B : Subgroup G} (hB : GLAIsBmax p B) :
    p ^ 4 ≤ Nat.card B := by
  rw [hB.2.1]
  exact Nat.pow_le_pow_right hc.prime.pos hc.rank_ge

theorem exists_pow_eq_one_noncomm_of_component (hp : p.Prime) (hp2 : p ≠ 2) {X K : Subgroup G}
    (hK : GLAPComponent p X K) : ∃ w ∈ K, w ^ p = 1 ∧ ∃ k ∈ K, k * w ≠ w * k := by
  haveI : Fact p.Prime := ⟨hp⟩
  let π : ↥K →* PQuot p K := QuotientGroup.mk' (GLAPPrimeCore p ↥K)
  have hKc : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥K)) := CFSG.pPrimeCore_coprime_card
  obtain ⟨yb, hyord, hycen⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
      (isQuasisimple_pQuot_of_glaPComponent hp hK) hp hp2 (dvd_card_pQuot_of_component hp hK)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective yb
  have hpy : π y ^ p = 1 := by
    have h := pow_orderOf_eq_one (π y)
    have hyord' : orderOf (π y) = p := hyord
    rwa [hyord'] at h
  obtain ⟨a, m, hm, hkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' p hp.ne_one
  set v : ↥K := y ^ m with hv
  have hπv : π v = π y ^ m := by rw [hv, map_pow]
  have hvK : v ^ p ∈ GLAPPrimeCore p ↥K := by
    have : π (v ^ p) = 1 := by
      rw [map_pow, hπv, ← pow_mul, mul_comm, pow_mul, hpy, one_pow]
    exact (QuotientGroup.eq_one_iff _).1 this
  have hpow : (v ^ p) ^ (p ^ a) = 1 := by
    have h1 : y ^ (p ^ a * m) = 1 := hkm ▸ pow_orderOf_eq_one y
    calc (v ^ p) ^ (p ^ a) = (y ^ (p ^ a * m)) ^ p := by
          rw [hv, ← pow_mul, ← pow_mul, ← pow_mul]
          congr 1
          ring
      _ = 1 := by rw [h1, one_pow]
  have hv1 : v ^ p = 1 := by
    have h1 : orderOf (v ^ p) ∣ p ^ a := orderOf_dvd_of_pow_eq_one hpow
    have h2 : orderOf (v ^ p) ∣ Nat.card (GLAPPrimeCore p ↥K) :=
      Subgroup.orderOf_dvd_natCard _ hvK
    have h3 := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left a hKc)] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  refine ⟨(v : G), v.2, ?_, ?_⟩
  · exact_mod_cast hv1
  by_contra hcon
  push Not at hcon
  have hvcomm : ∀ k : ↥K, k * v = v * k := fun k => Subtype.ext (hcon (k : G) k.2)
  have hπvc : π v ∈ Subgroup.center (PQuot p K) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥K) q
    show π k * π v = π v * π k
    rw [← map_mul, ← map_mul, hvcomm k]
  rw [hπv] at hπvc
  obtain ⟨s, t, hst⟩ := Nat.Coprime.isCoprime ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  have e : (1 : ℤ) = (p : ℤ) * s + (m : ℤ) * t := by linarith [hst]
  have hfin : π y = (π y ^ m) ^ t := by
    calc π y = π y ^ (1 : ℤ) := (zpow_one _).symm
      _ = π y ^ ((p : ℤ) * s + (m : ℤ) * t) := by rw [← e]
      _ = (π y ^ m) ^ t := by
        rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hpy, one_zpow, one_mul]
  have hyc : π y ∈ Subgroup.center (PQuot p K) := by
    rw [hfin]
    exact Subgroup.zpow_mem _ hπvc t
  exact hycen hyc

theorem sstarMax_layer_eq (hc : S6Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) : GLAPLayer p (Subgroup.centralizer ({x} : Set G)) = L := by
  have hp := hc.prime
  have hp2 := hc.odd
  have hT := IsSStarMax.inT hc h
  have hxB : x ∈ B := hT.2.1
  have hx1 : x ≠ 1 := hT.2.2.1
  have hLc : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L := hT.2.2.2.1
  have hxp : x ^ p = 1 := hT.1.1.2 x hxB
  have hxL : x ∈ centModSubgroup p L := by
    refine centMod_iff.1 (centMod_of_mem_centralizer ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.1 (hLc.1 hl)
  apply le_antisymm
  · refine sSup_le fun J hJ => ?_
    by_cases hJL : J = L
    · exact hJL ▸ le_rfl
    exfalso
    have hJCm : J ≤ centModSubgroup p L := le_centModSubgroup_of_ne hp hJ hLc hJL
    obtain ⟨w, hwJ, hwp, k, hkJ, hkw⟩ := exists_pow_eq_one_noncomm_of_component hp hp2 hJ
    have hkx : Commute k x := Subgroup.mem_centralizer_singleton_iff.1 (hJ.1 hkJ)
    have hwx : w * x = x * w := Subgroup.mem_centralizer_singleton_iff.1 (hJ.1 hwJ)
    have hwnx : w ∉ Subgroup.zpowers x := by
      intro hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      exact hkw (hkx.zpow_right n).eq
    obtain ⟨hE, hcard⟩ := Prop53.isElemAbelian_card_sup_zpowers hp hwx hwp hxp hx1 hwnx
    have hle : Subgroup.zpowers w ⊔ Subgroup.zpowers x ≤ centModSubgroup p L :=
      sup_le (Subgroup.zpowers_le.2 (hJCm hwJ)) (Subgroup.zpowers_le.2 hxL)
    have hcycS : IsCyclic (Subgroup.zpowers w ⊔ Subgroup.zpowers x : Subgroup G) :=
      IsSStarMax.cycMod h (Subgroup.zpowers w ⊔ Subgroup.zpowers x)
        (fun g hg => centMod_iff.2 (hle hg)) (isPGroup_of_isElemAbelian hE)
    have hdiv : Nat.card (Subgroup.zpowers w ⊔ Subgroup.zpowers x : Subgroup G) ≤ p :=
      card_le_of_isCyclic_of_pow hp hcycS (fun d hd => hE.2 d hd)
    rw [hcard] at hdiv
    have h2 := hp.two_le
    nlinarith
  · exact le_sSup hLc

end CFSG.LocalAnalysis.GLTheoremA
