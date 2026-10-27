module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThirteen
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Reduce

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Subgroup CFSG.Blueprint CFSG.Monster.GMS CFSG.Monster.Existence
  CFSG.EvenSporadicStandard.HypOne.BabyHyp.B68 CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThirteen

section Abstract

variable {G : Type} [Group G]

theorem commute_conj_of_commute {a b : G} (h : a * b = b * a) (c : G) :
    (c⁻¹ * a * c) * (c⁻¹ * b * c) = (c⁻¹ * b * c) * (c⁻¹ * a * c) :=
  calc (c⁻¹ * a * c) * (c⁻¹ * b * c) = c⁻¹ * (a * b) * c := by group
    _ = c⁻¹ * (b * a) * c := by rw [h]
    _ = (c⁻¹ * b * c) * (c⁻¹ * a * c) := by group

theorem exists_fixed_of_prime [Finite G] {p : ℕ} (hp : p.Prime) {a : G} (ha : orderOf a = p)
    {F : Set G} (hF : ∀ g ∈ zpowers a, ∀ s ∈ F, g * s * g⁻¹ ∈ F) (hdvd : ¬ p ∣ F.ncard) :
    ∃ s ∈ F, a * s = s * a := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI : MulAction (zpowers a) F := conjAction (zpowers a) F hF
  have hP : IsPGroup p (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  have hcard : ¬ p ∣ Nat.card F := by rwa [Nat.card_coe_set_eq]
  obtain ⟨s, hs⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card F hcard
  refine ⟨s.1, s.2, ?_⟩
  have h := congrArg Subtype.val (hs ⟨a, mem_zpowers a⟩)
  have h' : a * (s : G) * a⁻¹ = s := h
  rw [mul_inv_eq_iff_eq_mul] at h'
  exact h'

theorem false_of_cap13 [Finite G] {N : Fin 4 → ℕ} (hCap : Cap13 (G := G) N) {u x a : G}
    (hu : Inv N 0 u) (hx : orderOf x = 13) (hux : u * x = x * u) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hq13 : q ≠ 13) (ha : orderOf a = q) (hau : a * u = u * a)
    (hax : a * x = x * a) : False := by
  have hD := hCap hu hx hux
  set D : Subgroup G := centralizer ({u} : Set G) ⊓ centralizer ({x} : Set G) with hDdef
  have hxD : x ∈ D :=
    ⟨mem_centralizer_singleton_iff.2 hux.symm, mem_centralizer_singleton_iff.2 rfl⟩
  have huD : u ∈ D := ⟨mem_centralizer_singleton_iff.2 rfl, mem_centralizer_singleton_iff.2 hux⟩
  have haD : a ∈ D := ⟨mem_centralizer_singleton_iff.2 hau, mem_centralizer_singleton_iff.2 hax⟩
  have h13 : 13 ∣ Nat.card D := hx ▸ Subgroup.orderOf_dvd_natCard D hxD
  have h2 : 2 ∣ Nat.card D := hu.1 ▸ Subgroup.orderOf_dvd_natCard D huD
  have hqD : q ∣ Nat.card D := ha ▸ Subgroup.orderOf_dvd_natCard D haD
  have h26 : 26 ∣ Nat.card D := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 13) h2 h13
    simpa using this
  have hcop : Nat.Coprime 26 q := by
    have h2q : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).2 (Ne.symm hq2)
    have h13q : Nat.Coprime 13 q :=
      (Nat.coprime_primes (by norm_num) hq).2 (Ne.symm hq13)
    have := (Nat.Coprime.mul_right h2q.symm h13q.symm).symm
    simpa using this
  have h26q : 26 * q ∣ Nat.card D := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h26 hqD
  have hle : 26 * q ≤ 52 := (Nat.le_of_dvd Nat.card_pos h26q).trans hD
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    omega
  omega

theorem false_of_fixed_set [Finite G] {N : Fin 4 → ℕ} (hCap : Cap13 (G := G) N) {x z w r : G}
    (hx : orderOf x = 13) (hz : orderOf z = 5) (hzx : z * x = x * z) (hw : orderOf w = 3)
    (hwx : w * x = x * w) (hr : Inv N 0 r) (hrx : r * x = x * r)
    (hF : {s : G | Inv N 0 s ∧ s * x = x * s}.ncard ≤ 9) : False := by
  set F : Set G := {s : G | Inv N 0 s ∧ s * x = x * s} with hFdef
  have hFpos : 1 ≤ F.ncard := by
    have hrF : r ∈ F := ⟨hr, hrx⟩
    exact Nat.one_le_iff_ne_zero.2 ((Set.ncard_ne_zero_of_mem hrF (Set.toFinite F)))
  have hclosed : ∀ c : G, c * x = x * c → ∀ s ∈ F, c * s * c⁻¹ ∈ F := by
    intro c hcx s hs
    have hc : Commute c x := hcx
    have hs' : Commute s x := hs.2
    refine ⟨Inv.of_isConj hs.1 (isConj_iff.2 ⟨c, rfl⟩), ?_⟩
    exact ((hc.mul_left hs').mul_left hc.inv_left).eq
  have hpowF : ∀ {a : G}, a * x = x * a → ∀ g ∈ zpowers a, ∀ s ∈ F, g * s * g⁻¹ ∈ F := by
    intro a hax g hg s hs
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
    exact hclosed _ (Commute.zpow_left (show Commute a x from hax) k).eq s hs
  by_cases h5 : 5 ∣ F.ncard
  · have hcard : F.ncard = 5 := by
      obtain ⟨k, hk⟩ := h5
      omega
    have h3 : ¬ 3 ∣ F.ncard := by rw [hcard]; norm_num
    obtain ⟨u, hu, huw⟩ := exists_fixed_of_prime (by norm_num) hw (hpowF hwx) h3
    exact false_of_cap13 hCap hu.1 hx hu.2 (q := 3) (by norm_num) (by norm_num) (by norm_num) hw
      huw hwx
  · obtain ⟨u, hu, huz⟩ := exists_fixed_of_prime (by norm_num) hz (hpowF hzx) h5
    exact false_of_cap13 hCap hu.1 hx hu.2 (q := 5) (by norm_num) (by norm_num) (by norm_num) hz
      huz hzx

end Abstract


section BabyMonster


theorem noOrder65_B : NoOrder 65 NativeSporadic.B := by
  intro g hg
  haveI hfin : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  have hp2 : ¬ 13 ^ 2 ∣ Nat.card NativeSporadic.B := by
    rw [CFSG.RankThree.OddKernel.card_B_eq]
    norm_num
  have P := b13_parts
  have inv : ∀ {t : NativeSporadic.B}, t * t = 1 → t ≠ 1 →
      Matrix.rank (CFSG.Monster.B.bMat t - 1) = 1860 → BabyInv 0 t := by
    intro t h1 h2 h3
    have h2' : orderOf t = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [pow_two]; exact h1) h2
    exact babyInv_zero_of_rank_1860 h2' h3
  have i1 := inv P.mul_self_t1 P.ne_one_t1 P.rank_t1
  have i2 := inv P.mul_self_t2 P.ne_one_t2 P.rank_t2
  have i5 := inv P.mul_self_t5 P.ne_one_t5 P.rank_t5
  have hF := BThirteen.ncard_commuting_le (N := babyCentOrder) (sz := babyOrbitSize)
    BThirteen.arith13_baby babyTableIV BThirteen.cap13_baby P.order_x i1 i5 i2 P.comm_t1.symm
    P.comm_t5.symm P.comm_t2.symm P.comm_t1_t5 P.ne_t5_t1 P.order_t1_t2 P.comm_g_t1 P.comm_g_t5
    P.comm_g_t2 P.conj_g
  have hy13 : orderOf (g ^ 5) = 13 := by
    rw [orderOf_pow' _ (by norm_num), hg]
    norm_num
  have hz5 : orderOf (g ^ 13) = 5 := by
    rw [orderOf_pow' _ (by norm_num), hg]
    norm_num
  obtain ⟨c, hc⟩ := isConj_iff.1 (BThirteen.isConj_of_orderOf_thirteen hp2 P.order_x P.conj_g hy13)
  have hx' : xB13 = c⁻¹ * g ^ 5 * c := by rw [← hc]; group
  have hz'o : orderOf (c⁻¹ * g ^ 13 * c) = 5 := by
    rw [CFSG.Monster.Existence.StdOdd.Cert.orderOf_inv_mul_mul, hz5]
  have hz'c : (c⁻¹ * g ^ 13 * c) * xB13 = xB13 * (c⁻¹ * g ^ 13 * c) := by
    rw [hx']
    exact commute_conj_of_commute (Commute.pow_pow_self g 13 5).eq c
  have hw : ((t1B13 * t2B13) * xB13 = xB13 * (t1B13 * t2B13)) :=
    ((show Commute t1B13 xB13 from P.comm_t1).mul_left (show Commute t2B13 xB13 from P.comm_t2)).eq
  exact false_of_fixed_set BThirteen.cap13_baby P.order_x hz'o hz'c P.order_t1_t2 hw i1 P.comm_t1 hF

end BabyMonster

end CFSG.HardMathSupport.Dickson.Sec6.I1431
