module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.LargeExtraspecialOut
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112T1Defs
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Basic
public import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner

public section

namespace CFSG.HardMathSupport.Dickson.I271.ThreeOutRank

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Dickson.I271.LargeExtraspecialOut

variable {G : Type*} [Group G]

theorem isElemAbelian_range {Q H : Type*} [Group Q] [Group H] (ψ : Q →* H) {p : ℕ}
    (hcomm : ∀ a b : Q, ψ (a⁻¹ * b⁻¹ * a * b) = 1) (hpow : ∀ a : Q, ψ (a ^ p) = 1) :
    IsElemAbelian p ψ.range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨_, ⟨x, rfl⟩⟩ := a
    obtain ⟨_, ⟨y, rfl⟩⟩ := b
    apply Subtype.ext
    have h := hcomm x y
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h
    show ψ x * ψ y = ψ y * ψ x
    calc ψ x * ψ y = ψ y * ψ x * ((ψ x)⁻¹ * (ψ y)⁻¹ * ψ x * ψ y) := by group
      _ = ψ y * ψ x := by rw [h, mul_one]
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    exact hpow x

theorem exists_isElemAbelian_card {H : Type*} [Group H] {p m : ℕ} [Fact p.Prime]
    {A : Subgroup H} [Finite A] (hA : IsElemAbelian p A) (hdvd : p ^ m ∣ Nat.card A) :
    ∃ D : Subgroup H, D ≤ A ∧ IsElemAbelian p D ∧ Nat.card D = p ^ m := by
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) p hdvd
  refine ⟨K.map A.subtype, Subgroup.map_subtype_le K, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
    obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
    apply Subtype.ext
    show (x : H) * (y : H) = (y : H) * (x : H)
    exact congrArg Subtype.val (hA.1.is_comm.comm x y)
  · rintro _ ⟨x, hx, rfl⟩
    exact hA.2 x.1 x.2
  · rw [Subgroup.card_map_of_injective A.subtype_injective, hK]

theorem pow_dvd_card_range {Q H : Type*} [Group Q] [Finite Q] [Group H] {p k : ℕ}
    (hQ : Nat.card Q = p ^ (k + 1)) (ψ : Q →* H) (hker : Nat.card ψ.ker ∣ p) :
    p ^ k ∣ Nat.card ψ.range := by
  have h1 : Nat.card Q = Nat.card ψ.ker * Nat.card ψ.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  obtain ⟨c, hc⟩ := hker
  have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have hr : Nat.card ψ.range = p ^ k * c := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc Nat.card ψ.ker * Nat.card ψ.range = p ^ (k + 1) := by rw [← h1, hQ]
      _ = p ^ k * p := by ring
      _ = p ^ k * (Nat.card ψ.ker * c) := by rw [← hc]
      _ = Nat.card ψ.ker * (p ^ k * c) := by ring
  rw [hr]
  exact dvd_mul_right _ _

theorem exists_elemAbelian_inner_trivial {p k m : ℕ} [Fact p.Prime] (hmk : m ≤ k) {w : G}
    (hw : orderOf w = p) {Q X J : Subgroup G} [Finite Q] (hQX : Q ≤ X) (hJX : J ≤ X)
    (hwX : ∀ x ∈ X, x * w = w * x) (hperf : commutator ↥J = ⊤)
    (hQN : Q ≤ Subgroup.normalizer (J : Set G)) (hQ : Nat.card Q = p ^ (k + 1))
    (hker : Q ⊓ (J ⊔ (X ⊓ Subgroup.centralizer (J : Set G))) ≤ Subgroup.zpowers w)
    (hcomm : ∀ a ∈ Q, ∀ b ∈ Q, a⁻¹ * b⁻¹ * a * b ∈ Subgroup.zpowers w)
    (hpow : ∀ a ∈ Q, a ^ p ∈ Subgroup.zpowers w) :
    ∃ D : Subgroup (MulAut (↥J ⧸ Subgroup.center ↥J)), IsElemAbelian p D ∧
      Nat.card D = p ^ m ∧ D ⊓ innerAut (↥J ⧸ Subgroup.center ↥J) = ⊥ := by
  let φ : Q →* MulAut (↥J ⧸ Subgroup.center ↥J) := (actQuot J).comp (Subgroup.inclusion hQN)
  have hwC : Subgroup.zpowers w ≤ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    exact hwX h (hJX hh)
  have hφw : ∀ q : Q, (q : G) ∈ Subgroup.zpowers w → φ q = 1 := by
    intro q hq
    show actQuot J ⟨(q : G), hQN q.2⟩ = 1
    rw [← MonoidHom.mem_ker, ker_actQuot hperf, Subgroup.mem_subgroupOf]
    exact hwC hq
  have hinner : ∀ q : Q, φ q ∈ inner (↥J ⧸ Subgroup.center ↥J) →
      (q : G) ∈ Subgroup.zpowers w := by
    intro q hq
    have hin : actQuot J ⟨(q : G), hQN q.2⟩ ∈ inner (↥J ⧸ Subgroup.center ↥J) := hq
    obtain ⟨k', hk', hc⟩ := exists_mem_of_actQuot_mem_inner hperf (hQN q.2) hin
    apply hker
    refine ⟨q.2, ?_⟩
    have hX : k'⁻¹ * (q : G) ∈ X ⊓ Subgroup.centralizer (J : Set G) :=
      ⟨X.mul_mem (X.inv_mem (hJX hk')) (hQX q.2), hc⟩
    have := Subgroup.mul_mem_sup hk' hX
    rwa [mul_inv_cancel_left] at this
  have hA : IsElemAbelian p φ.range :=
    isElemAbelian_range φ (fun a b => hφw _ (hcomm a a.2 b b.2)) (fun a => hφw _ (hpow a a.2))
  have hker_dvd : Nat.card φ.ker ∣ p := by
    have hle : φ.ker.map Q.subtype ≤ Subgroup.zpowers w := by
      rintro _ ⟨q, hq, rfl⟩
      have hq1 : φ q = 1 := hq
      exact hinner q (by rw [hq1]; exact Subgroup.one_mem _)
    rw [← Subgroup.card_map_of_injective Q.subtype_injective]
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, hw] at this
  have hAk : p ^ k ∣ Nat.card φ.range := pow_dvd_card_range hQ φ hker_dvd
  haveI : Finite φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨D, hDA, hD, hDc⟩ := exists_isElemAbelian_card hA ((pow_dvd_pow p hmk).trans hAk)
  refine ⟨D, hD, hDc, ?_⟩
  rw [eq_bot_iff]
  rintro x ⟨hxD, hxI⟩
  obtain ⟨q, rfl⟩ := hDA hxD
  exact Subgroup.mem_bot.2 (hφw q (hinner q hxI))

theorem no_elemAbelian_three_cube (hOut : SporadicOuterLeTwo) (hRank : LieOuterRank)
    {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K) (hK : CFSG.Open.IsKGroup K)
    {D : Subgroup (MulAut (K ⧸ Subgroup.center K))} (hD : IsElemAbelian 3 D)
    (hc : Nat.card D = 3 ^ 3) (hin : D ⊓ innerAut (K ⧸ Subgroup.center K) = ⊥) : False := by
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq
  haveI : Group.IsPerfect K := ⟨hq.1⟩
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have hinj : Function.Injective
      ((QuotientGroup.mk' (inner (K ⧸ Subgroup.center K))).comp D.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have hx' : (x : MulAut (K ⧸ Subgroup.center K)) ∈ D ⊓ innerAut (K ⧸ Subgroup.center K) :=
      ⟨x.2, hx⟩
    rw [hin, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.2 (Subtype.ext hx')
  have h27 : 27 ≤ Nat.card (Outer (K ⧸ Subgroup.center K)) := by
    have := Nat.card_le_card_of_injective _ hinj
    rw [hc] at this
    norm_num at this
    exact this
  rcases centralQuotient_family hq hK with ⟨n, ⟨e⟩⟩ | ⟨d, ⟨e⟩⟩ | ⟨s, ⟨e⟩⟩
  · have hn := CFSG.HardMathSupport.Timmesfeld.Tables.Alt.five_le_of_centerQuotient hq.1 e
    have h4 : Nat.card (Outer (K ⧸ Subgroup.center K)) ≤ 4 :=
      (Nat.card_congr (equivalence e).toEquiv).trans_le
        (CFSG.RankThree.PartOne.card_outer_alternating_le_four hn)
    omega
  · obtain ⟨x, hx, hx1⟩ := hRank (K ⧸ Subgroup.center K) hq.2 hnab d ⟨e⟩ 3 Nat.prime_three
      (by norm_num) D hD hc
    rw [hin, Subgroup.mem_bot] at hx
    exact hx1 hx
  · have h2 := hOut (K ⧸ Subgroup.center K) hq.2 hnab s ⟨e⟩
    omega

end CFSG.HardMathSupport.Dickson.I271.ThreeOutRank
