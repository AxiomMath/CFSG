module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl2Basic
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec1Final

public section

namespace CFSG.OddStandard.ChengHeld.Excl2

open Subgroup CFSG.OddStandard.ChengHeldData
open CFSG.OddStandard.ChengHeld.ChartShape (cj_mul cj_inv cj_cj cj_of_commute cm_eq_one_iff)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

namespace Cfg

variable {d : Datum A} {α : ℕ} (K : Cfg d α)

include K

theorem pi_mul_self : K.c.pi * K.c.pi = 1 := by simpa [pow_two] using K.c.frame.pi2

theorem pi_not_mem_center : (⟨K.c.pi, d.S_le_A K.c.mem.1⟩ : ↥A) ∉ center ↥A := fun hz => by
  have hzC : K.c.pi ∈ centralizer (A : Set G) := mem_centralizer_iff.2 fun g hg =>
    congrArg Subtype.val (mem_center_iff.1 hz ⟨g, hg⟩)
  have h1 : K.c.pi ≠ 1 := fun h => K.c.shape_pi_not_mem_zpowers (h ▸ one_mem _)
  have h2 : orderOf K.c.pi = 2 := orderOf_eq_prime (by rw [pow_two]; exact K.pi_mul_self) h1
  apply K.c.shape_pi_not_mem_zpowers
  rw [d.eq_q_of_mem_centralizer K.h hzC h2, K.c.q_eq]
  exact pow_mem (mem_zpowers _) 2

theorem q_comm_S {s : G} (hs : s ∈ d.S) : s * d.q = d.q * s :=
  d.comm_Q_S K.q_mem_Q hs

theorem cj_pi_coset {s : G} (hs : s ∈ d.S) : ∃ w ∈ zpowers d.q, cj K.c.pi s = K.c.pi * w := by
  rw [← K.c.gen] at hs
  refine ChartShape.cj_coset_of_closure ?_ K.c.pi ?_ s hs
  · intro s' hs' z hz
    rw [K.c.gen] at hs'
    have hc : Commute d.q s' := (K.q_comm_S hs').symm
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hz
    rw [cj_of_commute (hc.zpow_left n)]
    exact hz
  · intro g hg
    have hpiq : K.c.pi * d.q = d.q * K.c.pi := (K.q_comm_S K.c.mem.1)
    rcases K.c.shape_cj_pi_gen hg with h | h
    · exact ⟨1, one_mem _, by rw [mul_one, h]⟩
    · exact ⟨d.q, mem_zpowers _, by rw [h, ← K.c.q_eq, ← hpiq]⟩

theorem mem_mul_center_of_comm_pi {a : G} (ha : a ∈ A)
    (hc : a * K.c.pi = K.c.pi * a) :
    ∃ s ∈ d.S, ∃ z ∈ A ⊓ centralizer (A : Set G), a = s * z := by
  obtain ⟨-, hcard⟩ := Sec1.invol_facts K.h
  set p : ↥A := ⟨K.c.pi, d.S_le_A K.c.mem.1⟩ with hp
  have hp2 : p * p = 1 := Subtype.ext K.pi_mul_self
  have hord : orderOf (QuotientGroup.mk p : ↥A ⧸ center ↥A) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← QuotientGroup.mk_mul, hp2, QuotientGroup.mk_one]
    · intro h1
      exact K.pi_not_mem_center ((QuotientGroup.eq_one_iff p).mp h1)
  have hcc := CFSG.Sporadic.HN.Local.card_conj_mul_card_centralizer
    (QuotientGroup.mk p : ↥A ⧸ center ↥A)
  rw [hcard _ hord, K.h.card_quotient] at hcc
  have hCp : IsPGroup 2 (centralizer {(QuotientGroup.mk p : ↥A ⧸ center ↥A)}) :=
    IsPGroup.of_card (n := 6) (by norm_num; omega)
  obtain ⟨P, hP⟩ := d.S_sylow.exists_sylow_eq_subgroupOf
  have hle : (P.mapSurjective (QuotientGroup.mk'_surjective (center ↥A)) :
      Subgroup (↥A ⧸ center ↥A)) ≤ centralizer {(QuotientGroup.mk p : ↥A ⧸ center ↥A)} := by
    rw [Sylow.coe_mapSurjective, hP]
    rintro _ ⟨s, hs, rfl⟩
    have hsS : (s : G) ∈ d.S := mem_subgroupOf.1 hs
    obtain ⟨w, hw, hcj⟩ := K.cj_pi_coset (d.S.inv_mem hsS)
    have hwA : w ∈ A := (zpowers_le.2 d.q_mem) hw
    have hwZ : (⟨w, hwA⟩ : ↥A) ∈ center ↥A := by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hw
      have e : (⟨w, hwA⟩ : ↥A) = (⟨d.q, d.q_mem⟩ : ↥A) ^ k := Subtype.ext (by simp [hk])
      rw [e]
      exact zpow_mem (Sec1.q_mem_center d) k
    have e : s * p = p * ⟨w, hwA⟩ * s := by
      apply Subtype.ext
      have h1 : (s : G) * K.c.pi * (s : G)⁻¹ = K.c.pi * w := by simpa [cj] using hcj
      simp only [Subgroup.coe_mul]
      calc (s : G) * K.c.pi = ((s : G) * K.c.pi * (s : G)⁻¹) * s := by group
        _ = K.c.pi * w * s := by rw [h1]
    rw [mem_centralizer_singleton_iff, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, e, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff _).2 hwZ, mul_one]
    exact (QuotientGroup.mk_mul (N := center ↥A) p s).symm
  have hap : (⟨a, ha⟩ : ↥A) * p = p * ⟨a, ha⟩ := Subtype.ext hc
  have haC : (QuotientGroup.mk (⟨a, ha⟩ : ↥A) : ↥A ⧸ center ↥A) ∈
      centralizer {(QuotientGroup.mk p : ↥A ⧸ center ↥A)} := by
    rw [mem_centralizer_singleton_iff, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hap]
  rw [(P.mapSurjective (QuotientGroup.mk'_surjective (center ↥A))).is_maximal' hCp hle,
    Sylow.coe_mapSurjective, hP] at haC
  obtain ⟨s, hs, hsa⟩ := Subgroup.mem_map.1 haC
  rw [QuotientGroup.mk'_apply] at hsa
  have hz : s⁻¹ * ⟨a, ha⟩ ∈ center ↥A := QuotientGroup.eq.1 hsa
  refine ⟨s, mem_subgroupOf.1 hs, ((s⁻¹ * ⟨a, ha⟩ : ↥A) : G),
    ⟨(s⁻¹ * ⟨a, ha⟩ : ↥A).2, mem_centralizer_iff.2 fun g hg =>
      congrArg Subtype.val (mem_center_iff.1 hz ⟨g, hg⟩)⟩, ?_⟩
  simp

theorem mem_X_of_mem_center {z : G} (hz : z ∈ A ⊓ centralizer (A : Set G)) {k : ℕ}
    (hzk : z ^ 2 ^ k = 1) : z ∈ d.X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZN : A ⊓ centralizer (A : Set G) ≤ normalizer (A : Set G) :=
    inf_le_left.trans le_normalizer
  have hNZ : normalizer (A : Set G) ≤
      normalizer ((A ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
    intro n hn
    have hnC : n ∈ normalizer ((centralizer (A : Set G) : Subgroup G) : Set G) := by
      rw [K.h.setting.standard.2.2.2.1]
      exact hn
    rw [mem_normalizer_iff_map_conj_eq] at hn hnC ⊢
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj n).injective, hn, hnC]
  have hsyl := d.X_sylow.inf_of_le_normalizer hZN hNZ
  have hp : IsPGroup 2 (zpowers z) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hzk)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨P, hP, hzP⟩ := exists_isSylowOf_of_le hp (zpowers_le.2 hz)
  obtain ⟨c, hcZ, hc⟩ := hsyl.exists_mem_conj hP
  have h1 := (hc z).1 (hzP (mem_zpowers z))
  have hcz : c⁻¹ * z * c = z := by
    have e : z * c = c * z := (mem_centralizer_iff.1 hz.2 c hcZ.1).symm
    calc c⁻¹ * z * c = c⁻¹ * (z * c) := by group
      _ = c⁻¹ * (c * z) := by rw [e]
      _ = z := by group
  rw [hcz] at h1
  exact h1.1

theorem conj_mem_W_of_mem_centralizer_V {c w : G}
    (hc : c ∈ centralizer (K.c.V : Set G)) (hw : w ∈ K.c.W) : c * w * c⁻¹ ∈ K.c.W := by
  have hqV : d.q ∈ K.c.V := subset_closure (by simp)
  have hpV : K.c.pi ∈ K.c.V := subset_closure (by simp)
  have hcN : c ∈ normalizer (A : Set G) := by
    rw [← d.centralizer_q K.h, mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.1 hc d.q hqV).symm
  have haA : c * w * c⁻¹ ∈ A := (mem_normalizer_iff.1 hcN w).1 (d.S_le_A hw.1)
  have haV : c * w * c⁻¹ ∈ centralizer (K.c.V : Set G) :=
    mul_mem (mul_mem hc hw.2) (inv_mem hc)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 d.X_sylow.isPGroup) ⟨w, d.S_le_X hw.1⟩
  have hwk : w ^ 2 ^ k = 1 := by
    rw [Subgroup.orderOf_mk] at hk
    rw [← hk]
    exact pow_orderOf_eq_one w
  have hak : (c * w * c⁻¹) ^ 2 ^ k = 1 := by rw [conj_pow, hwk]; group
  have hapi : c * w * c⁻¹ * K.c.pi = K.c.pi * (c * w * c⁻¹) :=
    (mem_centralizer_iff.1 haV K.c.pi hpV).symm
  obtain ⟨s, hs, z, hz, hasz⟩ := K.mem_mul_center_of_comm_pi haA hapi
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 d.X_sylow.isPGroup) ⟨s, d.S_le_X hs⟩
  have hsj : s ^ 2 ^ j = 1 := by
    rw [Subgroup.orderOf_mk] at hj
    rw [← hj]
    exact pow_orderOf_eq_one s
  have hsz : Commute s z := mem_centralizer_iff.1 hz.2 s (d.S_le_A hs)
  have hza : z = s⁻¹ * (c * w * c⁻¹) := by rw [hasz]; group
  have hsa : Commute s⁻¹ (c * w * c⁻¹) := by
    rw [hasz]
    exact (Commute.refl s).inv_left.mul_right hsz.inv_left
  have hzk : z ^ 2 ^ (j + k) = 1 := by
    rw [hza, hsa.mul_pow, inv_pow, pow_add, pow_mul, hsj, one_pow, inv_one, one_mul, pow_mul',
      hak, one_pow]
  have hzS : z ∈ d.S := ⟨K.mem_X_of_mem_center hz hzk, hz.1⟩
  exact ⟨by rw [hasz]; exact mul_mem hs hzS, haV⟩

end Cfg

end CFSG.OddStandard.ChengHeld.Excl2
