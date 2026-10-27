module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SquareCase
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.LinearSetup

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

theorem exists_conj_mem_sylow_of_pow {X : Type*} [Group X] [Finite X] (T : Sylow 2 X) {x : X}
    {n : ℕ} (hx : x ^ 2 ^ n = 1) : ∃ g : X, g * x * g⁻¹ ∈ (T : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx)
  have hP : IsPGroup 2 (Subgroup.zpowers x) := IsPGroup.of_card (n := k)
    (by rw [Nat.card_zpowers, hk])
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq X T Q
  refine ⟨g⁻¹, ?_⟩
  have h := hQ (Subgroup.mem_zpowers x)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h
  simpa [MulAut.smul_def, mul_assoc] using h

variable {G : Type} [Group G] [Finite G]

structure SzEightSetting (S : Sylow 2 G) (H : Subgroup G) (z : G)
    (J : Subgroup (EscapingQuotient z)) : Prop where
  square : SquareCaseSetting G S H z
  component : CFSG.IsComponent J
  not_le : ¬ J ≤ escapingImage H z
  involution : ∃ x ∈ J, orderOf x = 2 ∧ x ≠ escapingBar z
  center : ∀ c ∈ Subgroup.center J, (c : EscapingQuotient z) = 1 ∨
    (c : EscapingQuotient z) = escapingBar z
  outer : ∃ k ∈ escapingSylowImage S z, k ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) ∧
    k ≠ 1 ∧ k ≠ escapingBar z

namespace SzEightSetting

variable {S : Sylow 2 G} {H : Subgroup G} {z : G} {J : Subgroup (EscapingQuotient z)}
  (hs : SzEightSetting S H z J)
include hs

theorem central : IsCentralInvolution (S : Subgroup G) z := hs.square.central

theorem quotientData : EscapingQuotientData H z :=
  escapingQuotientData hs.square.core (hs.square.core.sylow_le hs.square.central.1)
    hs.square.central.2.1 hs.square.escape

theorem bar_mem : escapingBar z ∈ J := hs.square.caseTwo J hs.component

theorem two_le_pRank : 2 ≤ CFSG.Open.pRank 2 J := by
  obtain ⟨x, hxJ, hx, hne⟩ := hs.involution
  exact two_le_pRank_of_commuting_involutions hxJ hs.bar_mem hx hs.quotientData.bar_order hne
    (hs.quotientData.commute_bar x)

theorem normal : J.Normal :=
  hs.quotientData.component_normal_of_two_le_pRank hs.component hs.two_le_pRank

theorem eq_bar_of_mem_centralizer {k : EscapingQuotient z}
    (hk : k ∈ Subgroup.centralizer (J : Set (EscapingQuotient z))) (hk2 : orderOf k = 2) :
    k = escapingBar z :=
  hs.quotientData.eq_bar_of_mem_centralizer_of_two_le_pRank hs.component hs.two_le_pRank hk hk2

theorem mem_center_iff (c : J) :
    c ∈ Subgroup.center J ↔ (c : EscapingQuotient z) = 1 ∨ (c : EscapingQuotient z) = escapingBar z
    := by
  refine ⟨hs.center c, ?_⟩
  rintro (h | h)
  · rw [show c = 1 from Subtype.ext h]
    exact Subgroup.one_mem _
  · exact Subgroup.mem_center_iff.mpr fun g => Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, h]
      exact (hs.quotientData.commute_bar g).eq)

theorem mul_self_of_mem_center {c : J} (hc : c ∈ Subgroup.center J) : c * c = 1 := by
  apply Subtype.ext
  rcases hs.center c hc with h | h
  · rw [Subgroup.coe_mul, h, one_mul, Subgroup.coe_one]
  · rw [Subgroup.coe_mul, h, Subgroup.coe_one, ← pow_two]
    have h2 := pow_orderOf_eq_one (escapingBar z)
    rwa [hs.quotientData.bar_order] at h2

theorem card_center : Nat.card (Subgroup.center J) = 2 := by
  have hne : (1 : J) ≠ ⟨escapingBar z, hs.bar_mem⟩ := fun h => by
    have h1 : (1 : EscapingQuotient z) = escapingBar z := congrArg Subtype.val h
    have h2 := hs.quotientData.bar_order
    rw [← h1, orderOf_one] at h2
    exact absurd h2 (by decide)
  have hset : ((Subgroup.center J : Subgroup J) : Set J) = {1, ⟨escapingBar z, hs.bar_mem⟩} := by
    ext c
    simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [hs.mem_center_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_pair hne]

omit hs [Finite G] in
theorem mem_center_of_mem_centralizer {c : J}
    (hc : (c : EscapingQuotient z) ∈ Subgroup.centralizer (J : Set (EscapingQuotient z))) :
    c ∈ Subgroup.center J :=
  Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp hc g g.2)

theorem exists_root : ∃ k ∈ escapingSylowImage S z,
    k ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) ∧ k ^ 2 = escapingBar z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hkS, hkC, hk1, hkz⟩ := hs.outer
  have hP : IsPGroup 2 (escapingSylowImage S z) := by
    have h := (sylowBarSylow hs.central).isPGroup'
    rwa [coe_sylowBarSylow, sylowBar_range] at h
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hP ⟨k, hkS⟩
  rw [Subgroup.orderOf_mk] at hn
  obtain _ | _ | n := n
  · rw [pow_zero, orderOf_eq_one_iff] at hn
    exact absurd hn hk1
  · rw [zero_add, pow_one] at hn
    exact absurd (hs.eq_bar_of_mem_centralizer hkC hn) hkz
  refine ⟨k ^ 2 ^ n, (escapingSylowImage S z).pow_mem hkS _,
    (Subgroup.centralizer _).pow_mem hkC _, ?_⟩
  rw [← pow_mul, ← pow_succ]
  refine hs.eq_bar_of_mem_centralizer ((Subgroup.centralizer _).pow_mem hkC _) ?_
  rw [orderOf_pow_of_dvd (by positivity) (by rw [hn]; exact pow_dvd_pow 2 (by omega)), hn,
    pow_succ 2 (n + 1), Nat.mul_div_cancel_left _ (by positivity)]

theorem exists_involution_mem_sylow : ∃ x ∈ J, orderOf x = 2 ∧ x ≠ escapingBar z ∧
    x ∈ escapingSylowImage S z := by
  have := hs.normal
  obtain ⟨x, hxJ, hx, hne⟩ := hs.involution
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow_of_pow (sylowBarSylow hs.central) (n := 1)
    (x := x) (by rw [pow_one]; have h := pow_orderOf_eq_one x; rwa [hx] at h)
  rw [coe_sylowBarSylow, sylowBar_range] at hg
  refine ⟨g * x * g⁻¹, Subgroup.Normal.conj_mem inferInstance x hxJ g, ?_, fun h => hne ?_, hg⟩
  · simpa only [MulAut.conj_apply] using ((MulAut.conj g).orderOf_eq x).trans hx
  · rw [show x = g⁻¹ * (g * x * g⁻¹) * g by group, h, (hs.quotientData.commute_bar g⁻¹).eq,
      mul_assoc, inv_mul_cancel, mul_one]

end SzEightSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
