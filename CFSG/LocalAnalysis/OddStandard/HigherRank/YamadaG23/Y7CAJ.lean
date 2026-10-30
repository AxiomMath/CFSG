module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAD
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CACj
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ M : Type} [Group Γ] [Finite Γ] [Group M] [Finite M] {ρ : Γ →* MulAut M}
  {t : Γ} {J Q P M6 M7 : Subgroup Γ}

theorem y7c_J_card (c : K7Abs ρ t J Q P M6 M7) : Nat.card ↥J = 168 := by
  obtain ⟨e⟩ := c.J_iso
  rw [Nat.card_congr e.toEquiv, CFSG.ComponentClassification.GHarris.card_GL32_gh]

theorem y7c_J_simple (c : K7Abs ρ t J Q P M6 M7) : IsSimpleGroup ↥J := by
  obtain ⟨e⟩ := c.J_iso
  haveI := CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
  exact e.isSimpleGroup

theorem y7c_J_nonabelian (c : K7Abs ρ t J Q P M6 M7) :
    ∃ a ∈ J, ∃ b ∈ J, a * b ≠ b * a := by
  by_contra h
  push Not at h
  haveI hsimple := y7c_J_simple c
  haveI : IsMulCommutative ↥J :=
    IsMulCommutative.of_comm fun a b => Subtype.ext (h a.1 a.2 b.1 b.2)
  have hp : (Nat.card ↥J).Prime := Group.is_simple_iff_prime_card.mp hsimple
  rw [y7c_J_card c] at hp
  exact absurd hp (by norm_num)

theorem y7c_J_perfect (c : K7Abs ρ t J Q P M6 M7) : ⁅J, J⁆ = J := by
  haveI hsimple := y7c_J_simple c
  have hna : ¬ IsMulCommutative ↥J := by
    intro h
    obtain ⟨a, ha, b, hb, hab⟩ := y7c_J_nonabelian c
    exact hab (Subtype.ext_iff.mp (h.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  have htop : commutator ↥J = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (commutator ↥J) with hbot | htop
    · exact absurd ((commutator_eq_bot_iff (G := ↥J)).1 hbot) hna
    · exact htop
  refine le_antisymm (Subgroup.commutator_le_self J) ?_
  rw [← Subgroup.map_subtype_commutator J, htop, Subgroup.map_top, J.range_subtype]

theorem y7c_J_center (c : K7Abs ρ t J Q P M6 M7) {x : Γ} (hx : x ∈ J)
    (h : ∀ y ∈ J, x * y = y * x) : x = 1 := by
  haveI hsimple := y7c_J_simple c
  have hmem : (⟨x, hx⟩ : ↥J) ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (h y.1 y.2).symm
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center ↥J) with hbot | htop
  · rw [hbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext_iff.mp hmem
  · exfalso
    have hcomm : IsMulCommutative ↥J := Subgroup.center_eq_top_iff.mp htop
    obtain ⟨a, ha, b, hb, hab⟩ := y7c_J_nonabelian c
    exact hab (Subtype.ext_iff.mp (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))

theorem y7c_J_inf_normal (c : K7Abs ρ t J Q P M6 M7) (A : Subgroup Γ) [A.Normal] :
    J ⊓ A = ⊥ ∨ J ≤ A := by
  haveI hsimple := y7c_J_simple c
  rcases hsimple.eq_bot_or_eq_top_of_normal (A.subgroupOf J) with hbot | htop
  · left
    rw [Subgroup.subgroupOf_eq_bot, disjoint_iff] at hbot
    simpa only [inf_comm] using hbot
  · right
    rwa [Subgroup.subgroupOf_eq_top] at htop

theorem y7c_Q_comm (c : K7Abs ρ t J Q P M6 M7) {a b : Γ} (ha : a ∈ Q) (hb : b ∈ Q) :
    a * b = b * a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp c.Q_two
  have hbound : n ≤ 2 := by
    have hle : 2 ^ n ≤ 2 ^ 2 := by
      have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [← h4, ← hn]
      exact c.Q_card
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  have hcomm : IsMulCommutative ↥Q := by
    have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hn_cases with rfl | rfl | rfl
    · have h1 : Nat.card ↥Q = 1 := by rw [hn]; norm_num
      haveI : Subsingleton ↥Q := Finite.card_le_one_iff_subsingleton.mp h1.le
      exact IsMulCommutative.of_comm fun x y => Subsingleton.elim (x * y) (y * x)
    · haveI : IsCyclic ↥Q := isCyclic_of_prime_card (p := 2) (by simpa using hn)
      exact IsCyclic.isMulCommutative
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hn
  simpa using Subtype.ext_iff.mp (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem y7c_comm_mem_J (c : K7Abs ρ t J Q P M6 M7) {x y : Γ} (hx : x * t = t * x)
    (hy : y * t = t * y) : ⁅x, y⁆ ∈ J := by
  obtain ⟨j₁, hj₁, q₁, hq₁, rfl⟩ := c.cent x hx
  obtain ⟨j₂, hj₂, q₂, hq₂, rfl⟩ := c.cent y hy
  have hq1j2 : ⁅q₁, j₂⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (c.Q_J q₁ hq₁ j₂ hj₂)
  have hq1q2 : ⁅q₁, q₂⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (y7c_Q_comm c hq₁ hq₂)
  have hj1q2 : ⁅j₁, q₂⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (c.Q_J q₂ hq₂ j₁ hj₁).symm
  rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_mul_right_eq_mul_conj,
    commutatorElement_mul_right_eq_mul_conj, hq1j2, hq1q2, hj1q2]
  simp only [mul_assoc, mul_one, one_mul, mul_inv_cancel, inv_mul_cancel]
  exact Subgroup.commutator_le_self J (Subgroup.commutator_mem_commutator hj₁ hj₂)

theorem y7c_perfect_le_J (c : K7Abs ρ t J Q P M6 M7) {X : Subgroup Γ} (hX : ⁅X, X⁆ = X)
    (hXt : ∀ x ∈ X, x * t = t * x) : X ≤ J := by
  rw [← hX]
  exact Subgroup.commutator_le.mpr fun a ha b hb =>
    y7c_comm_mem_J c (hXt a ha) (hXt b hb)

theorem y7c_conjSub_J_le (c : K7Abs ρ t J Q P M6 M7) (n : Γ)
    (h : ∀ j ∈ J, (n * j * n⁻¹) * t = t * (n * j * n⁻¹)) : conjSub n J ≤ J := by
  refine y7c_perfect_le_J c ?_ ?_
  · unfold conjSub
    rw [← Subgroup.map_commutator (f := (MulAut.conj n).toMonoidHom), y7c_J_perfect c]
  · intro x hx
    have hx' : n⁻¹ * x * n ∈ J :=
      (y7c_mem_conjSub (g := n) (x := x) (Y := J)).mp hx
    simpa [mul_assoc] using h (n⁻¹ * x * n) hx'

theorem y7c_J_exists_order7 (c : K7Abs ρ t J Q P M6 M7) : ∃ x ∈ J, x ^ 7 = 1 ∧ x ≠ 1 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h7 : 7 ∣ Nat.card ↥J := by rw [y7c_J_card c]; norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) 7 h7
  refine ⟨x.1, x.2, ?_, ?_⟩
  · have hpow : x ^ 7 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    simpa [Subgroup.coe_pow] using congrArg Subtype.val hpow
  · intro h1
    have hx1 : x = 1 := Subtype.ext h1
    rw [hx1, orderOf_one] at hx
    exact absurd hx (by norm_num)

end CFSG.OddStandard.HigherRank.YamadaG23
