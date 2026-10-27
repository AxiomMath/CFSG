module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Bg.Local.Transfer1515
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RS
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74.L38

open Matrix Subgroup
open CFSG.GH74.GLS.Bg.Thompson (IsSylowIn)
open scoped MatrixGroups

theorem mul_eq_inv_mul_of_mul_self {G : Type*} [Group G] {c d m : G} (hc : c * c = m)
    (hd : d * d = m) (hmc : m * c = c * m) (hm : m * m = 1) : d * c = (c * d)⁻¹ := by
  have hci : c⁻¹ = c * m :=
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hc, hm])
  have hdi : d⁻¹ = d * m :=
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hd, hm])
  rw [_root_.mul_inv_rev, hci, hdi]
  calc d * c = d * c * (m * m) := by rw [hm, mul_one]
    _ = d * (m * c) * m := by rw [hmc]; group
    _ = d * m * (c * m) := by group

variable {K : Type} [Field K] [Finite K]

theorem sl2_eq_one_or_eq_neg_one (hodd : Odd (Nat.card K)) {g : SL(2, K)} (hg : g * g = 1) :
    g = 1 ∨ g = -1 :=
  Semidihedral.OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self K
    (Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd) g (inv_eq_of_mul_eq_one_right hg)

theorem exists_mul_self_conj_eq_or_inv (hodd : Odd (Nat.card K)) {G : Type*} [Group G]
    (ρ : SL(2, K) →* G) (hρ : Function.Injective ρ) {Q : Subgroup G}
    (hQ : IsSylowIn 2 Q ρ.range) {x : G} (hxx : x * x = 1)
    (hxQ : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) (hxz : x * ρ (-1) * x⁻¹ = ρ (-1)) :
    ∃ u ∈ Q, u * u = ρ (-1) ∧ (x * u * x⁻¹ = u ∨ x * u * x⁻¹ = u⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : K) ≠ 0 := Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have hp : IsPGroup 2 (Q.comap ρ) := hQ.2.1.comap_of_injective ρ hρ
  have hi : ¬ 2 ∣ (Q.comap ρ).index := by rw [index_comap]; exact hQ.2.2
  set P : Sylow 2 SL(2, K) := hp.toSylow hi with hP
  have hPQ : ∀ y, y ∈ (P : Subgroup SL(2, K)) ↔ ρ y ∈ Q := fun y => Iff.rfl
  obtain ⟨n, hn3, ⟨e⟩⟩ := Semidihedral.OddFieldSL2.sylow_two_quaternion K hodd P
  set N := 2 ^ (n - 2) with hNdef
  have hk : N = 2 ^ (n - 3) + 2 ^ (n - 3) := by
    rw [hNdef, show n - 2 = n - 3 + 1 by omega, pow_succ, mul_two]
  set k := 2 ^ (n - 3) with hkdef
  have hk1 : 1 ≤ k := Nat.one_le_two_pow
  have hN2 : 2 ≤ N := by omega
  have hw : ((e.symm (QuaternionGroup.a N) : P) : SL(2, K)) = -1 := by
    set w := e.symm (QuaternionGroup.xa 0) with hwdef
    have hww : e.symm (QuaternionGroup.a N) = w * w := by
      rw [hwdef, ← map_mul, quaternion_xa_mul_self]
    rw [hww]
    have hne : (w * w : (P : Subgroup SL(2, K))) ≠ 1 := by
      intro h
      have := congrArg e h
      rw [map_mul, hwdef, MulEquiv.apply_symm_apply, quaternion_xa_mul_self, map_one] at this
      have hN' : (N : ZMod (2 * N)) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd
        have := Nat.le_of_dvd (by omega) hd
        omega
      exact hN' (QuaternionGroup.a.inj (this.trans QuaternionGroup.one_def))
    have hsq : (w * w : (P : Subgroup SL(2, K))) ^ 2 = 1 := by
      apply e.injective
      rw [map_pow, map_mul, hwdef, MulEquiv.apply_symm_apply, quaternion_xa_mul_self, map_one,
        pow_two, QuaternionGroup.a_mul_a, ← QuaternionGroup.a_zero]
      congr 1
      rw [← two_mul]
      exact_mod_cast ZMod.natCast_self (2 * N)
    have hord : orderOf ((w * w : (P : Subgroup SL(2, K))) : SL(2, K)) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime hsq hne
    exact (Semidihedral.OddFieldSL2.orderOf_eq_two_iff K h2 _).mp hord
  set c₀ : P := e.symm (QuaternionGroup.a (k : ZMod (2 * N))) with hc₀
  have hkk : ((k : ZMod (2 * N)) + k) = N := by
    have h := congrArg (fun m : ℕ => (m : ZMod (2 * N))) hk.symm
    push_cast at h
    exact h
  have hcc : ((c₀ * c₀ : P) : SL(2, K)) = -1 := by
    rw [hc₀, ← map_mul, QuaternionGroup.a_mul_a, hkk]
    exact hw
  set c := ρ c₀ with hc
  have hcQ : c ∈ Q := (hPQ c₀).mp c₀.2
  have hcc' : c * c = ρ (-1) := by rw [hc, ← map_mul, ← Subgroup.coe_mul, hcc]
  have hm : ρ (-1) * ρ (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have hmc : ρ (-1) * c = c * ρ (-1) := by rw [hc, ← map_mul, ← map_mul, neg_one_mul, mul_neg_one]
  have hdQ : x * c * x⁻¹ ∈ Q := hxQ c hcQ
  obtain ⟨d₀, hd₀⟩ := hQ.1 hdQ
  have hd₀P : d₀ ∈ (P : Subgroup SL(2, K)) := by rw [hPQ, hd₀]; exact hdQ
  have hdd : d₀ * d₀ = -1 := by
    apply hρ
    rw [map_mul, hd₀, show x * c * x⁻¹ * (x * c * x⁻¹) = x * (c * c) * x⁻¹ by group, hcc', hxz]
  have hdd' : x * c * x⁻¹ * (x * c * x⁻¹) = ρ (-1) := by rw [← hd₀, ← map_mul, hdd]
  set d₁ : P := ⟨d₀, hd₀P⟩ with hd₁
  rcases hed : e d₁ with i | j
  ·
    have hcomm : Commute (c₀ : SL(2, K)) d₀ := by
      have h : c₀ * d₁ = d₁ * c₀ := by
        apply e.injective
        rw [map_mul, map_mul, hed, hc₀, MulEquiv.apply_symm_apply, QuaternionGroup.a_mul_a,
          QuaternionGroup.a_mul_a, add_comm]
      exact congrArg Subtype.val h
    have hc0 : (c₀ : SL(2, K)) * c₀ = -1 := by rw [← Subgroup.coe_mul, hcc]
    have hsq1 : ((c₀ : SL(2, K))⁻¹ * d₀) * ((c₀ : SL(2, K))⁻¹ * d₀) = 1 := by
      rw [hcomm.symm.inv_right.mul_mul_mul_comm, ← _root_.mul_inv_rev, hc0, hdd]
      exact inv_mul_cancel _
    rcases sl2_eq_one_or_eq_neg_one hodd hsq1 with h | h
    · refine ⟨c, hcQ, hcc', Or.inl ?_⟩
      rw [← hd₀, show d₀ = c₀ from (inv_mul_eq_one.mp h).symm]
    · refine ⟨c, hcQ, hcc', Or.inr ?_⟩
      have hd : d₀ = (c₀ : SL(2, K))⁻¹ := by
        refine eq_inv_of_mul_eq_one_left ?_
        have h' : d₀ = (c₀ : SL(2, K)) * -1 := by rw [← h, mul_inv_cancel_left]
        rw [h', mul_neg_one, neg_mul, hc0, neg_neg]
      rw [← hd₀, hd, map_inv]
  ·
    refine ⟨c * (x * c * x⁻¹), mul_mem hcQ hdQ, ?_, Or.inr ?_⟩
    · have h : c₀ * d₁ * (c₀ * d₁) = e.symm (QuaternionGroup.a N) := by
        apply e.injective
        rw [MulEquiv.apply_symm_apply, map_mul, map_mul, hed, hc₀, MulEquiv.apply_symm_apply,
          QuaternionGroup.a_mul_xa, quaternion_xa_mul_self]
      have h' : (c₀ : SL(2, K)) * d₀ * ((c₀ : SL(2, K)) * d₀) = -1 := by
        rw [← hw, ← h]
        rfl
      rw [← hd₀, hc, ← map_mul, ← map_mul, h']
    · have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
      have hxc : x * x * c * x⁻¹ * x⁻¹ = c := by rw [hxx, one_mul, hxi, mul_assoc, hxx, mul_one]
      calc x * (c * (x * c * x⁻¹)) * x⁻¹ = x * c * x⁻¹ * (x * x * c * x⁻¹ * x⁻¹) := by group
        _ = x * c * x⁻¹ * c := by rw [hxc]
        _ = (c * (x * c * x⁻¹))⁻¹ := mul_eq_inv_mul_of_mul_self hcc' hdd' hmc hm

end CFSG.ComponentClassification.HarrisLit.T1.S74.L38
