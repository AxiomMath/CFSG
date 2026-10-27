module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePB1Char
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePCases

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open QuaternionGroup

theorem quaternionGroup_anticomm_pair (k : ℕ) :
    a (k : ZMod (2 * (2 * k))) * a k = a ((2 * k : ℕ) : ZMod (2 * (2 * k))) ∧
    xa (0 : ZMod (2 * (2 * k))) * xa 0 = a ((2 * k : ℕ) : ZMod (2 * (2 * k))) ∧
    a (k : ZMod (2 * (2 * k))) * xa 0 =
      xa 0 * a k * a ((2 * k : ℕ) : ZMod (2 * (2 * k))) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [a_mul_a]
    congr 1
    push_cast
    ring
  · rw [xa_mul_xa]
    congr 1
    ring
  · rw [a_mul_xa, xa_mul_a, xa_mul_a]
    congr 1
    have h : ((2 * (2 * k) : ℕ) : ZMod (2 * (2 * k))) = 0 := ZMod.natCast_self _
    push_cast at h ⊢
    rw [zero_sub, zero_add, neg_eq_iff_add_eq_zero, ← h]
    ring

namespace PartC

variable {G : Type} [Group G] {T Q P₁ : Subgroup G} {e u : G}

theorem eq_or_eq_mul_of_mul_eq (hc : PartC T Q P₁ e u) {q q' p p' : G} (hq : q ∈ Q)
    (hq' : q' ∈ Q) (hp : p ∈ P₁) (hp' : p' ∈ P₁) (h : q * p = q' * p') :
    q' = q ∨ q' = q * e := by
  have hP : q⁻¹ * q' ∈ P₁ := by
    rw [show q⁻¹ * q' = p * p'⁻¹ by rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← h]; group]
    exact P₁.mul_mem hp (P₁.inv_mem hp')
  rcases hc.mem_inf _ (Q.mul_mem (Q.inv_mem hq) hq') hP with h1 | h1
  · left
    rw [inv_mul_eq_one] at h1
    exact h1.symm
  · right
    rw [inv_mul_eq_iff_eq_mul] at h1
    exact h1

theorem ne_of_mul_self_eq (hc : PartC T Q P₁ e u) {q : G} (hqq : q * q = e) :
    q ≠ 1 ∧ q ≠ e := by
  refine ⟨fun h => hc.centralElt_ne_one ?_, fun h => hc.centralElt_ne_one ?_⟩
  · rw [h, mul_one] at hqq
    exact hqq.symm
  · rw [h] at hqq
    exact mul_eq_left.mp hqq

theorem orderOf_mul_eq_two (hc : PartC T Q P₁ e u) {q p : G} (hq : q ∈ Q) (hp : p ∈ P₁)
    (hqq : q * q = e) (hpp : p * p = e) : orderOf (q * p) = 2 := by
  have hsq : q * p * (q * p) = 1 := by
    rw [show q * p * (q * p) = q * (p * q) * p by group, ← hc.commute q hq p hp,
      show q * (q * p) * p = (q * q) * (p * p) by group, hqq, hpp, hc.centralElt_mul_self]
  refine orderOf_eq_prime (by rw [pow_two]; exact hsq) fun h1 => ?_
  rcases hc.eq_or_eq_mul_of_mul_eq Q.one_mem hq P₁.one_mem hp (by rw [mul_one, h1]) with h | h
  · exact (hc.ne_of_mul_self_eq hqq).1 h
  · exact (hc.ne_of_mul_self_eq hqq).2 (by rw [h, one_mul])

theorem mul_ne_centralElt (hc : PartC T Q P₁ e u) {q p : G} (hq : q ∈ Q) (hp : p ∈ P₁)
    (hqq : q * q = e) : q * p ≠ e := by
  intro h
  rcases hc.eq_or_eq_mul_of_mul_eq hc.mem_left hq P₁.one_mem hp (by rw [mul_one, h]) with h' | h'
  · exact (hc.ne_of_mul_self_eq hqq).2 h'
  · exact (hc.ne_of_mul_self_eq hqq).1 (by rw [h', hc.centralElt_mul_self])

theorem three_le_pRank_of_anticomm [Finite G] (hc : PartC T Q P₁ e u) {a b : G} (ha : a ∈ P₁)
    (hb : b ∈ P₁) (haa : a * a = e) (hbb : b * b = e) (hab : a * b = b * a * e) :
    3 ≤ CFSG.Open.pRank 2 T := by
  obtain ⟨q₁, hq₁, q₂, hq₂, h11, h22, h21, h21e⟩ :=
    quaternion_exists_pair hc.quaternion.some hc.mem_left hc.order
  have hanti := hc.anticomm hq₁ hq₂ h11 h22 h21 h21e
  have hst : Commute (q₁ * a) (q₂ * b) := by
    change q₁ * a * (q₂ * b) = q₂ * b * (q₁ * a)
    calc q₁ * a * (q₂ * b) = q₁ * (a * q₂) * b := by group
      _ = q₁ * (q₂ * a) * b := by rw [hc.commute q₂ hq₂ a ha]
      _ = (q₁ * q₂) * (a * b) := by group
      _ = (q₂ * q₁ * e) * (b * a * e) := by rw [hanti, hab]
      _ = q₂ * q₁ * (e * (b * a)) * e := by group
      _ = q₂ * q₁ * ((b * a) * e) * e := by rw [← hc.commute_centralElt (b * a)]
      _ = q₂ * q₁ * b * a * (e * e) := by group
      _ = q₂ * (q₁ * b) * a := by rw [hc.centralElt_mul_self]; group
      _ = q₂ * (b * q₁) * a := by rw [hc.commute q₁ hq₁ b hb]
      _ = q₂ * b * (q₁ * a) := by group
  refine CFSG.ProperTwoGeneratedCore.Assembly.three_le_pRank_of_commuting_involutions
    (hc.left_le hc.mem_left) (T.mul_mem (hc.left_le hq₁) (hc.right_le ha))
    (T.mul_mem (hc.left_le hq₂) (hc.right_le hb)) hc.order
    (hc.orderOf_mul_eq_two hq₁ ha h11 haa) (hc.orderOf_mul_eq_two hq₂ hb h22 hbb)
    (hc.commute_centralElt _).symm (hc.commute_centralElt _).symm hst
    (hc.mul_ne_centralElt hq₁ ha h11).symm (hc.mul_ne_centralElt hq₂ hb h22) (fun h => ?_)
    (fun h => ?_)
  · rcases hc.eq_or_eq_mul_of_mul_eq hq₁ hq₂ ha hb h.symm with h' | h'
    · exact h21 h'
    · exact h21e h'
  · have h' : q₁ * e * a = q₂ * b := by
      rw [h, mul_assoc, ← hc.commute_centralElt a, ← mul_assoc, hc.commute_centralElt]
    rcases hc.eq_or_eq_mul_of_mul_eq (Q.mul_mem hq₁ hc.mem_left) hq₂ ha hb h' with h'' | h''
    · exact h21e h''
    · exact h21 (by rw [h'', hc.mul_centralElt_mul_centralElt])

theorem isCyclic_right_of_pRank_le_two [Finite G] (hc : PartC T Q P₁ e u)
    (hrank : CFSG.Open.pRank 2 T ≤ 2) : IsCyclic P₁ := by
  rcases hc.right_cyclic_or_quaternion with h | ⟨n, hn, ⟨φ⟩⟩
  · exact h
  exfalso
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ (n - 2) = 2 * k :=
    ⟨2 ^ (n - 3), by rw [← pow_succ']; congr 1; omega⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    have := Nat.two_pow_pos (n - 2)
    omega
  generalize 2 ^ (n - 2) = M at φ hk
  subst hk
  have : NeZero (2 * k) := ⟨by omega⟩
  obtain ⟨h1, h2, h3⟩ := quaternionGroup_anticomm_pair k
  have hE : φ.symm (a ((2 * k : ℕ) : ZMod (2 * (2 * k)))) = ⟨e, hc.mem_right⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact (hc.map_centralElt_right φ).symm
  have hxx : ((φ.symm (a k) : P₁) : G) * (φ.symm (a k) : P₁) = e := by
    rw [← Subgroup.coe_mul, ← map_mul, h1, hE]
  have hyy : ((φ.symm (xa 0) : P₁) : G) * (φ.symm (xa 0) : P₁) = e := by
    rw [← Subgroup.coe_mul, ← map_mul, h2, hE]
  have hxy : ((φ.symm (a k) : P₁) : G) * (φ.symm (xa 0) : P₁) =
      (φ.symm (xa 0) : P₁) * (φ.symm (a k) : P₁) * e := by
    have h := congrArg (fun w => ((φ.symm w : P₁) : G)) h3
    simp only [map_mul, hE, Subgroup.coe_mul] at h
    exact h
  have := hc.three_le_pRank_of_anticomm (φ.symm (a k)).2 (φ.symm (xa 0)).2 hxx hyy hxy
  omega

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
