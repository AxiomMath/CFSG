module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePCases
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreA0Basic

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}
  {N : Subgroup J}

@[expose] def a0Kernel (Q : Sylow 2 J) (B N : Subgroup J) : Subgroup J where
  carrier := {s | s ∈ (Q : Subgroup J) ∧ ∀ o ∈ N, o * s * o⁻¹ ∈ B}
  mul_mem' := fun {a b} ha hb => ⟨(Q : Subgroup J).mul_mem ha.1 hb.1, fun o ho => by
    have h1 := B.mul_mem (ha.2 o ho) (hb.2 o ho)
    rwa [show o * a * o⁻¹ * (o * b * o⁻¹) = o * (a * b) * o⁻¹ by group] at h1⟩
  one_mem' := ⟨(Q : Subgroup J).one_mem, fun o _ => by
    rw [mul_one, mul_inv_cancel]
    exact B.one_mem⟩
  inv_mem' := fun {a} ha => ⟨(Q : Subgroup J).inv_mem ha.1, fun o ho => by
    have h1 := B.inv_mem (ha.2 o ho)
    rwa [show (o * a * o⁻¹)⁻¹ = o * a⁻¹ * o⁻¹ by group] at h1⟩

omit [Finite J] in
theorem a0Kernel_le_sylow : a0Kernel Q B N ≤ (Q : Subgroup J) :=
  fun _ hs => hs.1

namespace A0Config

theorem conj_mem_a0Kernel (hc : A0Config Q B z u N) {q : J} (hq : q ∈ (Q : Subgroup J))
    {s : J} (hs : s ∈ a0Kernel Q B N) : q * s * q⁻¹ ∈ a0Kernel Q B N := by
  refine ⟨(Q : Subgroup J).mul_mem ((Q : Subgroup J).mul_mem hq hs.1)
    ((Q : Subgroup J).inv_mem hq), fun o ho => ?_⟩
  have ho' : q⁻¹ * o * q⁻¹⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp
    (hc.mem_normalizer ((Q : Subgroup J).inv_mem hq)) o).mp ho
  have hqB : q ∈ B := hc.setting.sylow_le hq
  have h1 := B.mul_mem (B.mul_mem hqB (hs.2 _ ho')) (B.inv_mem hqB)
  rwa [show q * (q⁻¹ * o * q⁻¹⁻¹ * s * (q⁻¹ * o * q⁻¹⁻¹)⁻¹) * q⁻¹ =
    o * (q * s * q⁻¹) * o⁻¹ by group] at h1

theorem le_normalizer_a0Kernel (hc : A0Config Q B z u N) :
    (Q : Subgroup J) ≤ Subgroup.normalizer (a0Kernel Q B N : Set J) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨hc.conj_mem_a0Kernel hq, fun hs => ?_⟩
  have h1 := hc.conj_mem_a0Kernel ((Q : Subgroup J).inv_mem hq) hs
  rwa [show q⁻¹ * (q * s * q⁻¹) * q⁻¹⁻¹ = s by group] at h1

theorem centralElt_mem_a0Kernel (hc : A0Config Q B z u N) : centralElt J ∈ a0Kernel Q B N :=
  ⟨hc.setting.centralElt_mem_sylow, fun o _ => by
    rw [Setting.conj_eq_of_mem_center hc.setting.centralElt_mem_center]
    exact hc.setting.centralElt_mem⟩

theorem self_mem_a0Kernel (hc : A0Config Q B z u N) : u ∈ a0Kernel Q B N :=
  ⟨hc.mem, fun o ho => by
    rw [hc.mul_comm_of_mem ho, mul_inv_cancel_right]
    exact hc.mem_core⟩

theorem eq_centralElt_of_mem_a0Kernel (hc : A0Config Q B z u N) {s : J}
    (hs : s ∈ a0Kernel Q B N) (hs2 : orderOf s = 2) : s = centralElt J := by
  obtain ⟨o, hoN, hoB⟩ := Set.not_subset.mp hc.not_le
  exact hc.setting.eq_centralElt_of_conj_mem hoB (hc.setting.sylow_le hs.1) (hs.2 o hoN) hs2

theorem mul_mem_a0Kernel_of_centralizer_le (hc : A0Config Q B z u N) {x : J}
    (hxQ : x ∈ (Q : Subgroup J)) (hxx : x * x ∈ Subgroup.center J)
    (hxZ : x ∉ Subgroup.center J) (hzxZ : z * x ∉ Subgroup.center J)
    (hC : ∀ o ∈ N, o * x = x * o → o ∈ B) : z * x ∈ a0Kernel Q B N := by
  have h := hc.setting
  have hz := hc.fourGen
  have hzB := hz.mem_of_setting h
  have hxB := h.sylow_le hxQ
  have hzC : ∀ o ∈ N, o * z = z * o → o ∈ B := fun o _ hoz => h.centralizer_le hzB hz.order
    hz.not_mem_center (Subgroup.mem_centralizer_singleton_iff.mpr hoz)
  refine ⟨(Q : Subgroup J).mul_mem hz.mem hxQ, fun o ho => ?_⟩
  obtain ⟨y, -, hyB, c, -, hcz, rfl⟩ := h.exists_mul_eq_of_centralizer_le hc.odd hzB hxB
    (hz.mul_self ▸ (Subgroup.center J).one_mem) hxx hz.not_mem_center hxZ
    (hz.comm_mem_center' hxQ) hzxZ (hc.mem_normalizer hz.mem) (hc.mem_normalizer hxQ) hzC hC ho
  have h1 : y * c * (z * x) * (y * c)⁻¹ = y * (z * x) * y⁻¹ := by
    calc y * c * (z * x) * (y * c)⁻¹ = y * (c * (z * x)) * c⁻¹ * y⁻¹ := by group
      _ = y * (z * x) * y⁻¹ := by rw [hcz]; group
  rw [h1]
  exact B.mul_mem (B.mul_mem hyB (B.mul_mem hzB hxB)) (B.inv_mem hyB)

theorem exists_mem_not_mem_commute_of_mul_not_mem (hc : A0Config Q B z u N) {x : J}
    (hxQ : x ∈ (Q : Subgroup J)) (hxx : x * x ∈ Subgroup.center J)
    (hxZ : x ∉ Subgroup.center J) (hzxZ : z * x ∉ Subgroup.center J)
    (hzx : z * x ∉ a0Kernel Q B N) : ∃ o ∈ N, o ∉ B ∧ o * x = x * o := by
  by_contra hcon
  push Not at hcon
  exact hzx (hc.mul_mem_a0Kernel_of_centralizer_le hxQ hxx hxZ hzxZ fun o ho hox => by
    by_contra hoB
    exact hcon o ho hoB hox)

theorem mul_mem_a0Kernel (hc : A0Config Q B z u N) {t : J} (htQ : t ∈ (Q : Subgroup J))
    (ht : t * t = 1) (htV : t ∉ fourGroup z) : z * t ∈ a0Kernel Q B N := by
  obtain ⟨htZ, htzZ, -⟩ := hc.not_mem_center_of_not_mem htQ ht htV
  have hztZ : z * t ∉ Subgroup.center J := fun h1 => htzZ (by
    have h2 := (Subgroup.center J).inv_mem h1
    rwa [mul_inv_rev, inv_eq_of_mul_eq_one_right hc.fourGen.mul_self,
      inv_eq_of_mul_eq_one_right ht] at h2)
  have ht1 : t ≠ 1 := fun h1 => htZ (h1 ▸ (Subgroup.center J).one_mem)
  exact hc.mul_mem_a0Kernel_of_centralizer_le htQ (ht ▸ (Subgroup.center J).one_mem) htZ hztZ
    fun o _ hot => hc.setting.centralizer_le (hc.setting.sylow_le htQ)
      (orderOf_eq_prime (by rw [pow_two]; exact ht) ht1) htZ
      (Subgroup.mem_centralizer_singleton_iff.mpr hot)

theorem mem_a0Kernel_or_mul_mem (hc : A0Config Q B z u N) {t : J}
    (htQ : t ∈ (Q : Subgroup J)) (ht : t * t = 1) :
    t ∈ a0Kernel Q B N ∨ z * t ∈ a0Kernel Q B N := by
  by_cases htV : t ∈ fourGroup z
  · rcases (hc.fourGen.mem_fourGroup_iff hc.setting).mp htV with h1 | h1 | h1 | h1 <;>
      rw [h1]
    · exact Or.inl (a0Kernel Q B N).one_mem
    · exact Or.inl hc.centralElt_mem_a0Kernel
    · rw [hc.fourGen.mul_self]
      exact Or.inr (a0Kernel Q B N).one_mem
    · refine Or.inr ?_
      rw [← mul_assoc, (hc.setting.commute_centralElt z).eq, mul_assoc, hc.fourGen.mul_self,
        mul_one]
      exact hc.centralElt_mem_a0Kernel
  · exact Or.inr (hc.mul_mem_a0Kernel htQ ht htV)

theorem mul_mul_self_of_not_mem (hc : A0Config Q B z u N) {t : J}
    (htQ : t ∈ (Q : Subgroup J)) (ht : t * t = 1) (htV : t ∉ fourGroup z) :
    z * t * (z * t) = centralElt J := by
  have htz : t * z = centralElt J * z * t := by
    rw [← hc.conj_eq_of_not_mem htQ ht htV, inv_mul_cancel_right]
  calc z * t * (z * t) = z * (t * z) * t := by group
    _ = z * (centralElt J * (z * t)) * t := by rw [htz]; group
    _ = centralElt J * (z * z) * (t * t) := by rw [hc.setting.mul_central_left]; group
    _ = centralElt J := by rw [hc.fourGen.mul_self, ht, mul_one, mul_one]

theorem conj_self_eq_of_mul (hc : A0Config Q B z u N) {t : J} (htQ : t ∈ (Q : Subgroup J))
    (ht : t * t = 1) (htV : t ∉ fourGroup z) :
    z * t * u * (z * t)⁻¹ = centralElt J * u := by
  have hzu : z * u * z⁻¹ = u := by rw [← hc.comm, mul_inv_cancel_right]
  rw [show z * t * u * (z * t)⁻¹ = z * (t * u * t⁻¹) * z⁻¹ by group,
    hc.conj_self_eq_of_not_mem htQ ht htV, hc.setting.mul_central_left, mul_assoc, hzu]

theorem a0Kernel_quaternion (hc : A0Config Q B z u N) :
    ∃ n, 3 ≤ n ∧ Nat.card (a0Kernel Q B N) = 2 ^ n ∧
      Nonempty (a0Kernel Q B N ≃* QuaternionGroup (2 ^ (n - 2))) := by
  have hK2 : IsPGroup 2 (a0Kernel Q B N) := Q.isPGroup'.to_le a0Kernel_le_sylow
  rcases CFSG.TwoRankLowerBound.Helpers.rank_one_two_group_cyclic_or_quaternion
      (a0Kernel Q B N) hK2 (twoRank_le_one_of_unique fun x hx hx2 =>
        hc.eq_centralElt_of_mem_a0Kernel hx hx2) with hcyc | ⟨n, hn, ⟨φ⟩⟩
  · exfalso
    obtain ⟨t, htQ, ht, htV⟩ := hc.fourGen.exists_involution_not_mem_fourGroup hc.setting
    let _ : CommGroup (a0Kernel Q B N) := IsCyclic.commGroup
    have hcomm := congrArg Subtype.val (mul_comm (⟨z * t, hc.mul_mem_a0Kernel htQ ht htV⟩ :
      a0Kernel Q B N) ⟨u, hc.self_mem_a0Kernel⟩)
    have h1 := hc.conj_self_eq_of_mul htQ ht htV
    change z * t * u = u * (z * t) at hcomm
    rw [hcomm, mul_inv_cancel_right] at h1
    exact hc.setting.centralElt_ne_one (mul_eq_right.mp h1.symm)
  · exact ⟨n, hn, by rw [Nat.card_congr φ.toEquiv, card_quaternionGroup_two_pow hn], ⟨φ⟩⟩

end A0Config

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
