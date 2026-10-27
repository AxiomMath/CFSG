module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K5Cent

public section

namespace CFSG.OddStandard.SmallF3.Omega.K5

namespace SL23Pair

variable {K : Type} [Group K] [Finite K] {A B : Subgroup K} (h : SL23Pair K A B)

theorem eq_of_comm {p q : Fin 4 ⊕ Fin 4} (hpq : p.isLeft = q.isLeft)
    (hc : h.gen p * h.gen q = h.gen q * h.gen p) : p = q := by
  rcases p with i | i <;> rcases q with j | j
  · have h1 : (h.eA.symm (k5g i)) * (h.eA.symm (k5g j)) =
        (h.eA.symm (k5g j)) * (h.eA.symm (k5g i)) := Subtype.ext hc
    have h2 : k5g i * k5g j = k5g j * k5g i := by simpa using congrArg h.eA h1
    exact congrArg Sum.inl (comm_k5g h2)
  · simp at hpq
  · simp at hpq
  · have h1 : (h.eB.symm (k5g i)) * (h.eB.symm (k5g j)) =
        (h.eB.symm (k5g j)) * (h.eB.symm (k5g i)) := Subtype.ext hc
    have h2 : k5g i * k5g j = k5g j * k5g i := by simpa using congrArg h.eB h1
    exact congrArg Sum.inr (comm_k5g h2)

theorem comm_of_blocks {p q : Fin 4 ⊕ Fin 4} (hpq : p.isLeft ≠ q.isLeft) :
    h.gen p * h.gen q = h.gen q * h.gen p := by
  rcases p with i | i <;> rcases q with j | j
  · exact absurd rfl hpq
  · exact h.comm _ (h.gen_mem_A i) _ (h.gen_mem_B j)
  · exact (h.comm _ (h.gen_mem_A j) _ (h.gen_mem_B i)).symm
  · exact absurd rfl hpq

theorem isLeft_eq_false_of_mem_B {q : Fin 4 ⊕ Fin 4} {x : K} (hx : x ∈ B)
    (hq : x = h.gen q ∨ x = (h.gen q)⁻¹) : q.isLeft = false := by
  have hgB : h.gen q ∈ B := by
    rcases hq with e | e
    · rw [← e]; exact hx
    · have : h.gen q = x⁻¹ := by rw [e, inv_inv]
      rw [this]; exact inv_mem hx
  rcases q with j | j
  · exact absurd (h.eq_one_of_mem_inf ⟨h.gen_mem_A j, hgB⟩ (h.gen_pow_three _))
      (h.gen_ne_one _)
  · rfl

theorem mem_A_of_isLeft {q : Fin 4 ⊕ Fin 4} {x : K} (hq : q.isLeft = true)
    (hx : x = h.gen q ∨ x = (h.gen q)⁻¹) : x ∈ A := by
  rcases q with j | j
  · rcases hx with e | e
    · rw [e]; exact h.gen_mem_A j
    · rw [e]; exact inv_mem (h.gen_mem_A j)
  · simp at hq

noncomputable def thetaFun (α : MulAut K) (p : Fin 4 ⊕ Fin 4) : Fin 4 ⊕ Fin 4 :=
  Classical.choose (h.exists_image α p)

theorem thetaFun_spec (α : MulAut K) (p : Fin 4 ⊕ Fin 4) :
    α (h.gen p) = h.gen (h.thetaFun α p) ∨ α (h.gen p) = (h.gen (h.thetaFun α p))⁻¹ :=
  Classical.choose_spec (h.exists_image α p)

theorem thetaFun_eq {α : MulAut K} {p q : Fin 4 ⊕ Fin 4}
    (hq : α (h.gen p) = h.gen q ∨ α (h.gen p) = (h.gen q)⁻¹) : q = h.thetaFun α p := by
  rcases h.thetaFun_spec α p with h1 | h1 <;> rcases hq with h2 | h2
  · exact h.gen_eq_of (Or.inl (h2.symm.trans h1))
  · exact (h.gen_eq_of (Or.inr (h1.symm.trans h2))).symm
  · exact h.gen_eq_of (Or.inr (h2.symm.trans h1))
  · exact h.gen_eq_of (Or.inl (inv_injective (h2.symm.trans h1)))

theorem thetaFun_one (p : Fin 4 ⊕ Fin 4) : h.thetaFun 1 p = p :=
  (h.thetaFun_eq (p := p) (q := p) (Or.inl rfl)).symm

theorem thetaFun_mul (α β : MulAut K) (p : Fin 4 ⊕ Fin 4) :
    h.thetaFun (α * β) p = h.thetaFun α (h.thetaFun β p) := by
  refine (h.thetaFun_eq ?_).symm
  have e : (α * β) (h.gen p) = α (β (h.gen p)) := rfl
  rw [e]
  rcases h.thetaFun_spec β p with h1 | h1
  · rw [h1]
    exact h.thetaFun_spec α _
  · rw [h1, map_inv]
    rcases h.thetaFun_spec α (h.thetaFun β p) with h2 | h2
    · right
      rw [h2]
    · left
      rw [h2, inv_inv]

noncomputable def theta : MulAut K →* Equiv.Perm (Fin 4 ⊕ Fin 4) where
  toFun α :=
    { toFun := h.thetaFun α
      invFun := h.thetaFun α⁻¹
      left_inv := fun p => by rw [← h.thetaFun_mul, inv_mul_cancel, h.thetaFun_one]
      right_inv := fun p => by rw [← h.thetaFun_mul, mul_inv_cancel, h.thetaFun_one] }
  map_one' := Equiv.ext fun p => h.thetaFun_one p
  map_mul' α β := Equiv.ext fun p => h.thetaFun_mul α β p

theorem theta_spec (α : MulAut K) (p : Fin 4 ⊕ Fin 4) :
    α (h.gen p) = h.gen (h.theta α p) ∨ α (h.gen p) = (h.gen (h.theta α p))⁻¹ :=
  h.thetaFun_spec α p

theorem theta_eq {α : MulAut K} {p q : Fin 4 ⊕ Fin 4}
    (hq : α (h.gen p) = h.gen q ∨ α (h.gen p) = (h.gen q)⁻¹) : h.theta α p = q :=
  (h.thetaFun_eq hq).symm

theorem comm_of_theta_comm (α : MulAut K) {p q : Fin 4 ⊕ Fin 4}
    (hc : h.gen (h.theta α p) * h.gen (h.theta α q) =
      h.gen (h.theta α q) * h.gen (h.theta α p)) :
    h.gen p * h.gen q = h.gen q * h.gen p := by
  have hcom : Commute (h.gen (h.theta α p)) (h.gen (h.theta α q)) := hc
  have hα : α (h.gen p * h.gen q) = α (h.gen q * h.gen p) := by
    rw [map_mul, map_mul]
    show Commute (α (h.gen p)) (α (h.gen q))
    rcases h.theta_spec α p with h1 | h1 <;> rcases h.theta_spec α q with h2 | h2 <;>
      rw [h1, h2]
    · exact hcom
    · exact hcom.inv_right
    · exact hcom.inv_left
    · exact hcom.inv_inv
  exact α.injective hα

theorem theta_block (α : MulAut K) {p q : Fin 4 ⊕ Fin 4} (hpq : p.isLeft = q.isLeft) :
    (h.theta α p).isLeft = (h.theta α q).isLeft := by
  by_cases hpq' : p = q
  · rw [hpq']
  · by_contra hne
    exact hpq' (h.eq_of_comm hpq (h.comm_of_theta_comm α (h.comm_of_blocks hne)))

end SL23Pair

end CFSG.OddStandard.SmallF3.Omega.K5
